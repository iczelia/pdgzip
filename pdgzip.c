/*  pdgzip: fast, embeddable gzip decoder.
    Written in 2026 by Kamila Szewczyk (k@iczelia.net).
    License: 0BSD.  Attribution welcomed but not required.  */
#include <stdalign.h>
#include <stddef.h>
#include <stdint.h>

/*  Check if we have string.h. If not, define our own string functions.  */
#if __has_include(<string.h>)
  #include <string.h>
  #define pdgzip_memcpy memcpy
  #define pdgzip_memset memset
#else
  static void * pdgzip_memcpy(void * dst, const void * src, size_t n) {
    uint8_t * d = (uint8_t *)dst;
    const uint8_t * s = (const uint8_t *)src;
    for (size_t i = 0; i < n; i++) d[i] = s[i];
    return dst;
  }
  static void * pdgzip_memset(void * dst, int c, size_t n) {
    unsigned char * p = (unsigned char *)dst;
    for (size_t i = 0; i < n; i++) p[i] = (unsigned char)c;
    return p;
  }
#endif

#include "pdgzip.h"

/*  Various tuning macros.  Most are fixed by the DEFLATE RFC,
    but different values of HUFF_BITS and INBUF_SIZE are permissible.  */
#define HUFF_BITS            9
#define INBUF_SIZE           (1 << 14)

#define HUFF_SIZE            (1 << HUFF_BITS)
#define HUFF_MASK            (HUFF_SIZE - 1)

#define MAX_LITLEN_CODES     288
#define MAX_DIST_CODES       32
#define MAX_CL_CODES         19
#define MAX_BITS             15

#define WINDOW_SIZE          32768

/*  Huffman Tables  */
typedef uint32_t huff_entry_t;

#define HUFF_SYM(e)          ((e) & 0xFFFF)
#define HUFF_LEN(e)          (((e) >> 16) & 0xF)
#define HUFF_REDIRECT(e)     (((e) >> 20) & 1)

static inline huff_entry_t make_entry(uint16_t sym, uint8_t bits) {
  return (uint32_t)sym | ((uint32_t)bits << 16);
}

static inline huff_entry_t make_redirect(uint8_t sub_bits, uint32_t offset) {
  return (offset & 0xFFFF) | ((uint32_t)(sub_bits & 0xF) << 16) | (1u << 20);
}

#define HUFF_CODE_EXTRA      (1 << (MAX_BITS - HUFF_BITS + 1))
#define HUFF_TAB_MAX         (HUFF_SIZE + HUFF_CODE_EXTRA * MAX_LITLEN_CODES)

typedef struct { huff_entry_t table[HUFF_TAB_MAX];  int used; } huff_table_t;

/*  Bit-wise I/O over the caller's read callback.  */
typedef struct {
  pdgzip_read_fn read_fn;
  void *         read_user;
  uint8_t        buf[INBUF_SIZE];
  int            buf_pos, buf_end;
  uint64_t       bits;
  int            nbits;
  int            src_eof;   /*  callback signalled EOF  */
  int            eof;       /*  ran out of bits mid-decode  */
} bitreader_t;

static void br_init(bitreader_t * br, pdgzip_read_fn fn, void * user) {
  pdgzip_memset(br, 0, sizeof(bitreader_t));
  br->read_fn = fn;
  br->read_user = user;
}

static int br_refill_buf(bitreader_t * br) {
  if (br->src_eof) return 0;
  size_t got = br->read_fn(br->read_user, br->buf, INBUF_SIZE);
  if (got < INBUF_SIZE) br->src_eof = 1;
  br->buf_end = (int)got;
  br->buf_pos = 0;
  return got > 0;
}

/*  Detect little-endian for the 64-bit bulk refill fast path.  On
    big-endian we just fall back to the byte loop.  */
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  #define PDGZIP_LE 1
#else
  #define PDGZIP_LE 0
#endif

static inline void br_need(bitreader_t * br, int n) {
  if (br->nbits >= n) return;
#if PDGZIP_LE
  /*  Bulk path: pull 8 bytes at once, advance up to 7 bytes worth of
      input.  Costs one unaligned 64-bit load per ~7 bits decoded.  */
  if (br->buf_pos + 8 <= br->buf_end) {
    uint64_t v;
    pdgzip_memcpy(&v, &br->buf[br->buf_pos], 8);
    br->bits |= v << br->nbits;
    int adv = (63 - br->nbits) >> 3;
    br->buf_pos += adv;
    br->nbits   += adv << 3;
    if (br->nbits >= n) return;
  }
#endif
  while (br->nbits < n) {
    if (br->buf_pos >= br->buf_end) {
      if (!br_refill_buf(br)) {
        br->eof = 1;  br->nbits = 64;  return;
      }
    }
    br->bits |= (uint64_t)br->buf[br->buf_pos++] << br->nbits;
    br->nbits += 8;
  }
}

static inline uint64_t br_peek(const bitreader_t * br, int n) {
  return br->bits & (((uint64_t)1 << n) - 1);
}

static inline void br_drop(bitreader_t * br, int n) {
  br->bits >>= n;  br->nbits -= n;
}

static inline uint64_t br_read(bitreader_t * br, int n) {
  br_need(br, n);
  uint64_t v = br_peek(br, n);
  br_drop(br, n);
  return v;
}

static inline void br_align(bitreader_t * br) {
  br_drop(br, br->nbits & 7);
}

static inline uint16_t br_read_u16(bitreader_t * br) {
  uint16_t lo = (uint16_t) br_read(br, 8);
  uint16_t hi = (uint16_t) br_read(br, 8);
  return (uint16_t)(lo | (hi << 8));
}

static inline uint32_t br_read_u32(bitreader_t * br) {
  uint32_t v = 0;
  for (int i = 0; i < 4; i++)
    v |= (uint32_t)br_read(br, 8) << (i * 8);
  return v;
}

/*  CRC-32 decompression code, slicing-by-8.  The 8 KiB table lives in the
    per-stream scratch so the decoder holds no global state.  It is
    initialized once per pdgzip_init.  */
typedef uint32_t crc_tab_t[8][256];

static void crc32_init_table(crc_tab_t tab) {
  for (uint32_t i = 0; i < 256; i++) {
    uint32_t c = i;
    for (int j = 0; j < 8; j++)
      c = (c >> 1) ^ (c & 1 ? 0xEDB88320u : 0);
    tab[0][i] = c;
  }
  for (uint32_t i = 0; i < 256; i++) {
    uint32_t c = tab[0][i];
    for (int k = 1; k < 8; k++) {
      c = tab[0][c & 0xFF] ^ (c >> 8);
      tab[k][i] = c;
    }
  }
}

static uint32_t crc32_update(crc_tab_t tab, uint32_t crc,
                             const uint8_t * data, size_t len) {
  for (; len >= 8; data += 8, len -= 8) {
    uint32_t lo = crc ^ ((uint32_t)data[0] | ((uint32_t)data[1] << 8) |
                  ((uint32_t)data[2] << 16) | ((uint32_t)data[3] << 24));
    uint32_t hi = (uint32_t)data[4] | ((uint32_t)data[5] << 8) |
                  ((uint32_t)data[6] << 16) | ((uint32_t)data[7] << 24);
    crc = tab[7][(lo      ) & 0xFF] ^
          tab[6][(lo >>  8) & 0xFF] ^
          tab[5][(lo >> 16) & 0xFF] ^
          tab[4][(lo >> 24) & 0xFF] ^
          tab[3][(hi      ) & 0xFF] ^
          tab[2][(hi >>  8) & 0xFF] ^
          tab[1][(hi >> 16) & 0xFF] ^
          tab[0][(hi >> 24) & 0xFF];
  }
  while (len--)
    crc = tab[0][(crc ^ *data++) & 0xFF] ^ (crc >> 8);
  return crc;
}

/*  Checked Huffman table building, decoder.  */
static int huff_build(huff_table_t * ht, const uint8_t * lengths, int count) {
  uint16_t bl_count[MAX_BITS + 1] = { 0 }, next_code[MAX_BITS + 1];
  uint16_t codes[MAX_LITLEN_CODES];

  int max_len = 0;
  for (int i = 0; i < count; i++) {
    if (lengths[i] > MAX_BITS) return -1;
    bl_count[lengths[i]]++;
    if (lengths[i] > max_len) max_len = lengths[i];
  }
  bl_count[0] = 0;

  uint32_t code = 0;
  for (int bits = 1; bits <= max_len; bits++) {
    code = (code + bl_count[bits - 1]) << 1;   /* Canonical Codes.  */
    next_code[bits] = (uint16_t)code;
  }
  if (max_len > 0 && code + bl_count[max_len] > (1u << max_len))
    return -1;  /*  Kraft condition failed.  */

  for (int i = 0; i < count; i++) {
    if (lengths[i] == 0) continue;
    codes[i] = next_code[lengths[i]]++;
  }

  ht->used = HUFF_SIZE;
  pdgzip_memset(ht->table, 0, HUFF_SIZE * sizeof(huff_entry_t));

  for (int sym = 0; sym < count; sym++) {
    int len = lengths[sym];
    if (len == 0) continue;

    if (len <= HUFF_BITS) {
      uint16_t entry_idx = 0;
      for (int b = 0; b < len; b++)
        entry_idx |= ((codes[sym] >> (len - 1 - b)) & 1) << b;

      int step = 1 << len;
      for (int idx = entry_idx; idx < HUFF_SIZE; idx += step)
        ht->table[idx] = make_entry((uint16_t)sym, (uint8_t)len);
    }
  }

  if (max_len > HUFF_BITS) {
    int sub_bits_needed[HUFF_SIZE];
    pdgzip_memset(sub_bits_needed, 0, sizeof(sub_bits_needed));

    for (int sym = 0; sym < count; sym++) {
      int len = lengths[sym];
      if (len <= HUFF_BITS) continue;

      uint16_t rev = 0;
      for (int b = 0; b < len; b++)
        rev |= ((codes[sym] >> (len - 1 - b)) & 1) << b;

      int primary = rev & HUFF_MASK, extra = len - HUFF_BITS;
      if (extra > sub_bits_needed[primary])
        sub_bits_needed[primary] = extra;
    }

    int sub_offsets[HUFF_SIZE];
    pdgzip_memset(sub_offsets, -1, sizeof(sub_offsets));

    for (int p = 0; p < HUFF_SIZE; p++) {
      if (sub_bits_needed[p] == 0) continue;
      int sub_sz = 1 << sub_bits_needed[p];
      if (ht->used + sub_sz > HUFF_TAB_MAX) return -1;
      sub_offsets[p] = ht->used;
      pdgzip_memset(&ht->table[ht->used], 0,
                    (size_t)sub_sz * sizeof(huff_entry_t));
      ht->table[p] = make_redirect((uint8_t)sub_bits_needed[p],
                     (uint32_t)ht->used);
      ht->used += sub_sz;
    }

    for (int sym = 0; sym < count; sym++) {
      int len = lengths[sym];
      if (len <= HUFF_BITS) continue;

      uint16_t rev = 0;
      for (int b = 0; b < len; b++)
        rev |= ((codes[sym] >> (len - 1 - b)) & 1) << b;

      int primary = rev & HUFF_MASK, extra_bits = len - HUFF_BITS;
      int sub_idx = (rev >> HUFF_BITS) & ((1 << sub_bits_needed[primary]) - 1);
      int off = sub_offsets[primary];

      int step = 1 << extra_bits, sub_sz = 1 << sub_bits_needed[primary];
      for (int idx = sub_idx; idx < sub_sz; idx += step)
        ht->table[off + idx] = make_entry((uint16_t)sym, (uint8_t)len);
    }
  }

  return 0;
}


static inline int huff_decode(bitreader_t * br, const huff_table_t * ht) {
  br_need(br, MAX_BITS);
  uint64_t peek = br_peek(br, MAX_BITS);
  huff_entry_t e = ht->table[peek & HUFF_MASK];
  if (HUFF_REDIRECT(e)) {
    uint32_t off = HUFF_SYM(e), sub_bits = HUFF_LEN(e);
    unsigned idx = (unsigned)((peek >> HUFF_BITS) & ((1u << sub_bits) - 1));
    e = ht->table[off + idx];
  }
  int len = HUFF_LEN(e);
  if (len == 0) return -1;
  br_drop(br, len);
  return (int) HUFF_SYM(e);
}

/*  Length/distance tables, decoder state machine.  */
static const uint16_t len_base[29] = {
    3,   4,   5,   6,   7,   8,   9,  10,  11,  13,
   15,  17,  19,  23,  27,  31,  35,  43,  51,  59,
   67,  83,  99, 115, 131, 163, 195, 227, 258
};
static const uint8_t len_extra[29] = {
  0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
  1, 1, 2, 2, 2, 2, 3, 3, 3, 3,
  4, 4, 4, 4, 5, 5, 5, 5, 0
};

static const uint16_t dist_base[30] = {
  1,     2,     3,     4,     5,     7,     9,      13,    17,     25,
  33,    49,    65,    97,    129,   193,   257,   385,   513,    769,
  1025,  1537,  2049,  3073,  4097,  6145,  8193, 12289, 16385, 24577
};
static const uint8_t dist_extra[30] = {
  0,  0,  0,  0,  1,  1,  2,  2,  3,  3,
  4,  4,  5,  5,  6,  6,  7,  7,  8,  8,
  9,  9, 10, 10, 11, 11, 12, 12, 13, 13
};

enum {
  S_HEADER, S_BLOCK_HDR, S_STORED_HDR, S_STORED_DATA, S_DYNAMIC_HDR,
  S_DECODE, S_MATCH, S_TRAILER,
  S_DONE, S_ERROR
};

/*  Full decoder state.  The public `struct pdgzip` is just this struct;
    the caller's scratch buffer is cast to a pointer to it.  */
struct pdgzip {
  bitreader_t br;
  uint8_t window[WINDOW_SIZE * 2];
  uint32_t wpos, crc, total;
  int state, err, bfinal, concat;
  const huff_table_t * ht_lit, * ht_dist;
  huff_table_t ht_litbuf, ht_distbuf;
  uint16_t store_remaining, match_len, match_dist, match_pos;
  crc_tab_t crc_tab;
};

/*  Rebuild the RFC1951 fixed-Huffman tables into the per-stream buffers.
    Done lazily on each BTYPE=01 block: fixed blocks are rare in modern
    gzip streams, and this keeps the tables out of .bss entirely.  */
static void build_fixed_tables(pdgzip_t * gz) {
  uint8_t ll[288], dd[32];  int i;
  for (i =   0; i <= 143; i++) ll[i] = 8;
  for (i = 144; i <= 255; i++) ll[i] = 9;
  for (i = 256; i <= 279; i++) ll[i] = 7;
  for (i = 280; i <= 287; i++) ll[i] = 8;
  huff_build(&gz->ht_litbuf, ll, 288);
  for (i = 0; i < 32; i++) dd[i] = 5;
  huff_build(&gz->ht_distbuf, dd, 32);
}

/*  Hardened Gzip header handling.  */
#define GZ_MAGIC1            0x1F
#define GZ_MAGIC2            0x8B
#define GZ_METHOD_DEFLATE    8
#define FHCRC                (1 << 1)
#define FEXTRA               (1 << 2)
#define FNAME                (1 << 3)
#define FCOMMENT             (1 << 4)

/*  Read one header byte and fold it into the running CRC-32 used for
    FHCRC validation.  The header CRC is the low 16 bits of CRC-32
    over every header byte preceding the FHCRC field itself.  */
static inline uint8_t hdr_byte(pdgzip_t * gz, uint32_t * hcrc) {
  uint8_t b = (uint8_t)br_read(&gz->br, 8);
  *hcrc = gz->crc_tab[0][(*hcrc ^ b) & 0xFFu] ^ (*hcrc >> 8);
  return b;
}

static int parse_gz_header(pdgzip_t * gz) {
  bitreader_t * br = &gz->br;
  uint32_t hcrc = 0xFFFFFFFFu;
  uint8_t id1 = hdr_byte(gz, &hcrc);
  uint8_t id2 = hdr_byte(gz, &hcrc);
  if (id1 != GZ_MAGIC1 || id2 != GZ_MAGIC2)
    return -1;
  uint8_t method = hdr_byte(gz, &hcrc);
  if (method != GZ_METHOD_DEFLATE)
    return -1;
  uint8_t flags = hdr_byte(gz, &hcrc);
  /*  RFC 1952: bits 5..7 of FLG are reserved and MUST be zero.  */
  if (flags & 0xE0) return -1;
  for (int i = 0; i < 6; i++)
    (void)hdr_byte(gz, &hcrc); /*  timestamp, xflags, OS  */
  if (flags & FEXTRA) {
    uint8_t xlo = hdr_byte(gz, &hcrc);
    uint8_t xhi = hdr_byte(gz, &hcrc);
    uint16_t xlen = (uint16_t)(xlo | (xhi << 8));
    for (uint16_t i = 0; i < xlen; i++)
      (void)hdr_byte(gz, &hcrc);
  }
  if (flags & FNAME) {
    while (hdr_byte(gz, &hcrc) != 0 && !br->eof) { }
  }
  if (flags & FCOMMENT) {
    while (hdr_byte(gz, &hcrc) != 0 && !br->eof) { }
  }
  if (flags & FHCRC) {
    /*  The FHCRC field itself is *not* fed into hcrc.  */
    uint16_t got  = br_read_u16(br);
    uint16_t want = (uint16_t)((hcrc ^ 0xFFFFFFFFu) & 0xFFFFu);
    if (got != want) return -1;
  }
  return br->eof ? -1 : 0;
}

/*  Gzip format table parser.  */
static const int cl_order[MAX_CL_CODES] = {
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
};

/*  Build the dynamic Huffman tables.  The code-length (CL) table is a
    transient scratch buffer -- we reuse `ht_distbuf` for it since the
    final distance table is built last, after we're done with the CL
    table.  This keeps the decoder's memory footprint to two huff_tables
    instead of three.  */
static int build_dynamic_tables(pdgzip_t * gz) {
  bitreader_t * br = &gz->br;
  int hlit  = (int)br_read(br, 5) + 257;
  int hdist = (int)br_read(br, 5) + 1;
  int hclen = (int)br_read(br, 4) + 4;
  if (hlit > 286 || hdist > 30) return -1;
  uint8_t cl_lengths[MAX_CL_CODES] = {0};
  for (int i = 0; i < hclen; i++)
    cl_lengths[cl_order[i]] = (uint8_t)br_read(br, 3);
  huff_table_t * ht_cl = &gz->ht_distbuf;  /*  scratch - reused below  */
  if (huff_build(ht_cl, cl_lengths, MAX_CL_CODES) < 0) return -1;
  int total = hlit + hdist, idx = 0;
  uint8_t all_lengths[MAX_LITLEN_CODES + MAX_DIST_CODES] = { 0 };
  while (idx < total) {
    int sym = huff_decode(br, ht_cl);
    if (sym < 0) return -1;
    if (sym < 16) {
      all_lengths[idx++] = (uint8_t)sym;
    } else if (sym == 16) {
      if (idx == 0) return -1;
      int rep = (int)br_read(br, 2) + 3;
      uint8_t prev = all_lengths[idx - 1];
      for (int i = 0; i < rep && idx < total; i++)
        all_lengths[idx++] = prev;
    } else if (sym == 17) {
      int rep = (int)br_read(br, 3) + 3;
      for (int i = 0; i < rep && idx < total; i++)
        all_lengths[idx++] = 0;
    } else if (sym == 18) {
      int rep = (int)br_read(br, 7) + 11;
      for (int i = 0; i < rep && idx < total; i++)
        all_lengths[idx++] = 0;
    } else {
      return -1;
    }
  }
  if (huff_build(&gz->ht_litbuf, all_lengths, hlit) < 0) return -1;
  if (huff_build(&gz->ht_distbuf, all_lengths + hlit, hdist) < 0) return -1;
  gz->ht_lit  = &gz->ht_litbuf;
  gz->ht_dist = &gz->ht_distbuf;
  return 0;
}

/*  Pull decompressed bytes per the state machine.  Returns bytes
    produced, 0 on clean end-of-stream, or negative PDGZIP_E_* on error.  */
static int64_t gz_decompress(pdgzip_t * gz, void * dst, size_t n) {
  uint8_t * out = dst;
  size_t written = 0;
  while (written < n) {
    switch (gz->state) {
    case S_HEADER:
      if (parse_gz_header(gz) < 0) {
        gz->state = S_ERROR;
        gz->err = gz->br.eof ? PDGZIP_E_IO : PDGZIP_E_FORMAT;
        return gz->err;
      }
      gz->state = S_BLOCK_HDR;
      break;

    case S_BLOCK_HDR: {
      gz->bfinal = (int)br_read(&gz->br, 1);
      int btype  = (int)br_read(&gz->br, 2);
      switch (btype) {
      case 0:
        gz->state = S_STORED_HDR;
        break;
      case 1:
        build_fixed_tables(gz);
        gz->ht_lit  = &gz->ht_litbuf;
        gz->ht_dist = &gz->ht_distbuf;
        gz->state   = S_DECODE;
        break;
      case 2:
        gz->state = S_DYNAMIC_HDR;
        break;
      default:
        gz->state = S_ERROR;  gz->err = PDGZIP_E_FORMAT;  return gz->err;
      }
      break;
    }

    case S_STORED_HDR: {
      br_align(&gz->br);
      uint16_t len  = br_read_u16(&gz->br);
      uint16_t nlen = br_read_u16(&gz->br);
      if (len != (uint16_t)~nlen) {
        gz->state = S_ERROR;  gz->err = PDGZIP_E_FORMAT;  return gz->err;
      }
      gz->store_remaining = len;
      gz->state = S_STORED_DATA;
      break;
    }

    case S_STORED_DATA: {
      while (gz->store_remaining > 0 && written < n) {
        if (gz->wpos >= WINDOW_SIZE * 2) {
          gz->crc = crc32_update(gz->crc_tab, gz->crc,
                                 gz->window + WINDOW_SIZE, WINDOW_SIZE);
          pdgzip_memcpy(gz->window, gz->window + WINDOW_SIZE, WINDOW_SIZE);
          gz->wpos = WINDOW_SIZE;
        }
        uint8_t b = (uint8_t)br_read(&gz->br, 8);
        out[written++] = b;
        gz->window[gz->wpos++] = b;
        gz->total++;
        gz->store_remaining--;
      }
      if (gz->store_remaining == 0)
        gz->state = gz->bfinal ? S_TRAILER : S_BLOCK_HDR;
      break;
    }

    case S_DYNAMIC_HDR:
      if (build_dynamic_tables(gz) < 0) {
        gz->state = S_ERROR;
        gz->err = gz->br.eof ? PDGZIP_E_IO : PDGZIP_E_FORMAT;
        return gz->err;
      }
      gz->state = S_DECODE;
      break;

    case S_DECODE: {
      uint32_t wpos  = gz->wpos, total = gz->total;
      uint8_t * window = gz->window;
      bitreader_t * br = &gz->br;
      for (;;) {
        if (wpos >= WINDOW_SIZE * 2) {
          gz->crc = crc32_update(gz->crc_tab, gz->crc,
                                 window + WINDOW_SIZE, WINDOW_SIZE);
          pdgzip_memcpy(window, window + WINDOW_SIZE, WINDOW_SIZE);
          wpos = WINDOW_SIZE;
        }
        if (written >= n) break;
        int sym = huff_decode(br, gz->ht_lit);
        if ((unsigned)sym < 256u) {
          out[written++] = window[wpos++] = (uint8_t)sym;
          total++;
          continue;
        }
        if (sym == 256) {
          gz->state = gz->bfinal ? S_TRAILER : S_BLOCK_HDR;
          break;
        }
        if ((unsigned)sym > 285u) {
          gz->wpos = wpos; gz->total = total;
          gz->state = S_ERROR;  gz->err = PDGZIP_E_FORMAT;  return gz->err;
        }
        unsigned li = (unsigned)sym - 257u;   /*  bounded: 0..28  */
        unsigned mlen = (unsigned)len_base[li] +
                        (unsigned)br_read(br, len_extra[li]);
        int di = huff_decode(br, gz->ht_dist);
        if ((unsigned)di >= 30u) {
          gz->wpos = wpos; gz->total = total;
          gz->state = S_ERROR;  gz->err = PDGZIP_E_FORMAT;  return gz->err;
        }
        unsigned mdist = (unsigned)dist_base[di] +
                         (unsigned)br_read(br, dist_extra[di]);

        /*  Fast path: the entire match (<= 258 bytes) fits in the
            remaining output and current window semispace, with no
            self-overlap.  This is the common case and skips the
            S_MATCH dispatch and per-iteration bounds checks.  */
        size_t buf_space = n - written;
        size_t win_space = WINDOW_SIZE * 2 - wpos;
        if (mlen <= buf_space && mlen <= win_space && mdist >= mlen) {
          pdgzip_memcpy(window + wpos, window + wpos - mdist, mlen);
          pdgzip_memcpy(out + written, window + wpos, mlen);
          wpos += mlen; written += mlen; total += mlen;
          continue;
        }
        /*  Slow path: split across window edge / output edge / overlap.  */
        unsigned mpos = 0;
        while (mpos < mlen) {
          if (wpos >= WINDOW_SIZE * 2) {
            gz->crc = crc32_update(gz->crc_tab, gz->crc,
                                   window + WINDOW_SIZE, WINDOW_SIZE);
            pdgzip_memcpy(window, window + WINDOW_SIZE, WINDOW_SIZE);
            wpos = WINDOW_SIZE;
          }
          size_t chunk = mlen - mpos;
          if (chunk > n - written) chunk = n - written;
          if (chunk > WINDOW_SIZE * 2 - wpos) chunk = WINDOW_SIZE * 2 - wpos;
          if (chunk == 0) {
            /*  Caller's output buffer is full mid-match; resume via
                S_MATCH on the next pdgzip_read call.  */
            gz->wpos = wpos; gz->total = total;
            gz->match_len  = (uint16_t)mlen;
            gz->match_dist = (uint16_t)mdist;
            gz->match_pos  = (uint16_t)mpos;
            gz->state = S_MATCH;
            return (int64_t)written;
          }
          if (mdist >= chunk) {
            pdgzip_memcpy(window + wpos, window + wpos - mdist, chunk);
            pdgzip_memcpy(out + written, window + wpos, chunk);
          } else {
            for (size_t i = 0; i < chunk; i++) {
              uint8_t b = window[wpos + i - mdist];
              window[wpos + i] = b;
              out[written + i] = b;
            }
          }
          wpos += (uint32_t)chunk;
          written += chunk;
          total += (uint32_t)chunk;
          mpos += (unsigned)chunk;
        }
      }
      gz->wpos  = wpos;
      gz->total = total;
      break;
    }

    case S_MATCH: {
      uint32_t wpos  = gz->wpos, total = gz->total;
      uint8_t * window = gz->window;
      uint16_t dist = gz->match_dist;
      while (gz->match_pos < gz->match_len && written < n) {
        if (wpos >= WINDOW_SIZE * 2) {
          gz->crc = crc32_update(gz->crc_tab, gz->crc,
                                 window + WINDOW_SIZE, WINDOW_SIZE);
          pdgzip_memcpy(window, window + WINDOW_SIZE, WINDOW_SIZE);
          wpos = WINDOW_SIZE;
        }
        size_t remaining = gz->match_len - gz->match_pos, chunk = remaining;
        size_t buf_space = n - written,  win_space = WINDOW_SIZE * 2 - wpos;
        if (chunk > buf_space) chunk = buf_space;
        if (chunk > win_space) chunk = win_space;
        if (dist >= chunk) {
          pdgzip_memcpy(window + wpos, window + wpos - dist, chunk);
          pdgzip_memcpy(out + written, window + wpos, chunk);
          wpos += (uint32_t)chunk;
          written += chunk;
          total += (uint32_t)chunk;
          gz->match_pos += (uint16_t)chunk;
        } else {
          uint8_t b = window[wpos - dist];
          out[written++] = window[wpos++] = b;
          total++;
          gz->match_pos++;
        }
      }
      gz->wpos  = wpos;
      gz->total = total;
      if (gz->match_pos == gz->match_len)
        gz->state = S_DECODE;
      break;
    }

    case S_TRAILER: {
      uint32_t pending = gz->wpos - WINDOW_SIZE;
      if (pending > 0)
        gz->crc = crc32_update(gz->crc_tab, gz->crc,
                               gz->window + WINDOW_SIZE, pending);
      br_align(&gz->br);
      uint32_t exp_crc   = br_read_u32(&gz->br);
      uint32_t exp_isize = br_read_u32(&gz->br);
      if (gz->br.eof) {
        gz->state = S_ERROR;  gz->err = PDGZIP_E_IO;  return gz->err;
      }
      if ((gz->crc ^ 0xFFFFFFFFu) != exp_crc) {
        gz->state = S_ERROR;  gz->err = PDGZIP_E_CHECKSUM;  return gz->err;
      }
      /*  ISIZE is the low 32 bits of the decompressed size.  CRC32
          already catches corruption for any stream, so for streams
          < 4 GiB this is strictly redundant.  At or above 4 GiB the
          value is modular and carries no additional bits of truth
          beyond what the writer chose to encode -- but validating
          (total & 0xFFFFFFFF) against it is still sound on any
          conforming stream and matches zlib's behaviour, which the
          differential fuzzer depends on.  */
      if ((uint32_t)(gz->total & 0xFFFFFFFFu) != exp_isize) {
        gz->state = S_ERROR;  gz->err = PDGZIP_E_CHECKSUM;  return gz->err;
      }
      if (gz->concat) {
        /*  Probe for another member.  br_need() sets br->eof when the
            source callback has no more bytes.  If more bytes are
            available, reset per-member state and restart at S_HEADER;
            the buffered bits remain intact so the new header is read
            from exactly where the trailer ended.  */
        br_need(&gz->br, 8);
        if (!gz->br.eof) {
          gz->crc   = 0xFFFFFFFFu;
          gz->total = 0;
          gz->wpos  = WINDOW_SIZE;
          gz->bfinal = 0;
          /*  Zero the lower semispace so stale data from the previous
              member can never leak into early back-references.  */
          pdgzip_memset(gz->window, 0, WINDOW_SIZE);
          gz->state = S_HEADER;
          break;
        }
        /*  fall through: no more input, clean EOS  */
      }
      gz->state = S_DONE;
      break;
    }

    case S_DONE:  return (int64_t) written;
    case S_ERROR: return gz->err;
    default:
      gz->state = S_ERROR;  gz->err = PDGZIP_E_FORMAT;  return gz->err;
    }
  }

  return (int64_t)written;
}

/*  Public API.  */
size_t pdgzip_state_size(void)  { return sizeof(struct pdgzip); }
size_t pdgzip_state_align(void) { return alignof(struct pdgzip); }

pdgzip_t * pdgzip_init(void * scratch, const pdgzip_cfg_t * cfg) {
  if (!scratch || !cfg || !cfg->read) return NULL;
  pdgzip_t * gz = scratch;
  pdgzip_memset(gz, 0, sizeof(*gz));
  br_init(&gz->br, cfg->read, cfg->user);
  gz->wpos   = WINDOW_SIZE;   /*  Semi-space streaming decoding.  */
  gz->crc    = 0xFFFFFFFFu;
  gz->state  = S_HEADER;
  gz->err    = 0;
  gz->concat = cfg->concat;
  crc32_init_table(gz->crc_tab);
  return gz;
}

int64_t pdgzip_read(pdgzip_t * gz, void * buf, size_t n) {
  if (!gz) return PDGZIP_E_FORMAT;
  if (gz->state == S_ERROR) return gz->err;
  if (n == 0) return 0;
  return gz_decompress(gz, buf, n);
}

/*  The peak memory usage of this (fast) Gzip decoder is roughly
    pdgzip_state_size() bytes per stream (~385 KiB with default tuning).
    This can be reduced by increasing HUFF_BITS from 9 at a small
    decode-speed cost: 9 -> 385 KiB, 10 -> ~225 KiB, 11 -> ~145 KiB.  */
