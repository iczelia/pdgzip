/* pdgzip, kamila szewczyk (iczelia), 27feb2026 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
static uint32_t crc_table[256];
static void crc32_init(void) {
  for (uint32_t i = 0; i < 256; i++) {
    uint32_t c = i;
    for (int k = 0; k < 8; k++)
      c = (c & 1u) ? (0xEDB88320u ^ (c >> 1)) : (c >> 1);
    crc_table[i] = c;
  }
}
static uint32_t crc32_update(uint32_t crc, const uint8_t * buf, size_t len) {
  uint32_t c = crc;
  for (size_t i = 0; i < len; i++)
    c = crc_table[(c ^ buf[i]) & 0xFFu] ^ (c >> 8);
  return c;
}
static void put_u32_le(FILE * out, uint32_t v) {
  fputc((int)(v & 0xFFu), out);
  fputc((int)((v >> 8) & 0xFFu), out);
  fputc((int)((v >> 16) & 0xFFu), out);
  fputc((int)((v >> 24) & 0xFFu), out);
}
static void write_gzip_header(FILE * out, const char * in_path, int level) {
  uint32_t mtime = 0;
  uint8_t xfl = level <= 1 ? 4 : level >= 9 ? 2 : 0, flg = 0;
  const char * name = in_path;
  if (in_path) {
    struct stat st;
    if (stat(in_path, &st) == 0) {
      if ((uint64_t)st.st_mtime > 0xFFFFFFFFu) mtime = 0xFFFFFFFFu;
      else mtime = (uint32_t)st.st_mtime;
    }
  }
  if (in_path && in_path[0])
    for (const char *p = in_path; *p; p++)
      if (*p == '/' || *p == '\\') name = p + 1;
  if (name && name[0]) flg |= 0x08;
  fputc(0x1f, out);  fputc(0x8b, out);
  fputc(8, out);
  fputc(flg, out);
  put_u32_le(out, mtime);
  fputc(xfl, out);
  fputc(255, out);
  if (flg & 0x08) {
    fwrite(name, 1, strlen(name), out);  fputc(0, out);
  }
}
typedef struct {
  FILE * out;  uint64_t bitbuf;  int bitcnt;
} BitW;
static void bw_write_bits(BitW * bw, uint32_t val, int nbits) {
  bw->bitbuf |= ((uint64_t)val) << bw->bitcnt;
  bw->bitcnt += nbits;
  while (bw->bitcnt >= 8) {
    fputc((int)(bw->bitbuf & 0xFFu), bw->out);
    bw->bitbuf >>= 8;
    bw->bitcnt -= 8;
  }
}
static void bw_flush_final(BitW * bw) {
  if (bw->bitcnt) {
    fputc((int)(bw->bitbuf & 0xFFu), bw->out);
    bw->bitbuf = bw->bitcnt = 0;
  }
}
typedef struct {
  FILE * in;  uint64_t bitbuf;  int bitcnt, eof;
} BitR;
static int br_fill(BitR * br, int need_bits) {
  while (br->bitcnt < need_bits && !br->eof) {
    int c = fgetc(br->in);
    if (c == EOF) { br->eof = 1; break; }
    br->bitbuf |= ((uint64_t)(uint8_t)c) << br->bitcnt;
    br->bitcnt += 8;
  }
  return br->bitcnt >= need_bits;
}
static void br_drop_bits(BitR * br, int nbits) {
  br->bitbuf >>= nbits;
  br->bitcnt -= nbits;
}
static uint32_t br_read_bits(BitR * br, int nbits) {
  if (!br_fill(br, nbits)) return 0;
  uint32_t v = (uint32_t)(br->bitbuf & ((nbits == 32) ? 0xFFFFFFFFu : ((1u << nbits) - 1u)));
  br_drop_bits(br, nbits);
  return v;
}
static int br_read_byte_aligned(BitR * br, int * ok) {
  if (br->bitcnt & 7) br_drop_bits(br, br->bitcnt & 7);
  if (!br_fill(br, 8)) { *ok = 0; return 0; }
  int c = (int)(br->bitbuf & 0xFFu);
  br_drop_bits(br, 8);
  *ok = 1;
  return c;
}
#define WSIZE 32768
#define MIN_MATCH 3
#define MAX_MATCH 258
static const uint16_t len_base[29] = {
  3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,
  35,43,51,59,67,83,99,115,131,163,195,227,258
};
static const uint8_t len_ebits[29] = {
  0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,
  4,4,4,4,5,5,5,5,0
};
static const uint16_t dist_base[30] = {
  1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,
  257,385,513,769,1025,1537,2049,3073,4097,6145,
  8193,12289,16385,24577
};
static const uint8_t dist_ebits[30] = {
  0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,
  8,8,9,9,10,10,11,11,12,12,13,13
};
static void encode_length(int length, int * sym, uint16_t * extra, int * ebits) {
  if (length == 258) { *sym = 285; *extra = 0; *ebits = 0; return; }
  int code = 0;
  while (code < 28) {
    int next_base = len_base[code + 1];
    if (length < next_base) break;
    code++;
  }
  *sym = 257 + code;
  *ebits = len_ebits[code];
  *extra = (uint16_t)(length - len_base[code]);
}
static void encode_dist(int dist, int * sym, uint16_t * extra, int * ebits) {
  int code = 0;
  while (code < 29) {
    int next_base = dist_base[code + 1];
    if (dist < next_base) break;
    code++;
  }
  *sym = code;
  *ebits = dist_ebits[code];
  *extra = (uint16_t)(dist - dist_base[code]);
}
static void make_canonical_codes_rev(const uint8_t * lens, int n, int max_bits, uint16_t * codes_rev) {
  uint16_t bl_count[16] = {0}, next_code[16] = {0};
  for (int i = 0; i < n; i++) if (lens[i]) bl_count[lens[i]]++;
  uint16_t code = 0;
  bl_count[0] = 0;
  for (int bits = 1; bits <= max_bits; bits++) {
    code = (uint16_t)((code + bl_count[bits - 1]) << 1);
    next_code[bits] = code;
  }
  for (int i = 0; i < n; i++) {
    uint8_t len = lens[i];
    if (len) {
      uint16_t codev = next_code[len]++, rev = 0;
      for (int k = 0; k < len; k++) {
        rev = (uint16_t)((rev << 1) | (codev & 1u));
        codev >>= 1;
      }
      codes_rev[i] = rev;
    } else codes_rev[i] = 0;
  }
}
typedef struct { uint16_t sym;  uint8_t len; } DecEnt;
enum { DECODE_BITS = 15, CL_DECODE_BITS = 7 };
static int build_decode_table(const uint8_t * lens, int n, int max_bits, int table_bits, DecEnt * tab) {
  const int TSZ = 1 << table_bits;
  for (int i = 0; i < TSZ; i++) { tab[i].sym = 0; tab[i].len = 0; }
  uint16_t codes_rev[300];
  make_canonical_codes_rev(lens, n, max_bits, codes_rev);
  for (int s = 0; s < n; s++) {
    int l = lens[s];
    if (!l) continue;
    uint16_t c = codes_rev[s]; /* l bits in LSB order */
    if (l > table_bits) { return 0; } /* keep simple */
    for (uint32_t idx = c; idx < (uint32_t)TSZ; idx += 1u << l) {
      tab[idx].sym = (uint16_t)s;  tab[idx].len = (uint8_t)l;
    }
  }
  return 1;
}
static int huff_decode(BitR *br, const DecEnt * tab, int table_bits, int * out_sym) {
  if (!br_fill(br, table_bits)) return 0;
  uint32_t idx = (uint32_t)(br->bitbuf & ((1u << table_bits) - 1u));
  uint8_t l = tab[idx].len;
  if (!l) return 0;
  *out_sym = tab[idx].sym;
  br_drop_bits(br, l);
  return 1;
}
typedef struct { int sym;  uint32_t freq; } SymFreq;
static int cmp_symfreq_asc(const void * a, const void * b) {
  const SymFreq * x = (const SymFreq *) a;
  const SymFreq * y = (const SymFreq *) b;
  if (x->freq < y->freq) return -1;
  if (x->freq > y->freq) return 1;
  return x->sym - y->sym;
}
typedef struct { uint32_t w; int node; } HeapItem;
typedef struct { HeapItem * a; int n;  const uint32_t * w; } MinHeap;
static void heap_swap(HeapItem * x, HeapItem * y) { HeapItem t = *x; *x = *y; *y = t; }
static void heap_push(MinHeap * h, int node) {
  int i = h->n++;
  h->a[i].node = node;
  h->a[i].w = h->w[node];
  while (i > 0) {
    int p = (i - 1) >> 1;
    if (h->a[p].w < h->a[i].w || (h->a[p].w == h->a[i].w && h->a[p].node < h->a[i].node))
      break;
    heap_swap(&h->a[p], &h->a[i]);
    i = p;
  }
}
static int heap_pop(MinHeap * h) {
  HeapItem root = h->a[0];
  h->n--;
  if (h->n > 0) {
    h->a[0] = h->a[h->n];
    int i = 0;
    for (;;) {
      int l = i*2 + 1, r = l + 1, s = i;
      if (l < h->n) {
        if (h->a[l].w < h->a[s].w || (h->a[l].w == h->a[s].w && h->a[l].node < h->a[s].node))
          s = l;
      }
      if (r < h->n) {
        if (h->a[r].w < h->a[s].w || (h->a[r].w == h->a[s].w && h->a[r].node < h->a[s].node))
          s = r;
      }
      if (s == i) break;
      heap_swap(&h->a[s], &h->a[i]);
      i = s;
    }
  }
  return root.node;
}
enum { MAX_CODELEN_SYMS = 286, MAX_CODELEN_NODES = MAX_CODELEN_SYMS * 2 + 2,
       MAX_CODELEN_HEAP = MAX_CODELEN_SYMS * 2 + 8 };
static void build_code_lengths(const uint32_t * freq, int n, int max_bits, uint8_t * lens) {
  memset(lens, 0, (size_t) n);
  if (n <= 0 || n > MAX_CODELEN_SYMS) return;
  SymFreq sf[MAX_CODELEN_SYMS];
  int ns = 0;
  for (int i = 0; i < n; i++)
    if (freq[i]) sf[ns++] = (SymFreq) { i, freq[i] };
  if (ns == 0) { lens[0] = lens[1] = 1; return; }
  if (ns == 1) { int s = sf[0].sym; lens[s] = lens[s == 0 ? 1 : 0] = 1; return; }
  int max_nodes = 2 * n + 2;
  uint32_t w[MAX_CODELEN_NODES] = {0};
  int parent[MAX_CODELEN_NODES];
  for (int i = 0; i < max_nodes; i++) parent[i] = -1;
  for (int i = 0; i < n; i++) w[i] = freq[i];
  HeapItem ha[MAX_CODELEN_HEAP];
  MinHeap hp = { ha, 0, w };
  for (int i = 0; i < ns; i++) heap_push(&hp, sf[i].sym);
  int next = n;
  while (hp.n > 1) {
    int a = heap_pop(&hp);
    int b = heap_pop(&hp);
    int nn = next++;
    w[nn] = w[a] + w[b];
    parent[a] = nn;
    parent[b] = nn;
    heap_push(&hp, nn);
  }
  uint8_t tmp_len[MAX_CODELEN_SYMS] = {0};
  for (int i = 0; i < ns; i++) {
    int s = sf[i].sym, d = 0, x = s;
    while (parent[x] != -1) { d++; x = parent[x]; }
    if (d == 0) d = 1;
    if (d > 255) d = 255;
    tmp_len[s] = (uint8_t)d;
  }
  uint32_t bl_count[16] = {0};
  for (int i = 0; i < n; i++) {
    if (tmp_len[i]) {
      uint8_t L = tmp_len[i] > (uint8_t)max_bits ? (uint8_t)max_bits : tmp_len[i];
      tmp_len[i] = L;  bl_count[L]++;
    }
  }
  uint32_t K = 0;
  for (int L = 1; L <= max_bits; L++)
    K += bl_count[L] << (max_bits - L);
  const uint32_t target = 1u << max_bits;
  while (K > target) {
    int changed = 0;
    for (int L = max_bits - 1; L >= 1; L--) {
      if (bl_count[L] == 0) continue;
      uint32_t delta = 1u << (max_bits - L - 1);
      bl_count[L]--;
      bl_count[L + 1]++;
      K -= delta;
      changed = 1; if (K <= target) break;
    }
    if (!changed) break;
  }
  while (K < target) {
    int changed = 0;
    for (int L = max_bits; L >= 2; L--) {
      if (bl_count[L] == 0) continue;
      uint32_t delta = 1u << (max_bits - L);
      if (K + delta > target) continue;
      bl_count[L]--;
      bl_count[L - 1]++;
      K += delta;
      changed = 1; if (K == target) break;
    }
    if (!changed) break;
  }
  qsort(sf, (size_t)ns, sizeof(SymFreq), cmp_symfreq_asc);
  memset(lens, 0, (size_t)n);
  int pos = 0;
  for (int L = max_bits; L >= 1; L--)
    for (uint32_t cnt = bl_count[L]; cnt-- && pos < ns; )
      lens[sf[pos++].sym] = (uint8_t)L;
}
static const uint8_t cl_order[19] = {16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15};
typedef struct { uint8_t sym, ebits_n; uint16_t ebits_v; } CLItem;
static CLItem * rle_code_lengths(const uint8_t * seq, int nseq, int * out_nitems, uint32_t freq_cl[19]) {
  memset(freq_cl, 0, 19 * sizeof(uint32_t));
  CLItem * items = (CLItem*)malloc((size_t)(nseq * 2 + 32) * sizeof(CLItem));
  int out = 0, run;
  for (int i = 0; i < nseq; i += run) {
    uint8_t v = seq[i];
    run = 1;
    while (i + run < nseq && seq[i + run] == v && run < 138) run++;
    if (v == 0) {
      int left = run;
      while (left > 0) {
        if (left >= 11) {
          int use = left > 138 ? 138 : left;
          items[out++] = (CLItem){18, 7, (uint16_t)(use - 11)};
          freq_cl[18]++; left -= use;
        } else if (left >= 3) {
          int use = left > 10 ? 10 : left;
          items[out++] = (CLItem){17, 3, (uint16_t)(use - 3)};
          freq_cl[17]++; left -= use;
        } else {
          items[out++] = (CLItem){0, 0, 0};
          freq_cl[0]++; left--;
        }
      }
    } else {
      items[out++] = (CLItem){v, 0, 0};
      freq_cl[v]++;
      int left = run - 1;
      while (left > 0) {
        if (left >= 3) {
          int use = left > 6 ? 6 : left;
          items[out++] = (CLItem){16, 2, (uint16_t)(use - 3)};
          freq_cl[16]++; left -= use;
        } else {
          items[out++] = (CLItem){v, 0, 0};
          freq_cl[v]++; left--;
        }
      }
    }
  }
  *out_nitems = out;
  return items;
}
static void make_fixed_lens(uint8_t litlen_lens[288], uint8_t dist_lens[32]) {
  for (int i = 0; i <= 143; i++) litlen_lens[i] = 8;
  for (int i = 144; i <= 255; i++) litlen_lens[i] = 9;
  for (int i = 256; i <= 279; i++) litlen_lens[i] = 7;
  for (int i = 280; i <= 287; i++) litlen_lens[i] = 8;
  for (int i = 0; i < 32; i++) dist_lens[i] = 5;
}
#define HASH_BITS 15
#define HASH_SIZE (1u << HASH_BITS)
#define HASH_MASK (HASH_SIZE - 1u)
static inline uint32_t hash3(const uint8_t * p) {
  uint32_t v = ((uint32_t)p[0] << 16) ^ ((uint32_t)p[1] << 8) ^ (uint32_t)p[2];
  return ((v * 2654435761u) >> (32 - HASH_BITS)) & HASH_MASK;
}
typedef struct { uint8_t is_match;  uint16_t lit, len, dist; } Token;
typedef struct { Token * t;  size_t n, cap; } TokVec;
static int tok_push(TokVec * v, Token x) {
  if (v->n == v->cap) {
    size_t nc = v->cap ? v->cap * 2 : 4096;
    Token * nt = (Token *) realloc(v->t, nc * sizeof(Token));
    if (!nt) return 0;
    v->t = nt; v->cap = nc;
  }
  v->t[v->n++] = x;
  return 1;
}
typedef struct { int good_length, max_lazy, nice_length, max_chain, level; } DefParams;
static void insert_string(const uint8_t * in, size_t n, size_t pos, int32_t * head, int32_t * prev) {
  if (pos + 2 >= n) return;
  uint32_t h = hash3(in + pos);
  prev[pos] = head[h];
  head[h] = (int32_t)pos;
}
static void find_longest_match(const uint8_t * in, size_t n, size_t pos, int32_t head_val,
                              int32_t * prev, int max_chain, int nice_length, int * best_len,
                              int * best_dist) {
  *best_len = *best_dist = 0;
  if (pos + 2 >= n) return;
  int32_t cur = head_val;
  int chain = 0;
  while (cur >= 0 && chain++ < max_chain) {
    int dist = (int)(pos - (size_t)cur);
    if (dist > WSIZE) break;
    if (in[cur] != in[pos] || in[(size_t)cur + 1] != in[pos + 1] || in[(size_t)cur + 2] != in[pos + 2]) {
      cur = prev[cur];
      continue;
    }
    int max = (int)(n - pos);
    if (max > MAX_MATCH) max = MAX_MATCH;
    int l = 3;
    while (l < max && in[(size_t)cur + (size_t)l] == in[pos + (size_t)l]) l++;
    if (l > *best_len) {
      *best_len = l;
      *best_dist = dist;
      if (l >= nice_length) return;
    }
    cur = prev[cur];
  }
}
#define MAX_SYMS_PER_BLOCK 16383 /* block flush unit (symbols) */
typedef struct { TokVec toks;  uint32_t freq_ll[286], freq_d[30];  size_t raw_start, raw_end; } Block;
static void block_free(Block *b) {
  free(b->toks.t);  b->toks.t = NULL;
  b->toks.n = b->toks.cap = 0;
}
static int tokenize_next_block(const uint8_t * in, size_t n, size_t * io_pos, int32_t * head,
                               int32_t * prev, DefParams p, Block * blk) {
  memset(blk, 0, sizeof(*blk));
  blk->raw_start = *io_pos;
  size_t pos = *io_pos;
  int sym_count = 0;
  while (pos < n && sym_count < MAX_SYMS_PER_BLOCK) {
    int best_len = 0, best_dist = 0, lazy_len = 0, lazy_dist = 0;
    int32_t head_val = -1;
    if (pos + 2 < n)
      head_val = head[hash3(in + pos)];
    find_longest_match(in, n, pos, head_val, prev, p.max_chain, p.nice_length, &best_len, &best_dist);
    insert_string(in, n, pos, head, prev);
    if (best_len >= MIN_MATCH) {
      if (p.max_lazy > 0 && best_len < p.max_lazy && pos + 1 < n) {
        int32_t head_val2 = -1;
        if (pos + 1 + 2 < n)
          head_val2 = head[hash3(in + pos + 1)];
        find_longest_match(in, n, pos + 1, head_val2, prev, p.max_chain, p.nice_length, &lazy_len, &lazy_dist);
      }
      if (lazy_len > best_len) {
        if (!tok_push(&blk->toks, (Token){0, in[pos], 0, 0})) return 0;
        blk->freq_ll[in[pos]]++;
        pos++;
        sym_count++;
        continue;
      }
      if (!tok_push(&blk->toks, (Token){1, 0, (uint16_t)best_len, (uint16_t)best_dist})) return 0;
      int lsym, leb; uint16_t lex;
      int dsym, deb; uint16_t dex;
      encode_length(best_len, &lsym, &lex, &leb);
      encode_dist(best_dist, &dsym, &dex, &deb);
      blk->freq_ll[lsym]++;
      blk->freq_d[dsym]++;
      size_t end = pos + (size_t)best_len;
      size_t j = pos + 1;
      while (j < end) {
        insert_string(in, n, j, head, prev);
        j++;
      }
      pos = end;
    } else {
      if (!tok_push(&blk->toks, (Token){0, in[pos], 0, 0})) return 0;
      blk->freq_ll[in[pos++]]++;
    }
    sym_count++;
  }
  blk->raw_end = pos;
  *io_pos = pos;
  return 1;
}

typedef struct {
  int num_ll, num_d, num_cl, cl_nitems;
  uint8_t len_ll[286], len_d[30], len_cl[19];
  uint16_t code_ll[286], code_d[30], code_cl[19];
  CLItem * cl_items;
  uint64_t header_bits_after_btype; /* bits after the 3-bit block header (HLIT.. + CL stream) */
} DynTrees;
static int build_dynamic_trees(const uint32_t freq_ll_in[286], const uint32_t freq_d_in[30], DynTrees * dt) {
  memset(dt, 0, sizeof(*dt));
  uint32_t freq_ll[286], freq_d[30];
  memcpy(freq_ll, freq_ll_in, 286 * sizeof(uint32_t));
  memcpy(freq_d,  freq_d_in,  30 * sizeof(uint32_t));
  freq_ll[256]++;
  int dist_nonzero = 0;
  for (int i = 0; i < 30; i++) if (freq_d[i]) { dist_nonzero = 1; break; }
  if (!dist_nonzero) { freq_d[0] = 1; freq_d[1] = 1; }
  build_code_lengths(freq_ll, 286, 15, dt->len_ll);
  build_code_lengths(freq_d,  30,  15, dt->len_d);
  dt->num_ll = 286;
  while (dt->num_ll > 257 && dt->len_ll[dt->num_ll - 1] == 0) dt->num_ll--;
  if (dt->num_ll < 257) dt->num_ll = 257;
  dt->num_d = 30;
  while (dt->num_d > 1 && dt->len_d[dt->num_d - 1] == 0) dt->num_d--;
  if (dt->num_d < 1) dt->num_d = 1;
  uint8_t seq[400];
  for (int i = 0; i < dt->num_ll; i++) seq[i] = dt->len_ll[i];
  for (int i = 0; i < dt->num_d; i++)  seq[dt->num_ll + i] = dt->len_d[i];
  uint32_t freq_cl[19];
  dt->cl_items = rle_code_lengths(seq, dt->num_ll + dt->num_d, &dt->cl_nitems, freq_cl);
  if (!dt->cl_items) return 0;
  build_code_lengths(freq_cl, 19, 7, dt->len_cl);
  dt->num_cl = 19;
  while (dt->num_cl > 4 && dt->len_cl[cl_order[dt->num_cl - 1]] == 0) dt->num_cl--;
  make_canonical_codes_rev(dt->len_ll, 286, 15, dt->code_ll);
  make_canonical_codes_rev(dt->len_d,  30,  15, dt->code_d);
  make_canonical_codes_rev(dt->len_cl, 19, 7,  dt->code_cl);
  uint64_t hb = 0;
  hb += 5 + 5 + 4;        /* HLIT, HDIST, HCLEN */
  hb += (uint64_t)dt->num_cl * 3; /* code-length code lengths */
  for (int i = 0; i < dt->cl_nitems; i++) {
    uint8_t s = dt->cl_items[i].sym;
    hb += dt->len_cl[s];
    hb += dt->cl_items[i].ebits_n;
  }
  dt->header_bits_after_btype = hb;
  return 1;
}

typedef enum { BT_STORED = 0, BT_FIXED = 1, BT_DYNAMIC = 2 } BlockType;
static uint64_t estimate_fixed_bits(const Token * tok, size_t ntok) {
  uint8_t ll_lens[288], d_lens[32];
  uint16_t ll_codes[288], d_codes[32];
  make_fixed_lens(ll_lens, d_lens);
  make_canonical_codes_rev(ll_lens, 288, 15, ll_codes);
  make_canonical_codes_rev(d_lens, 32,  15, d_codes);
  uint64_t bits = 3;
  for (size_t i = 0; i < ntok; i++) {
    if (!tok[i].is_match) {
      bits += ll_lens[tok[i].lit];
    } else {
      int lsym, leb; uint16_t lex;
      int dsym, deb; uint16_t dex;
      encode_length(tok[i].len, &lsym, &lex, &leb);
      encode_dist(tok[i].dist, &dsym, &dex, &deb);
      bits += ll_lens[lsym] + (uint64_t)leb;
      bits += d_lens[dsym] + (uint64_t)deb;
    }
  }
  bits += ll_lens[256]; /* EOB */
  return bits;
}
static uint64_t estimate_dynamic_bits(const Token * tok, size_t ntok, const DynTrees * dt) {
  uint64_t bits = 3; /* BFINAL+BTYPE */
  bits += dt->header_bits_after_btype;
  for (size_t i = 0; i < ntok; i++) {
    if (!tok[i].is_match) {
      bits += dt->len_ll[tok[i].lit];
    } else {
      int lsym; uint16_t lex; int leb;
      int dsym; uint16_t dex; int deb;
      encode_length(tok[i].len, &lsym, &lex, &leb);
      encode_dist(tok[i].dist, &dsym, &dex, &deb);
      bits += dt->len_ll[lsym] + (uint64_t)leb;
      bits += dt->len_d[dsym] + (uint64_t)deb;
    }
  }
  bits += dt->len_ll[256]; /* EOB */
  return bits;
}
static uint64_t estimate_stored_bits(size_t raw_len, int bitcnt_mod8) {
  int pad = (8 - ((bitcnt_mod8 + 3) & 7)) & 7;
  if (raw_len > 65535u) return (uint64_t)-1;
  return 3ull + (uint64_t)pad + 32ull + (uint64_t)raw_len * 8ull;
}
static void write_block_stored(BitW * bw, int bfinal, const uint8_t * raw, size_t raw_len) {
  bw_write_bits(bw, (uint32_t)bfinal, 1);
  bw_write_bits(bw, 0, 2); /* stored */
  int pad = (8 - (bw->bitcnt & 7)) & 7;
  if (pad) bw_write_bits(bw, 0, pad);
  uint16_t L = (uint16_t)raw_len;
  uint16_t NL = (uint16_t)~L;
  fputc((int)(L & 0xFFu), bw->out);
  fputc((int)((L >> 8) & 0xFFu), bw->out);
  fputc((int)(NL & 0xFFu), bw->out);
  fputc((int)((NL >> 8) & 0xFFu), bw->out);
  fwrite(raw, 1, raw_len, bw->out);
}
static void write_block_fixed(BitW * bw, int bfinal, const Token * tok, size_t ntok) {
  uint8_t ll_lens[288], d_lens[32];
  uint16_t ll_codes[288], d_codes[32];
  make_fixed_lens(ll_lens, d_lens);
  make_canonical_codes_rev(ll_lens, 288, 15, ll_codes);
  make_canonical_codes_rev(d_lens, 32,  15, d_codes);
  bw_write_bits(bw, (uint32_t)bfinal, 1);
  bw_write_bits(bw, 1, 2); /* fixed */
  for (size_t i = 0; i < ntok; i++) {
    if (!tok[i].is_match) {
      uint16_t sym = tok[i].lit;
      bw_write_bits(bw, ll_codes[sym], ll_lens[sym]);
    } else {
      int lsym; uint16_t lex; int leb;
      int dsym; uint16_t dex; int deb;
      encode_length(tok[i].len, &lsym, &lex, &leb);
      encode_dist(tok[i].dist, &dsym, &dex, &deb);
      bw_write_bits(bw, ll_codes[lsym], ll_lens[lsym]);
      if (leb) bw_write_bits(bw, (uint32_t)lex, leb);
      bw_write_bits(bw, d_codes[dsym], d_lens[dsym]);
      if (deb) bw_write_bits(bw, (uint32_t)dex, deb);
    }
  }
  bw_write_bits(bw, ll_codes[256], ll_lens[256]); /* EOB */
}
static void write_block_dynamic(BitW * bw, int bfinal, const Token * tok, size_t ntok, DynTrees * dt) {
  bw_write_bits(bw, (uint32_t)bfinal, 1);
  bw_write_bits(bw, 2, 2); /* dynamic */
  bw_write_bits(bw, (uint32_t)(dt->num_ll - 257), 5);
  bw_write_bits(bw, (uint32_t)(dt->num_d - 1), 5);
  bw_write_bits(bw, (uint32_t)(dt->num_cl - 4), 4);
  for (int i = 0; i < dt->num_cl; i++)
    bw_write_bits(bw, (uint32_t)dt->len_cl[cl_order[i]], 3);
  for (int i = 0; i < dt->cl_nitems; i++) {
    uint8_t s = dt->cl_items[i].sym;
    bw_write_bits(bw, dt->code_cl[s], dt->len_cl[s]);
    if (dt->cl_items[i].ebits_n)
      bw_write_bits(bw, dt->cl_items[i].ebits_v, dt->cl_items[i].ebits_n);
  }
  for (size_t i = 0; i < ntok; i++) {
    if (!tok[i].is_match) {
      uint16_t sym = tok[i].lit;
      bw_write_bits(bw, dt->code_ll[sym], dt->len_ll[sym]);
    } else {
      int lsym, leb; uint16_t lex;
      int dsym, deb; uint16_t dex;
      encode_length(tok[i].len, &lsym, &lex, &leb);
      encode_dist(tok[i].dist, &dsym, &dex, &deb);
      bw_write_bits(bw, dt->code_ll[lsym], dt->len_ll[lsym]);
      if (leb) bw_write_bits(bw, (uint32_t)lex, leb);
      bw_write_bits(bw, dt->code_d[dsym], dt->len_d[dsym]);
      if (deb) bw_write_bits(bw, (uint32_t)dex, deb);
    }
  }
  bw_write_bits(bw, dt->code_ll[256], dt->len_ll[256]); /* EOB */
}
static int read_all(FILE * in, uint8_t ** out_buf, size_t * out_len, uint32_t * out_crc) {
  size_t cap = 1 << 20, len = 0;
  uint8_t * buf = (uint8_t *) malloc(cap);
  if (!buf) return 0;
  uint32_t crc = 0xFFFFFFFFu;
  for (;;) {
    if (len == cap) {
      cap *= 2;
      uint8_t * nb = (uint8_t *) realloc(buf, cap);
      if (!nb) { free(buf); return 0; }
      buf = nb;
    }
    size_t n = fread(buf + len, 1, cap - len, in);
    if (n) {
      crc = crc32_update(crc, buf + len, n);
      len += n;
    }
    if (n == 0) {
      if (ferror(in)) { free(buf); return 0; }
      break;
    }
  }
  *out_buf = buf;  *out_len = len;
  *out_crc = crc ^ 0xFFFFFFFFu;
  return 1;
}
static int gzip_compress(FILE * in, FILE * out, const char * in_path, int level) {
  int ok = 0;
  uint8_t * buf = NULL;
  int32_t * head = NULL, * prev = NULL;
  size_t len = 0;
  uint32_t crc = 0;
  if (!read_all(in, &buf, &len, &crc)) goto done;
  write_gzip_header(out, in_path, level);
  head = (int32_t *) malloc(HASH_SIZE * sizeof(int32_t));
  prev = (int32_t *) malloc(len ? len * sizeof(int32_t) : 1);
  if (!head || !prev) goto done;
  for (uint32_t i = 0; i < HASH_SIZE; i++) head[i] = -1;
  for (size_t i = 0; i < len; i++) prev[i] = -1;
  DefParams p;
  if (level < 1) level = 1;
  if (level > 9) level = 9;
  p.level = level;
  if (level == 9) {
    p.good_length = 32;
    p.max_lazy = 258;  p.nice_length = 258;  p.max_chain = 4096;
  } else if (level >= 6) {
    p.good_length = 8;
    p.max_lazy = 32;  p.nice_length = 128;  p.max_chain = 256;
  } else {
    p.good_length = 4;
    p.max_lazy = 16;  p.nice_length = 64;  p.max_chain = 64;
  }
  BitW bw = { out, 0, 0 };
  if (len == 0) {
    write_block_fixed(&bw, 1, NULL, 0);
    bw_flush_final(&bw);
    put_u32_le(out, crc);
    put_u32_le(out, 0);
    ok = 1;
    goto done;
  }
  size_t pos = 0;
  while (pos < len) {
    Block blk;
    if (!tokenize_next_block(buf, len, &pos, head, prev, p, &blk)) {
      block_free(&blk);
      goto done;
    }
    DynTrees dt;
    if (!build_dynamic_trees(blk.freq_ll, blk.freq_d, &dt)) {
      block_free(&blk);
      goto done;
    }
    size_t raw_len = blk.raw_end - blk.raw_start;
    const uint8_t *raw = buf + blk.raw_start;
    uint64_t bits_fixed = estimate_fixed_bits(blk.toks.t, blk.toks.n);
    uint64_t bits_dyn   = estimate_dynamic_bits(blk.toks.t, blk.toks.n, &dt);
    uint64_t bits_sto   = estimate_stored_bits(raw_len, bw.bitcnt & 7);
    BlockType bt = BT_DYNAMIC;
    uint64_t best = bits_dyn;
    if (bits_fixed < best) { best = bits_fixed; bt = BT_FIXED; }
    if (bits_sto != (uint64_t)-1 && bits_sto < best) { best = bits_sto; bt = BT_STORED; }
    int bfinal = (pos == len);
    if (bt == BT_STORED) {
      write_block_stored(&bw, bfinal, raw, raw_len);
    } else if (bt == BT_FIXED) {
      write_block_fixed(&bw, bfinal, blk.toks.t, blk.toks.n);
    } else {
      write_block_dynamic(&bw, bfinal, blk.toks.t, blk.toks.n, &dt);
    }
    free(dt.cl_items);
    block_free(&blk);
  }
  bw_flush_final(&bw);
  put_u32_le(out, crc);
  put_u32_le(out, (uint32_t)(len & 0xFFFFFFFFu));
  ok = 1;
done:
  free(head);
  free(prev);
  free(buf);
  return ok;
}
static int skip_gzip_header(BitR * br) {
  int ok = 1;
  int id1 = br_read_byte_aligned(br, &ok); if (!ok) return 0;
  int id2 = br_read_byte_aligned(br, &ok); if (!ok) return 0;
  if (id1 != 0x1f || id2 != 0x8b) return -1;
  int cm = br_read_byte_aligned(br, &ok); if (!ok) return -1;
  int flg = br_read_byte_aligned(br, &ok); if (!ok) return -1;
  if (cm != 8) return -1;
  for (int i = 0; i < 6; i++) { (void)br_read_byte_aligned(br, &ok); if (!ok) return -1; }
  if (flg & 0x04) { /* FEXTRA */
    int xlen0 = br_read_byte_aligned(br, &ok); if (!ok) return -1;
    int xlen1 = br_read_byte_aligned(br, &ok); if (!ok) return -1;
    int xlen = xlen0 | (xlen1 << 8);
    for (int i = 0; i < xlen; i++) { (void)br_read_byte_aligned(br, &ok); if (!ok) return -1; }
  }
  if (flg & 0x08) { int c; do { c = br_read_byte_aligned(br, &ok); if (!ok) return -1; } while (c != 0); }
  if (flg & 0x10) { int c; do { c = br_read_byte_aligned(br, &ok); if (!ok) return -1; } while (c != 0); }
  if (flg & 0x02) { br_read_byte_aligned(br, &ok); if (!ok) return -1; br_read_byte_aligned(br, &ok); if (!ok) return -1; }
  return 1;
}
static int inflate_stream(BitR * br, FILE * out, uint32_t * out_crc, uint32_t * out_isize) {
  uint32_t crc = 0xFFFFFFFFu, isz = 0;
  size_t wpos = 0;
  uint8_t window[WSIZE], fixed_ll_lens[288], fixed_d_lens[32];
  DecEnt * fixed_ll_tab = (DecEnt*)malloc((1u << DECODE_BITS) * sizeof(DecEnt));
  DecEnt * fixed_d_tab  = (DecEnt*)malloc((1u << DECODE_BITS) * sizeof(DecEnt));
#define INFLATE_FAIL() do { free(fixed_ll_tab); free(fixed_d_tab); return 0; } while (0)
#define INFLATE_BLOCK_FAIL() do { free(cl_tab); free(dyn_ll_tab); free(dyn_d_tab); INFLATE_FAIL(); } while (0)
#define INFLATE_OUTBYTE(v) do { \
  uint8_t _b = (uint8_t)(v); \
  fputc(_b, out); \
  window[wpos] = _b; \
  wpos = (wpos + 1) & (WSIZE - 1); \
  crc = crc32_update(crc, &_b, 1); \
  isz++; \
} while (0)
  if (!fixed_ll_tab || !fixed_d_tab) { INFLATE_FAIL(); }
  make_fixed_lens(fixed_ll_lens, fixed_d_lens);
  if (!build_decode_table(fixed_ll_lens, 288, 15, DECODE_BITS, fixed_ll_tab)) { INFLATE_FAIL(); }
  if (!build_decode_table(fixed_d_lens,  32,  15, DECODE_BITS, fixed_d_tab))  { INFLATE_FAIL(); }
  int bfinal = 0;
  while (!bfinal) {
    DecEnt * dyn_ll_tab = NULL, * dyn_d_tab = NULL, * cl_tab = NULL;
    DecEnt * ll_tab = NULL, * d_tab = NULL;
    int ll_bits = DECODE_BITS, d_bits = DECODE_BITS;
    if (!br_fill(br, 3)) { free(fixed_ll_tab); free(fixed_d_tab); return 0; }
    bfinal = (int) br_read_bits(br, 1);
    int btype = (int) br_read_bits(br, 2);
    if (btype == 0) {
      int ok = 1;
      int l0 = br_read_byte_aligned(br, &ok); if (!ok) INFLATE_BLOCK_FAIL();
      int l1 = br_read_byte_aligned(br, &ok); if (!ok) INFLATE_BLOCK_FAIL();
      int nl0 = br_read_byte_aligned(br, &ok); if (!ok) INFLATE_BLOCK_FAIL();
      int nl1 = br_read_byte_aligned(br, &ok); if (!ok) INFLATE_BLOCK_FAIL();
      uint16_t L = (uint16_t) ((uint16_t)l0 | ((uint16_t)l1 << 8));
      uint16_t NL = (uint16_t) ((uint16_t)nl0 | ((uint16_t)nl1 << 8));
      if ((uint16_t)~L != NL) INFLATE_BLOCK_FAIL();
      for (uint16_t i = 0; i < L; i++) {
        int c = br_read_byte_aligned(br, &ok);
        if (!ok) INFLATE_BLOCK_FAIL();
        INFLATE_OUTBYTE(c);
      }
    } else {
      uint8_t dyn_ll_lens[288] = {0}, dyn_d_lens[32] = {0};
      if (btype == 1) {
        ll_tab = fixed_ll_tab;
        d_tab  = fixed_d_tab;
      } else if (btype == 2) {
        int HLIT  = (int)br_read_bits(br, 5) + 257;
        int HDIST = (int)br_read_bits(br, 5) + 1;
        int HCLEN = (int)br_read_bits(br, 4) + 4;
        if (HLIT < 257 || HLIT > 286 || HDIST < 1 || HDIST > 32) INFLATE_BLOCK_FAIL();
        uint8_t cl_lens[19] = {0};
        for (int i = 0; i < HCLEN; i++) cl_lens[cl_order[i]] = (uint8_t)br_read_bits(br, 3);
        cl_tab = (DecEnt *) malloc((1u << CL_DECODE_BITS) * sizeof(DecEnt));
        if (!cl_tab) INFLATE_BLOCK_FAIL();
        if (!build_decode_table(cl_lens, 19, 7, CL_DECODE_BITS, cl_tab)) INFLATE_BLOCK_FAIL();
        int total = HLIT + HDIST;
        uint8_t lens_all[320];
        for (int i = 0; i < total; ) {
          int sym;
          if (!huff_decode(br, cl_tab, CL_DECODE_BITS, &sym)) INFLATE_BLOCK_FAIL();
          if (sym <= 15) {
            lens_all[i++] = (uint8_t)sym;
          } else if (sym == 16) {
            if (i == 0) INFLATE_BLOCK_FAIL();
            int rep = (int)br_read_bits(br, 2) + 3;
            uint8_t prevL = lens_all[i - 1];
            while (rep-- && i < total) lens_all[i++] = prevL;
          } else if (sym == 17) {
            int rep = (int)br_read_bits(br, 3) + 3;
            while (rep-- && i < total) lens_all[i++] = 0;
          } else if (sym == 18) {
            int rep = (int)br_read_bits(br, 7) + 11;
            while (rep-- && i < total) lens_all[i++] = 0;
          } else {
            INFLATE_BLOCK_FAIL();
          }
        }
        for (int i = 0; i < HLIT; i++) dyn_ll_lens[i] = lens_all[i];
        for (int i = 0; i < HDIST; i++) dyn_d_lens[i] = lens_all[HLIT + i];
        int d_nz = 0;
        for (int i = 0; i < 32; i++) if (dyn_d_lens[i]) { d_nz = 1; break; }
        if (!d_nz) dyn_d_lens[0] = 1;
        dyn_ll_tab = (DecEnt *) malloc((1u << DECODE_BITS) * sizeof(DecEnt));
        dyn_d_tab  = (DecEnt *) malloc((1u << DECODE_BITS) * sizeof(DecEnt));
        if (!dyn_ll_tab || !dyn_d_tab) INFLATE_BLOCK_FAIL();
        if (!build_decode_table(dyn_ll_lens, 288, 15, DECODE_BITS, dyn_ll_tab)) INFLATE_BLOCK_FAIL();
        if (!build_decode_table(dyn_d_lens,  32,  15, DECODE_BITS, dyn_d_tab)) INFLATE_BLOCK_FAIL();
        free(cl_tab);
        cl_tab = NULL;
        ll_tab = dyn_ll_tab;
        d_tab  = dyn_d_tab;
      } else {
        INFLATE_BLOCK_FAIL();
      }
      for (;;) {
        int sym;
        if (!huff_decode(br, ll_tab, ll_bits, &sym)) INFLATE_BLOCK_FAIL();
        if (sym < 256) {
          INFLATE_OUTBYTE(sym);
        } else if (sym == 256) {
          break;
        } else {
          if (sym < 257 || sym > 285) INFLATE_BLOCK_FAIL();
          int out_len;
          if (sym == 285) {
            out_len = 258;
          } else {
            int len_idx = sym - 257;
            int len_extra_bits = len_ebits[len_idx];
            int len_extra = len_extra_bits ? (int)br_read_bits(br, len_extra_bits) : 0;
            out_len = len_base[len_idx] + len_extra;
          }
          int dsym;
          if (!huff_decode(br, d_tab, d_bits, &dsym)) INFLATE_BLOCK_FAIL();
          if (dsym < 0 || dsym > 29) INFLATE_BLOCK_FAIL();
          int dist_extra_bits = dist_ebits[dsym];
          int dist_extra = dist_extra_bits ? (int)br_read_bits(br, dist_extra_bits) : 0;
          int out_dist = dist_base[dsym] + dist_extra;
          if (out_dist <= 0 || out_dist > WSIZE) INFLATE_BLOCK_FAIL();
          for (int k = 0; k < out_len; k++) INFLATE_OUTBYTE(window[(wpos - (size_t)out_dist) & (WSIZE - 1)]);
        }
      }
    }
    free(cl_tab);
    free(dyn_ll_tab);
    free(dyn_d_tab);
  }
  free(fixed_ll_tab);
  free(fixed_d_tab);
  *out_crc = crc ^ 0xFFFFFFFFu;
  *out_isize = isz;
  return 1;
#undef INFLATE_OUTBYTE
#undef INFLATE_BLOCK_FAIL
#undef INFLATE_FAIL
}
static int gzip_decompress(FILE * in, FILE * out) {
  BitR br = { in, 0, 0, 0 };
  for (;;) {
    int hdr = skip_gzip_header(&br);
    if (hdr == 0) return 1;
    if (hdr < 0) return 0;
    uint32_t crc_calc = 0, isz_calc = 0;
    if (!inflate_stream(&br, out, &crc_calc, &isz_calc)) return 0;
    int ok = 1;
    uint32_t crc_file = 0, isz_file = 0;
    for (int i = 0; i < 4; i++) { int b = br_read_byte_aligned(&br, &ok); if (!ok) return 0; crc_file |= (uint32_t)b << (i * 8); }
    for (int i = 0; i < 4; i++) { int b = br_read_byte_aligned(&br, &ok); if (!ok) return 0; isz_file |= (uint32_t)b << (i * 8); }
    if (crc_file != crc_calc || isz_file != isz_calc) return 0;
  }
}
static void usage(const char * argv0) {
  fprintf(stderr,
    "pdgzip written by kamila szewczyk (iczelia). released to the public domain.\n"
    "Usage:\n"
    "  %s [-1..-9] [input [output]]    (compress, default level 9)\n"
    "  %s -d [input [output]]          (decompress)\n", argv0, argv0);
}
int main(int argc, char ** argv) {
  crc32_init();
  int decompress = 0, level = 9;
  const char * in_path = NULL, * out_path = NULL;
  int ai = 1;
  while (ai < argc && argv[ai][0] == '-') {
    if (strcmp(argv[ai], "-d") == 0) { decompress = 1; ai++; continue; }
    if (strlen(argv[ai]) == 2 && argv[ai][1] >= '1' && argv[ai][1] <= '9') { level = argv[ai][1] - '0'; ai++; continue; }
    usage(argv[0]); return 1;
  }
  if (ai < argc) in_path = argv[ai++];
  if (ai < argc) out_path = argv[ai++];
  if (ai < argc) { usage(argv[0]); return 1; }
  FILE * in = in_path ? fopen(in_path, "rb") : stdin;
  FILE * out = out_path ? fopen(out_path, "wb") : stdout;
  if (!in) { perror("open input"); return 1; }
  if (!out) { perror("open output"); if (in_path) fclose(in); return 1; }
  int ok = decompress ? gzip_decompress(in, out) : gzip_compress(in, out, in_path, level);
  if (in_path) fclose(in);
  if (out_path) fclose(out);
  if (!ok) { fprintf(stderr, "error\n"); return 1; }
}
