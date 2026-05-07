/*  pdgzip: fast, embeddable gzip decoder.
    Written in 2026 by Kamila Szewczyk (k@iczelia.net).
    License: 0BSD.  Attribution welcomed but not required.  */
#ifndef PDGZIP_H
#define PDGZIP_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque decoder handle.  The full state lives inside caller-provided
   scratch memory; see pdgzip_state_size() and pdgzip_init().  */
struct pdgzip;
typedef struct pdgzip pdgzip_t;

/* Read callback: pull compressed input from the caller's source.
   Must fill up to `len` bytes into `buf` and return the number of bytes
   actually read.  A return of 0 (or any value < len) is treated as end
   of input; further calls will not be made after a short read.  */
typedef size_t (* pdgzip_read_fn)(void * user, void * buf, size_t len);

typedef struct {
    pdgzip_read_fn read;   /*  required  */
    void * user;           /*  passed back to `read` verbatim  */
    int concat;            /*  nonzero: decode concatenated gzip members
                               as one logical stream (stops when source
                               signals EOF at a member boundary)  */
} pdgzip_cfg_t;

/*  Constant size, in bytes, of the scratch buffer required by one decoder
    instance.  Never changes at runtime for a given build.  */
size_t pdgzip_state_size(void);

/*  Required alignment of the scratch buffer, in bytes.  */
size_t pdgzip_state_align(void);

/*  Set up a decoder in caller-provided scratch memory.
   `scratch` must point to at least pdgzip_state_size() bytes aligned to
    pdgzip_state_align().  The decoder performs no allocations and touches
    no global state; `scratch` may be freed or reused for a new stream
    (via another pdgzip_init) as soon as the caller is done with it.
    Returns a handle backed by `scratch`, or NULL if cfg/scratch is bad.  */
pdgzip_t * pdgzip_init(void * scratch, const pdgzip_cfg_t * cfg);

/*  Decompress up to `n` bytes into `buf`.
      > 0 : bytes produced
      = 0 : clean end of stream, trailer (CRC32) verified
      < 0 : error, one of PDGZIP_E_*; the handle is unusable afterwards.  */
int64_t pdgzip_read(pdgzip_t * gz, void * buf, size_t n);

enum {
  PDGZIP_E_FORMAT   = -1,  /*  malformed gzip/deflate stream         */
  PDGZIP_E_CHECKSUM = -2,  /*  trailer CRC32 did not match           */
  PDGZIP_E_IO       = -3   /*  read callback hit EOF mid-stream      */
};

#ifdef __cplusplus
}
#endif

#endif
