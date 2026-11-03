/*  xxhash.c -- streaming XXH3 128-bit for Isabelle/ML (library/xxhash.ML).
    Part of libperformant_isabelle_ml, the native half of Performant_Isabelle_ML.

    Five entry points over an opaque state:

      xxh128_create()               a fresh state, seed 0; NULL if out of memory.
      xxh128_update(st, buf, len)   feed len bytes.
      xxh128_update_file(st, path)  feed the bytes of the file at path (UTF-8, the
                                    platform's form), read in blocks; 0, or an errno
                                    value.  A read error is a failure, so a directory
                                    or an unreadable file never hashes as empty.
      xxh128_digest(st, out)        the 16-byte canonical (big-endian) digest of
                                    everything fed so far -- what Python's
                                    xxhash.xxh128().digest() returns.
      xxh128_free(st)               release the state.

    The hash is xxHash's own: xxhash.h (v0.8.3, vendored unmodified; see README),
    inlined with XXH_INLINE_ALL, so none of its symbols is exported and no other
    copy of xxHash in the process can clash with it.

    Files are opened in binary mode, so no newline translation happens on Windows.
    There the UTF-8 path is converted to UTF-16 and opened with _wfopen: the
    narrow fopen would read it in the ANSI code page and fail on non-ASCII names. */

#define XXH_INLINE_ALL
#include "xxhash.h"

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#include <windows.h>
/* Resolved by name (GetProcAddress); exported explicitly, as in thread_cpu.c. */
#define XXH128_API __declspec(dllexport)
#else
#define XXH128_API
#endif

XXH128_API void *xxh128_create(void);
XXH128_API void xxh128_update(void *st, const uint8_t *buf, size_t len);
XXH128_API int xxh128_update_file(void *st, const char *path);
XXH128_API void xxh128_digest(void *st, uint8_t out[16]);
XXH128_API void xxh128_free(void *st);

/* Allocated, not on the stack: the calling thread is an ML thread whose C
   stack size is not ours to assume. */
#define BLOCK_SIZE ((size_t)64 * 1024)

void *xxh128_create(void)
{
  XXH3_state_t *st = XXH3_createState();
  if (st != NULL && XXH3_128bits_reset(st) != XXH_OK) {
    XXH3_freeState(st);
    return NULL;
  }
  return st;
}

void xxh128_update(void *st, const uint8_t *buf, size_t len)
{
  (void)XXH3_128bits_update((XXH3_state_t *)st, buf, len);
}

static int error_code(void) { return errno != 0 ? errno : EIO; }

static FILE *open_binary(const char *path)
{
#if defined(_WIN32)
  int n = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, path, -1, NULL, 0);
  if (n <= 0) { errno = EINVAL; return NULL; }
  wchar_t *wpath = malloc((size_t)n * sizeof(wchar_t));
  if (wpath == NULL) { errno = ENOMEM; return NULL; }
  if (MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, path, -1, wpath, n) != n) {
    free(wpath);
    errno = EINVAL;
    return NULL;
  }
  errno = 0;
  FILE *f = _wfopen(wpath, L"rb");
  free(wpath);
  return f;
#else
  errno = 0;
  return fopen(path, "rb");
#endif
}

int xxh128_update_file(void *st, const char *path)
{
  FILE *f = open_binary(path);
  if (f == NULL) return error_code();

  unsigned char *buf = malloc(BLOCK_SIZE);
  if (buf == NULL) { fclose(f); return ENOMEM; }

  int err = 0;
  size_t n;
  errno = 0;
  while ((n = fread(buf, 1, BLOCK_SIZE, f)) > 0)
    (void)XXH3_128bits_update((XXH3_state_t *)st, buf, n);
  if (ferror(f)) err = error_code();

  free(buf);
  fclose(f);
  return err;
}

void xxh128_digest(void *st, uint8_t out[16])
{
  XXH128_canonical_t c;
  XXH128_canonicalFromHash(&c, XXH3_128bits_digest((const XXH3_state_t *)st));
  memcpy(out, c.digest, sizeof c.digest);
}

void xxh128_free(void *st)
{
  XXH3_freeState((XXH3_state_t *)st);
}
