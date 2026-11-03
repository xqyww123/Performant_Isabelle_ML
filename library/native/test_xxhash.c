/*  test_xxhash.c -- self-test for the xxh128 entry points, run by ./build on
    every target, Windows included.

      test_xxhash LIBRARY SCRATCH_DIR

    Loads the freshly built library the way Poly/ML will (dlopen / LoadLibrary)
    and checks, against digests pinned from Python's xxhash.xxh128:
      1. one-shot updates over inputs covering every XXH3 length class
         (0, 1-3, 4-8, 9-16, 17-128, 129-240, 241-1024, several blocks);
      2. the same inputs fed in pseudo-random pieces give the same digests;
      3. xxh128_update_file over files of those lengths -- among them a 0-byte
         file and files larger than its 64 KiB read block -- and over a file
         whose name is not ASCII (created on Windows with a wide-character name,
         so its creation does not share the library's UTF-8 conversion);
      4. a missing file and a directory both fail.
    Writes only inside SCRATCH_DIR.  Exit status 1 on any failure.           */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#include <windows.h>
#include <direct.h>
#define chdir _chdir
static HMODULE lib;
static int load(const char *path) { lib = LoadLibraryA(path); return lib != NULL; }
static void *sym(const char *name) { return (void *)GetProcAddress(lib, name); }
#else
#include <dlfcn.h>
#include <unistd.h>
static void *lib;
static int load(const char *path) { lib = dlopen(path, RTLD_NOW | RTLD_LOCAL); return lib != NULL; }
static void *sym(const char *name) { return dlsym(lib, name); }
#endif

typedef void *(*create_fn)(void);
typedef void (*update_fn)(void *, const uint8_t *, size_t);
typedef int (*update_file_fn)(void *, const char *);
typedef void (*digest_fn)(void *, uint8_t *);
typedef void (*free_fn)(void *);

static create_fn xxh128_create;
static update_fn xxh128_update;
static update_file_fn xxh128_update_file;
static digest_fn xxh128_digest;
static free_fn xxh128_free;

/* Python: xxhash.xxh128(gen(n)).hexdigest(), with gen the generator below. */
static const struct { size_t len; const char *hex; } vectors[] = {
  {      0, "99aa06d3014798d86001c324468d497f"},
  {      1, "5e33aa40b898f6f90de0f3cef1e76922"},
  {      3, "3d10cb6802b68f06a434d638feb579dc"},
  {      4, "9672e4b44f44b2070dcaa12c359c6ae1"},
  {      8, "c55f9bfc342bc90b2523cd3549545611"},
  {      9, "025faa7c2f136210ccb73573bf4f3f50"},
  {     16, "1bf96d5f63f46cd50f7a68caa8759209"},
  {     17, "f128bc4b214ec3eb6fcb7a39f5d12c04"},
  {    128, "9da5dfbd217ec644cd151da49daa5378"},
  {    129, "736740f77724d18b00a28cfadf372d44"},
  {    240, "11e89fa8990fc86841804516bc34e8ba"},
  {    241, "7fb64a3fe8a9193625ebd647d0cad5f9"},
  {   1024, "05b6d358992d0878b67d9e9c04ceda9d"},
  {   1025, "ecf397b86a2eb252f9c5ce44fe38d3c7"},
  {  65536, "9dc181c6d5109c0d843841842c3a1aed"},
  {  65537, "a813b47dcae879ae2a3b0f92157c7e87"},
  {1048593, "fbf24d05ce2da81a8fab70e50318a673"},
};
#define N_VECTORS (sizeof vectors / sizeof vectors[0])
#define MAX_LEN 1048593

/* def gen(n):
     x = 0x12345678; out = bytearray(n)
     for i in range(n): x = (x*1664525 + 1013904223) & 0xffffffff; out[i] = x >> 24 */
static void gen(uint8_t *out, size_t n)
{
  uint32_t x = 0x12345678u;
  for (size_t i = 0; i < n; i++) { x = x * 1664525u + 1013904223u; out[i] = (uint8_t)(x >> 24); }
}

static void to_hex(const uint8_t d[16], char out[33])
{
  static const char hex[] = "0123456789abcdef";
  for (int i = 0; i < 16; i++) { out[2 * i] = hex[d[i] >> 4]; out[2 * i + 1] = hex[d[i] & 15]; }
  out[32] = 0;
}

static int failures;

static void expect(const char *what, size_t len, const uint8_t d[16], const char *want)
{
  char got[33];
  to_hex(d, got);
  if (strcmp(got, want) != 0) {
    printf("  FAIL: %s, %lu bytes: %s, expected %s\n", what, (unsigned long)len, got, want);
    failures++;
  }
}

static void one_shot(const uint8_t *data, size_t len, uint8_t d[16])
{
  void *st = xxh128_create();
  if (st == NULL) { printf("  FAIL: xxh128_create returned NULL\n"); failures++; memset(d, 0, 16); return; }
  xxh128_update(st, data, len);
  xxh128_digest(st, d);
  xxh128_free(st);
}

/* Pieces of 0..300 bytes, so they straddle XXH3's 256-byte internal buffer. */
static void pieces(const uint8_t *data, size_t len, uint8_t d[16])
{
  uint32_t x = 0x9e3779b9u + (uint32_t)len;
  void *st = xxh128_create();
  if (st == NULL) { printf("  FAIL: xxh128_create returned NULL\n"); failures++; memset(d, 0, 16); return; }
  size_t i = 0;
  while (i < len) {
    x = x * 1664525u + 1013904223u;
    size_t k = (x >> 16) % 301;
    if (k > len - i) k = len - i;
    xxh128_update(st, data + i, k);
    i += k;
  }
  xxh128_digest(st, d);
  xxh128_free(st);
}

static int write_file(FILE *f, const uint8_t *data, size_t len)
{
  int ok = f != NULL && fwrite(data, 1, len, f) == len;
  if (f != NULL && fclose(f) != 0) ok = 0;
  return ok;
}

/* 0 on success: the digest is in d. */
static int hash_file(const char *path, uint8_t d[16])
{
  void *st = xxh128_create();
  if (st == NULL) { printf("  FAIL: xxh128_create returned NULL\n"); failures++; return -1; }
  int r = xxh128_update_file(st, path);
  if (r == 0) xxh128_digest(st, d);
  xxh128_free(st);
  return r;
}

int main(int argc, char **argv)
{
  if (argc != 3) { fprintf(stderr, "usage: %s LIBRARY SCRATCH_DIR\n", argv[0]); return 2; }
  if (!load(argv[1])) { printf("FAIL: cannot load %s\n", argv[1]); return 1; }
  xxh128_create = (create_fn)sym("xxh128_create");
  xxh128_update = (update_fn)sym("xxh128_update");
  xxh128_update_file = (update_file_fn)sym("xxh128_update_file");
  xxh128_digest = (digest_fn)sym("xxh128_digest");
  xxh128_free = (free_fn)sym("xxh128_free");
  if (!xxh128_create || !xxh128_update || !xxh128_update_file || !xxh128_digest || !xxh128_free) {
    printf("FAIL: %s does not export all five xxh128_* entry points\n", argv[1]);
    return 1;
  }

  /* Every name from here on is relative to SCRATCH_DIR, so the directory's
     name never reaches the library's UTF-8 conversion. */
  if (chdir(argv[2]) != 0) { printf("FAIL: cannot enter %s\n", argv[2]); return 1; }

  uint8_t *data = malloc(MAX_LEN);
  char path[32];
  if (data == NULL) { printf("FAIL: out of memory\n"); return 1; }
  gen(data, MAX_LEN);
  uint8_t d[16];

  /* 1, 2, 3 */
  for (size_t i = 0; i < N_VECTORS; i++) {
    size_t len = vectors[i].len;
    one_shot(data, len, d);
    expect("one-shot", len, d, vectors[i].hex);
    pieces(data, len, d);
    expect("in pieces", len, d, vectors[i].hex);

    snprintf(path, sizeof path, "v%lu.bin", (unsigned long)len);
    if (!write_file(fopen(path, "wb"), data, len)) { printf("  FAIL: cannot write %s\n", path); failures++; continue; }
    int r = hash_file(path, d);
    if (r != 0) { printf("  FAIL: xxh128_update_file(%s) = %d\n", path, r); failures++; }
    else expect("file", len, d, vectors[i].hex);
  }
  printf("vectors:      %lu inputs, one-shot, in pieces and as files\n", (unsigned long)N_VECTORS);

  /* 3: a non-ASCII name ("xxh-测试-ü.bin"), 1025 bytes */
  {
    static const char name_utf8[] = "xxh-\xe6\xb5\x8b\xe8\xaf\x95-\xc3\xbc.bin";
#if defined(_WIN32)
    FILE *f = _wfopen(L"xxh-\u6d4b\u8bd5-\u00fc.bin", L"wb");
#else
    FILE *f = fopen(name_utf8, "wb");
#endif
    if (!write_file(f, data, 1025)) { printf("  FAIL: cannot create the non-ASCII file\n"); failures++; }
    else {
      int r = hash_file(name_utf8, d);
      if (r != 0) { printf("  FAIL: xxh128_update_file on the non-ASCII name = %d\n", r); failures++; }
      else expect("non-ASCII file name", 1025, d, "ecf397b86a2eb252f9c5ce44fe38d3c7");
    }
    printf("non-ASCII:    file name checked\n");
  }

  /* 4 */
  int r = hash_file("missing.bin", d);
  if (r == 0) { printf("  FAIL: a missing file hashed\n"); failures++; }
  printf("missing file: xxh128_update_file = %d\n", r);
  r = hash_file(".", d);
  if (r == 0) { printf("  FAIL: a directory hashed\n"); failures++; }
  printf("directory:    xxh128_update_file = %d\n", r);

  free(data);
  printf(failures ? "FAILED\n" : "OK\n");
  return failures ? 1 : 0;
}
