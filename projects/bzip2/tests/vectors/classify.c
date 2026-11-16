/* Reference driver for the golden vectors: runs the vendored libbz2 over a file exactly as
   uncompressStream does (`bzip2.c:435-543`: concatenated streams, `bzip2.c:454-481`; garbage
   after the first stream ignored, `bzip2.c:536-543`). Usage: classify IN OUT. Writes the
   output to OUT and prints one of ok | magic | data | eof | other on stdout. */
#include <stdio.h>
#include <string.h>
#include "bzlib.h"

int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: classify IN OUT\n"); return 2; }
  FILE *in = fopen(argv[1], "rb"), *out = fopen(argv[2], "wb");
  if (!in || !out) { perror("open"); return 2; }
  unsigned char obuf[5000], unused[BZ_MAX_UNUSED], *tmp;
  int nUnused = 0, streamNo = 0, bzerr, nread, i;
  void *unusedV;
  const char *res = "other";
  for (;;) {
    BZFILE *bzf = BZ2_bzReadOpen(&bzerr, in, 0, 0, unused, nUnused);
    if (bzf == NULL || bzerr != BZ_OK) goto fail;
    streamNo++;
    while (bzerr == BZ_OK) {
      nread = BZ2_bzRead(&bzerr, bzf, obuf, 5000);
      if (bzerr == BZ_DATA_ERROR_MAGIC) goto fail;
      if ((bzerr == BZ_OK || bzerr == BZ_STREAM_END) && nread > 0) fwrite(obuf, 1, nread, out);
    }
    if (bzerr != BZ_STREAM_END) goto fail;
    BZ2_bzReadGetUnused(&bzerr, bzf, &unusedV, &nUnused);
    tmp = unusedV;
    for (i = 0; i < nUnused; i++) unused[i] = tmp[i];
    BZ2_bzReadClose(&bzerr, bzf);
    if (nUnused == 0 && feof(in)) break;
    if (nUnused == 0) { int c = fgetc(in); if (c == EOF) break; ungetc(c, in); }
  }
  puts("ok");
  fclose(out);
  return 0;
fail:
  if (bzerr == BZ_DATA_ERROR_MAGIC) res = streamNo <= 1 ? "magic" : "ok";
  else if (bzerr == BZ_DATA_ERROR) res = "data";
  else if (bzerr == BZ_UNEXPECTED_EOF) res = "eof";
  puts(res);
  fclose(out);
  return 0;
}
