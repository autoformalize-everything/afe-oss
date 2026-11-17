/* Driver for tests/vectors/decompress-symbols: runs the vendored libbz2 on a bzip2 stream until
   the first block's symbols are decoded and prints what `BZ2_decompress` left behind.

     symbols FILE.bz2

   The stream is given to BZ2_bzDecompress whole, with room for one output byte. The library
   decodes the first block (decompress.c:354-490, the symbols; then the inverse transform's
   setup, decompress.c:497-572), writes one byte and returns; nothing here re-implements any of
   it. The state is then read from `strm->state` (bzlib_private.h:360-430). The low byte of each
   `tt` entry is the symbol decoder's output; the setup only adds links above it
   (decompress.c:567-568).

   Output lines:
     result R    ok (the block was decoded); data (BZ_DATA_ERROR); eof (the input ended, so
                 BZ2_decompress returned BZ_OK with avail_in == 0, which BZ2_bzRead reports as
                 BZ_UNEXPECTED_EOF, bzlib.c:1204-1209); other
   and for `ok` only:
     nblock N    the number of bytes in the block
     pos P       bits consumed from the stream (total_in * 8 - bsLive) after the last symbol
     unzftab ... the 256 byte counts
     hash H      h = h * 31 + byte over the block's bytes, h a UInt32 starting at 0
     tt HH ...   the bytes in hex, only when there are at most 4096 */
#include <stdio.h>
#include <stdlib.h>
#include "bzlib_private.h"

int main(int argc, char **argv)
{
   if (argc != 2) { fprintf(stderr, "usage: symbols FILE.bz2\n"); return 2; }
   FILE *f = fopen(argv[1], "rb");
   if (!f) { perror("open"); return 2; }
   static char in[1 << 20];
   size_t n = fread(in, 1, sizeof in, f);
   fclose(f);
   bz_stream strm;
   strm.bzalloc = NULL; strm.bzfree = NULL; strm.opaque = NULL;
   if (BZ2_bzDecompressInit(&strm, 0, 0) != BZ_OK) return 2;
   char out[1];
   strm.next_in = in; strm.avail_in = (unsigned int)n;
   strm.next_out = out; strm.avail_out = 1;
   int r = BZ2_bzDecompress(&strm);
   if (r == BZ_DATA_ERROR || r == BZ_DATA_ERROR_MAGIC) { puts("result data"); return 0; }
   if (r == BZ_OK && strm.avail_in == 0 && strm.avail_out == 1) { puts("result eof"); return 0; }
   if (r != BZ_OK || strm.avail_out != 0) { puts("result other"); return 0; }
   DState *s = strm.state;
   puts("result ok");
   printf("nblock %d\n", s->save_nblock);
   printf("pos %u\n", strm.total_in_lo32 * 8 - (unsigned int)s->bsLive);
   printf("unzftab");
   for (int i = 0; i < 256; i++) printf(" %d", s->unzftab[i]);
   printf("\n");
   UInt32 h = 0;
   for (int i = 0; i < s->save_nblock; i++) h = h * 31 + (s->tt[i] & 0xff);
   printf("hash %u\n", h);
   if (s->save_nblock <= 4096) {
      printf("tt");
      for (int i = 0; i < s->save_nblock; i++) printf(" %02x", s->tt[i] & 0xff);
      printf("\n");
   }
   return 0;
}
