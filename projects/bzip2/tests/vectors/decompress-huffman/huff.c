/* Driver for tests/vectors/decompress-huffman: runs the vendored libbz2's Huffman decoding on
   cases given on stdin, and prints each case with what the C code computed.

     huff cases           reads cases from stdin, writes them with results to stdout
     huff lens FILE.bz2   decompresses FILE.bz2 with BZ2_bzDecompress and prints, for each
                          coding table of the last block, its code lengths and the limit, base,
                          perm and minLen the library built for it (`rminLen`, `rlimit`, ...)

   The tables are built by the library's BZ2_hbCreateDecodeTables (huffman.c:170-200) and
   symbols are read with GET_MTF_VAL, whose text (decompress.c:40-102) the build copies out of
   the vendored decompress.c into mtfval.h: nothing here re-implements either.

   A case is a run of lines ended by a blank line:
     # text            comment, echoed
     len L0 L1 ...     code lengths: the tables are built as decompress.c:339-352 does
     minLen M          } instead of `len`: the tables themselves (limit and base have 23
     limit ...         } entries, perm any number, the rest 0), to reach what no lengths give
     base ...          }
     perm ...          }
     bits HH HH ...    the input bytes, hex
     n N               how many symbols to read at most
   The output is the case with, for `len` cases, the derived minLen, limit, base and perm (the
   symbols by length, as many as there are lengths), then `syms` (the symbols read, until N or
   a failure), `pos` (bits consumed after the last symbol read) and `end` (`ok` after N
   symbols; `data` for BZ_DATA_ERROR; `eof` when the input ran out, BZ_OK from GET_BITS
   with avail_in == 0, which BZ2_bzRead reports as BZ_UNEXPECTED_EOF, bzlib.c:1204-1209). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "bzlib_private.h"
#include "mtfval.h"

#define SUCCESS (-100)

/* One GET_MTF_VAL on table 0 of `s`, reading from s->strm. The group bookkeeping is set so
   the macro uses table 0 as it stands (groupPos = 1: no selector is consulted). */
static Int32 get_sym(DState *s, Int32 *sym)
{
   Int32 retVal = SUCCESS;
   Int32 groupNo = 0, groupPos = 1, nSelectors = 1, gSel = 0;
   Int32 gMinlen = s->minLens[0];
   Int32 *gLimit = &(s->limit[0][0]);
   Int32 *gPerm = &(s->perm[0][0]);
   Int32 *gBase = &(s->base[0][0]);
   Int32 zn, zvec, zj, nextSym = 0;
   (void)groupNo; (void)nSelectors; (void)gSel;
   s->state = 0;
   switch (s->state) {
   default:
      GET_MTF_VAL(BZ_X_MTF_1, BZ_X_MTF_2, nextSym);
      *sym = nextSym;
   }
   save_state_and_return:
   return retVal;
}

static void print_arr(const char *name, const Int32 *a, int n)
{
   printf("%s", name);
   for (int i = 0; i < n; i++) printf(" %d", a[i]);
   printf("\n");
}

static int parse_ints(const char *p, Int32 *out, int max, int base)
{
   int n = 0;
   char *e;
   for (;;) {
      long v = strtol(p, &e, base);
      if (e == p) break;
      if (n < max) out[n] = (Int32)v;
      n++;
      p = e;
   }
   return n;
}

static void run_case(char lines[][65536], int nl)
{
   static DState s;
   static bz_stream strm;
   static UChar len[BZ_MAX_ALPHA_SIZE];
   static UChar bits[65536];
   Int32 tmp[1024], n = 0, nbits = 0, alpha = 0, have_len = 0, pp = 0;
   memset(&s, 0, sizeof s);
   memset(&strm, 0, sizeof strm);
   s.strm = &strm;
   for (int i = 0; i < nl; i++) {
      char *l = lines[i];
      if (l[0] == '#') { printf("%s\n", l); continue; }
      if (!strncmp(l, "len ", 4)) {
         alpha = parse_ints(l + 4, tmp, 1024, 10);
         for (int k = 0; k < alpha; k++) len[k] = (UChar)tmp[k];
         have_len = 1;
         print_arr("len", tmp, alpha);
      } else if (!strncmp(l, "minLen ", 7)) {
         s.minLens[0] = atoi(l + 7); printf("%s\n", l);
      } else if (!strncmp(l, "limit ", 6)) {
         parse_ints(l + 6, s.limit[0], BZ_MAX_ALPHA_SIZE, 10); printf("%s\n", l);
      } else if (!strncmp(l, "base ", 5)) {
         parse_ints(l + 5, s.base[0], BZ_MAX_ALPHA_SIZE, 10); printf("%s\n", l);
      } else if (!strncmp(l, "perm ", 5)) {
         parse_ints(l + 5, s.perm[0], BZ_MAX_ALPHA_SIZE, 10); printf("%s\n", l);
      } else if (!strncmp(l, "bits ", 5)) {
         nbits = parse_ints(l + 5, tmp, 65536, 16);
         for (int k = 0; k < nbits; k++) bits[k] = (UChar)tmp[k];
         printf("%s\n", l);
      } else if (!strncmp(l, "n ", 2)) {
         n = atoi(l + 2); printf("%s\n", l);
      }
   }
   if (have_len) {
      /* decompress.c:339-352 */
      Int32 minLen = 32, maxLen = 0;
      for (int i = 0; i < alpha; i++) {
         if (len[i] > maxLen) maxLen = len[i];
         if (len[i] < minLen) minLen = len[i];
      }
      BZ2_hbCreateDecodeTables(&(s.limit[0][0]), &(s.base[0][0]), &(s.perm[0][0]),
                               len, minLen, maxLen, alpha);
      s.minLens[0] = minLen;
      for (int i = 0; i < alpha; i++) if (len[i] >= minLen && len[i] <= maxLen) pp++;
      printf("minLen %d\n", minLen);
      print_arr("limit", s.limit[0], BZ_MAX_CODE_LEN);
      print_arr("base", s.base[0], BZ_MAX_CODE_LEN);
      print_arr("perm", s.perm[0], pp);
   }
   strm.next_in = (char *)bits;
   strm.avail_in = nbits;
   printf("syms");
   const char *end = "ok";
   long pos = 0;
   for (int k = 0; k < n; k++) {
      Int32 sym = 0;
      Int32 r = get_sym(&s, &sym);
      if (r == SUCCESS) {
         printf(" %d", sym);
         pos = (long)strm.total_in_lo32 * 8 - s.bsLive;
      } else if (r == BZ_OK) { end = "eof"; break; }
      else if (r == BZ_DATA_ERROR) { end = "data"; break; }
      else { end = "other"; break; }
   }
   printf("\npos %ld\nend %s\n\n", pos, end);
}

static void lens(const char *file)
{
   static bz_stream strm;
   static char in[1 << 20], out[1 << 20];
   FILE *f = fopen(file, "rb");
   if (!f) { perror(file); exit(2); }
   size_t got = fread(in, 1, sizeof in, f);
   fclose(f);
   if (BZ2_bzDecompressInit(&strm, 0, 0) != BZ_OK) exit(2);
   strm.next_in = in; strm.avail_in = (unsigned)got;
   int r;
   do {
      strm.next_out = out; strm.avail_out = sizeof out;
      r = BZ2_bzDecompress(&strm);
   } while (r == BZ_OK && strm.avail_in > 0);
   if (r != BZ_STREAM_END) { fprintf(stderr, "%s: not a whole stream (%d)\n", file, r); exit(2); }
   DState *s = strm.state;
   for (int t = 0; t < s->save_nGroups; t++) {
      int alpha = s->save_alphaSize;
      Int32 tmp[BZ_MAX_ALPHA_SIZE];
      for (int i = 0; i < alpha; i++) tmp[i] = s->len[t][i];
      print_arr("len", tmp, alpha);
      printf("rminLen %d\n", s->minLens[t]);
      print_arr("rlimit", s->limit[t], BZ_MAX_CODE_LEN);
      print_arr("rbase", s->base[t], BZ_MAX_CODE_LEN);
      print_arr("rperm", s->perm[t], alpha);
      printf("\n");
   }
}

int main(int argc, char **argv)
{
   if (argc == 3 && !strcmp(argv[1], "lens")) { lens(argv[2]); return 0; }
   if (argc != 2 || strcmp(argv[1], "cases")) { fprintf(stderr, "usage\n"); return 2; }
   static char lines[64][65536];
   int nl = 0;
   while (fgets(lines[nl], sizeof lines[nl], stdin)) {
      lines[nl][strcspn(lines[nl], "\n")] = 0;
      if (lines[nl][0] == 0) { if (nl) run_case(lines, nl); nl = 0; }
      else if (++nl == 64) { fprintf(stderr, "case too long\n"); return 2; }
   }
   if (nl) run_case(lines, nl);
   return 0;
}
