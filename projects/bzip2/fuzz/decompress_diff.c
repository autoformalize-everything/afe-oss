/*
 * Differential decompression: libbz2 against the Lean oracle, one stream.
 *
 * The C side is BZ2_bzBuffToBuffDecompress (bzlib.c:1302-1351), small = 0, into a 16 MiB
 * buffer. It decodes the first stream of the input and ignores what follows
 * (bzlib.c:1330-1337). The oracle side is Bzip2.Oracle.decompressStream through the FFI
 * (ffi/bzip2_oracle.h). The harness aborts unless both give the same verdict:
 *
 *   ok     BZ_OK                (BZ_STREAM_END from BZ2_bzDecompress, bzlib.c:1332-1337)
 *   magic  BZ_DATA_ERROR_MAGIC  (a bad stream header, decompress.c:197-208)
 *   data   BZ_DATA_ERROR        (anything else corrupt, block and combined CRCs included)
 *   eof    BZ_UNEXPECTED_EOF    (BZ_OK with output space left, bzlib.c:1339-1342)
 *
 * and, on ok, the same bytes and the same number of input bytes consumed.
 *
 * BZ_OUTBUFF_FULL (bzlib.c:1343-1345), the 16 MiB filled, is skipped: the oracle has no
 * output limit, so there is nothing to compare. Any other C status, or an oracle status
 * outside the four verdicts (BZ_PARAM_ERROR, BZIP2_ORACLE_UNIMPLEMENTED), aborts.
 *
 * BZ2_bzBuffToBuffDecompress does not report how much input it read, so for an ok input the
 * harness repeats its calls (bzlib.c:1319-1330) on a bz_stream of its own and takes the
 * input size less the avail_in that BZ2_bzDecompress leaves; it checks that this second run
 * also ends the stream with the same output length.
 */
#include "bzip2_oracle.h"

#include <bzlib.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define OUTPUT_CAP (16u << 20)

static char *output;

int LLVMFuzzerInitialize(int *argc, char ***argv)
{
    (void)argc;
    (void)argv;
    output = malloc(OUTPUT_CAP);
    if (output == NULL || bzip2_oracle_init() != BZ_OK) {
        fprintf(stderr, "decompress_diff: initialisation failed\n");
        abort();
    }
    return 0;
}

static const char *verdict(int status)
{
    switch (status) {
    case BZ_OK: return "ok";
    case BZ_DATA_ERROR_MAGIC: return "magic";
    case BZ_DATA_ERROR: return "data";
    case BZ_UNEXPECTED_EOF: return "eof";
    default: return NULL;
    }
}

static void fail(const char *what, int c_status, int oracle_status)
{
    fprintf(stderr, "decompress_diff: %s (libbz2 %d, oracle %d)\n",
            what, c_status, oracle_status);
    abort();
}

/* The input bytes the stream took, by the calls BZ2_bzBuffToBuffDecompress makes. */
static unsigned c_consumed(char *source, unsigned size, unsigned expected_len)
{
    bz_stream strm;
    memset(&strm, 0, sizeof(strm));
    if (BZ2_bzDecompressInit(&strm, 0, 0) != BZ_OK)
        fail("BZ2_bzDecompressInit failed", BZ_OK, BZ_OK);
    strm.next_in = source;
    strm.avail_in = size;
    strm.next_out = output;
    strm.avail_out = OUTPUT_CAP;
    int ret = BZ2_bzDecompress(&strm);
    unsigned avail_in = strm.avail_in;
    unsigned written = OUTPUT_CAP - strm.avail_out;
    BZ2_bzDecompressEnd(&strm);
    if (ret != BZ_STREAM_END || written != expected_len)
        fail("BZ2_bzDecompress disagrees with BZ2_bzBuffToBuffDecompress", ret, BZ_OK);
    return size - avail_in;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
    if (size > UINT_MAX)
        return 0;
    /* BZ2_bzBuffToBuffDecompress takes a mutable, non-NULL source (bzlib.c:1313-1317). */
    char *source = malloc(size == 0 ? 1 : size);
    if (source == NULL)
        abort();
    if (size != 0)
        memcpy(source, data, size);

    unsigned c_len = OUTPUT_CAP;
    int c_status = BZ2_bzBuffToBuffDecompress(output, &c_len, source, (unsigned)size, 0, 0);
    if (c_status == BZ_OUTBUFF_FULL) {
        free(source);
        return -1; /* skipped: libFuzzer does not add it to the corpus */
    }
    if (verdict(c_status) == NULL)
        fail("unexpected libbz2 status", c_status, 0);

    bzip2_oracle_result result = {0};
    int oracle_status = bzip2_oracle_decompress_stream(data, size, &result);
    if (verdict(oracle_status) == NULL)
        fail("unexpected oracle status", c_status, oracle_status);
    if (oracle_status != c_status) {
        fprintf(stderr, "decompress_diff: libbz2 says %s, oracle says %s\n",
                verdict(c_status), verdict(oracle_status));
        fail("verdicts differ", c_status, oracle_status);
    }

    if (c_status == BZ_OK) {
        if (result.size != c_len) {
            fprintf(stderr, "decompress_diff: libbz2 gives %u bytes, oracle %zu\n",
                    c_len, result.size);
            fail("output lengths differ", c_status, oracle_status);
        }
        if (c_len != 0 && memcmp(output, result.data, c_len) != 0) {
            size_t i = 0;
            while (output[i] == (char)result.data[i])
                i++;
            fprintf(stderr, "decompress_diff: outputs first differ at byte %zu\n", i);
            fail("outputs differ", c_status, oracle_status);
        }
        unsigned consumed = c_consumed(source, (unsigned)size, c_len);
        if (result.consumed != consumed) {
            fprintf(stderr, "decompress_diff: libbz2 consumed %u bytes, oracle %zu\n",
                    consumed, result.consumed);
            fail("consumed input lengths differ", c_status, oracle_status);
        }
    }
    bzip2_oracle_result_free(&result);
    free(source);
    return 0;
}
