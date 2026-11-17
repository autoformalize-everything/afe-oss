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

static void fail(const char *what)
{
    fprintf(stderr, "AFE-FUZZ: %s\n", what);
    abort();
}

static const char *status_name(int status)
{
    switch (status) {
    case BZ_OK: return "BZ_OK";
    case BZ_RUN_OK: return "BZ_RUN_OK";
    case BZ_FLUSH_OK: return "BZ_FLUSH_OK";
    case BZ_FINISH_OK: return "BZ_FINISH_OK";
    case BZ_STREAM_END: return "BZ_STREAM_END";
    case BZ_SEQUENCE_ERROR: return "BZ_SEQUENCE_ERROR";
    case BZ_PARAM_ERROR: return "BZ_PARAM_ERROR";
    case BZ_MEM_ERROR: return "BZ_MEM_ERROR";
    case BZ_DATA_ERROR: return "BZ_DATA_ERROR";
    case BZ_DATA_ERROR_MAGIC: return "BZ_DATA_ERROR_MAGIC";
    case BZ_IO_ERROR: return "BZ_IO_ERROR";
    case BZ_UNEXPECTED_EOF: return "BZ_UNEXPECTED_EOF";
    case BZ_OUTBUFF_FULL: return "BZ_OUTBUFF_FULL";
    case BZ_CONFIG_ERROR: return "BZ_CONFIG_ERROR";
    case BZIP2_ORACLE_UNIMPLEMENTED: return "BZIP2_ORACLE_UNIMPLEMENTED";
    default: return "unknown";
    }
}

static void unexpected_status(int status)
{
    fprintf(stderr, "AFE-FUZZ: unexpected status %s\n", status_name(status));
    abort();
}

/* The input bytes the stream took, by the calls BZ2_bzBuffToBuffDecompress makes. */
static unsigned c_consumed(char *source, unsigned size, unsigned expected_len)
{
    bz_stream strm;
    memset(&strm, 0, sizeof(strm));
    int init = BZ2_bzDecompressInit(&strm, 0, 0);
    if (init != BZ_OK)
        unexpected_status(init);
    strm.next_in = source;
    strm.avail_in = size;
    strm.next_out = output;
    strm.avail_out = OUTPUT_CAP;
    int ret = BZ2_bzDecompress(&strm);
    unsigned avail_in = strm.avail_in;
    unsigned written = OUTPUT_CAP - strm.avail_out;
    BZ2_bzDecompressEnd(&strm);
    if (ret != BZ_STREAM_END)
        unexpected_status(ret);
    if (written != expected_len)
        fail("output length differs");
    return size - avail_in;
}

/*
 * The mutator. A mutation inside a block almost always breaks its CRC, and both sides then
 * say "data", so the bytes of a changed block are seldom compared. After libFuzzer's own
 * mutation, half the time, the mutator therefore rewrites the CRCs of a stream whose first
 * block starts at byte 4: the block CRC (bytes 10-13, compress.c:624-637) becomes the CRC of
 * the bytes libbz2 writes before it fails, which are the first block's when the block CRC
 * was the error (bzlib.c:824-831); the 32 bits after the last end-of-stream magic become the
 * same value, the combined CRC of a one-block stream (bzlib.c:832-835).
 */
size_t LLVMFuzzerMutate(uint8_t *data, size_t size, size_t max_size);

static const uint8_t block_magic[6] = {0x31, 0x41, 0x59, 0x26, 0x53, 0x59};
#define END_MAGIC 0x177245385090ull

static uint32_t crc_of(const char *bytes, unsigned len)
{
    /* CRC-32, polynomial 0x04c11db7, most significant bit first (bzlib_private.h:157-172). */
    uint32_t crc = 0xffffffffu;
    for (unsigned i = 0; i < len; i++) {
        crc ^= (uint32_t)(uint8_t)bytes[i] << 24;
        for (int k = 0; k < 8; k++)
            crc = (crc & 0x80000000u) ? (crc << 1) ^ 0x04c11db7u : crc << 1;
    }
    return ~crc;
}

static int get_bit(const uint8_t *data, size_t bit)
{
    return (data[bit / 8] >> (7 - bit % 8)) & 1;
}

static void put_bits32(uint8_t *data, size_t bit, uint32_t value)
{
    for (int k = 0; k < 32; k++, bit++) {
        uint8_t mask = (uint8_t)(0x80 >> (bit % 8));
        if ((value >> (31 - k)) & 1)
            data[bit / 8] |= mask;
        else
            data[bit / 8] &= (uint8_t)~mask;
    }
}

static void fix_crcs(uint8_t *data, size_t size)
{
    if (size < 14 + 10 || size > UINT_MAX || memcmp(data, "BZh", 3) != 0 ||
        data[3] < '1' || data[3] > '9' || memcmp(data + 4, block_magic, 6) != 0)
        return;
    bz_stream strm;
    memset(&strm, 0, sizeof(strm));
    if (BZ2_bzDecompressInit(&strm, 0, 0) != BZ_OK)
        return;
    strm.next_in = (char *)data;
    strm.avail_in = (unsigned)size;
    strm.next_out = output;
    strm.avail_out = OUTPUT_CAP;
    BZ2_bzDecompress(&strm);
    unsigned written = OUTPUT_CAP - strm.avail_out;
    BZ2_bzDecompressEnd(&strm);
    uint32_t crc = crc_of(output, written);
    for (int k = 0; k < 4; k++)
        data[10 + k] = (uint8_t)(crc >> (24 - 8 * k));
    /* The last 48-bit end-of-stream magic with 32 bits after it, at any bit offset. */
    uint64_t window = 0;
    size_t last = 0;
    for (size_t bit = 0; bit + 32 < size * 8; bit++) {
        window = ((window << 1) | (uint64_t)get_bit(data, bit)) & 0xffffffffffffull;
        if (bit >= 47 && window == END_MAGIC)
            last = bit + 1;
    }
    if (last != 0)
        put_bits32(data, last, crc);
}

size_t LLVMFuzzerCustomMutator(uint8_t *data, size_t size, size_t max_size, unsigned seed)
{
    size = LLVMFuzzerMutate(data, size, max_size);
    if (seed % 2 == 0)
        fix_crcs(data, size);
    return size;
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
        unexpected_status(c_status);

    bzip2_oracle_result result = {0};
    int oracle_status = bzip2_oracle_decompress_stream(data, size, &result);
    if (verdict(oracle_status) == NULL)
        unexpected_status(oracle_status);
    if (oracle_status != c_status) {
        fprintf(stderr, "AFE-FUZZ: verdict libbz2=%s oracle=%s\n",
                verdict(c_status), verdict(oracle_status));
        abort();
    }

    if (c_status == BZ_OK) {
        if (result.size != c_len)
            fail("output length differs");
        if (c_len != 0 && memcmp(output, result.data, c_len) != 0)
            fail("output differs");
        unsigned consumed = c_consumed(source, (unsigned)size, c_len);
        if (result.consumed != consumed)
            fail("consumed differs");
    }
    bzip2_oracle_result_free(&result);
    free(source);
    return 0;
}
