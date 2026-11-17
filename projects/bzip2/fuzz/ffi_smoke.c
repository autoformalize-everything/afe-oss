#include "ffi/bzip2_oracle.h"

#include <bzlib.h>
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int check(int status, const bzip2_oracle_result *result)
{
    if (status == BZIP2_ORACLE_UNIMPLEMENTED)
        return result->data == NULL && result->size == 0 && result->consumed == 0;
    return status == BZ_OK && result->data != NULL;
}

int main(void)
{
    /* A valid empty stream, used by both decompress entry points. */
    static const uint8_t empty_stream[] = {
        0x42, 0x5a, 0x68, 0x39, 0x17, 0x72, 0x45, 0x38,
        0x50, 0x90, 0x00, 0x00, 0x00, 0x00
    };
    bzip2_oracle_result result = {0};
    char stream_copy[sizeof(empty_stream)];
    char decoded[1];
    unsigned decoded_size = sizeof(decoded);
    memcpy(stream_copy, empty_stream, sizeof(empty_stream));

    if (BZ2_bzlibVersion() == NULL || bzip2_oracle_init() != BZ_OK ||
        bzip2_oracle_init() != BZ_OK ||
        BZ2_bzBuffToBuffDecompress(decoded, &decoded_size, stream_copy,
                                    sizeof(stream_copy), 0, 0) != BZ_OK || decoded_size != 0)
        return 1;

    int status = bzip2_oracle_decompress(empty_stream, sizeof(empty_stream), &result);
    if (!check(status, &result))
        return 2;
    bzip2_oracle_result_free(&result);

    status = bzip2_oracle_decompress_stream(empty_stream, sizeof(empty_stream), &result);
    if (!check(status, &result) ||
        (status == BZ_OK && result.consumed != sizeof(empty_stream)))
        return 3;
    bzip2_oracle_result_free(&result);

    status = bzip2_oracle_compress(9, NULL, 0, &result);
    if (!check(status, &result))
        return 4;
    bzip2_oracle_result_free(&result);

    lean_finalize_task_manager();
    puts("ffi_smoke: ok");
    return 0;
}
