#include "bzip2_oracle.h"

#include <lean/lean.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>

#include "bzlib.h"

/* These signatures are generated from Bzip2.Ffi.Oracle's @[export] declarations. */
extern lean_object *initialize_bzip2_Bzip2_Ffi_Oracle(uint8_t builtin);
extern lean_object *bzip2_oracle_lean_decompress(lean_object *input);
extern lean_object *bzip2_oracle_lean_decompress_stream(lean_object *input);
extern lean_object *bzip2_oracle_lean_compress(uint32_t level, lean_object *input);

/* Lean's module initialization retains global GMP constants for the process lifetime. */
extern void __lsan_disable(void) __attribute__((weak));
extern void __lsan_enable(void) __attribute__((weak));

static pthread_once_t init_once = PTHREAD_ONCE_INIT;
static int init_status = BZ_CONFIG_ERROR;

static void initialize(void)
{
    if (__lsan_disable != NULL)
        __lsan_disable();
    lean_object *res = initialize_bzip2_Bzip2_Ffi_Oracle(1);
    if (__lsan_enable != NULL)
        __lsan_enable();
    if (lean_io_result_is_error(res)) {
        lean_dec(res);
        return;
    }
    lean_dec(res);
    lean_io_mark_end_initialization();
    lean_init_task_manager();
    init_status = BZ_OK;
}

int bzip2_oracle_init(void)
{
    if (pthread_once(&init_once, initialize) != 0)
        return BZ_CONFIG_ERROR;
    return init_status;
}

void bzip2_oracle_result_free(bzip2_oracle_result *result)
{
    if (result == NULL)
        return;
    free(result->data);
    result->data = NULL;
    result->size = 0;
    result->consumed = 0;
}

static int prepare(const uint8_t *input, size_t size, bzip2_oracle_result *result,
                   lean_object **bytes)
{
    if (result == NULL)
        return BZ_PARAM_ERROR;
    *result = (bzip2_oracle_result){0};
    if (input == NULL && size != 0)
        return BZ_PARAM_ERROR;
    int status = bzip2_oracle_init();
    if (status != BZ_OK)
        return status;
    *bytes = lean_alloc_sarray(1, size, size);
    if (size != 0)
        memcpy(lean_sarray_cptr(*bytes), input, size);
    return BZ_OK;
}

static int finish(lean_object *value, bzip2_oracle_result *result)
{
    /* Result has one object field, then UInt64 and Int32 scalar fields. */
    int32_t status = (int32_t)lean_ctor_get_uint32(value, sizeof(void *) + 8);
    if (status == BZ_OK) {
        lean_object *output = lean_ctor_get(value, 0);
        size_t size = lean_sarray_size(output);
        uint64_t consumed64 = lean_ctor_get_uint64(value, sizeof(void *));
        size_t consumed = (size_t)consumed64;
        if ((uint64_t)consumed != consumed64) {
            lean_dec(value);
            return BZ_PARAM_ERROR;
        }
        uint8_t *data = malloc(size == 0 ? 1 : size);
        if (data == NULL) {
            lean_dec(value);
            return BZ_MEM_ERROR;
        }
        if (size != 0)
            memcpy(data, lean_sarray_cptr(output), size);
        result->data = data;
        result->size = size;
        result->consumed = consumed;
    }
    lean_dec(value);
    return status;
}

int bzip2_oracle_decompress(const uint8_t *input, size_t size,
                            bzip2_oracle_result *result)
{
    lean_object *bytes;
    int status = prepare(input, size, result, &bytes);
    if (status != BZ_OK)
        return status;
    return finish(bzip2_oracle_lean_decompress(bytes), result);
}

int bzip2_oracle_decompress_stream(const uint8_t *input, size_t size,
                                   bzip2_oracle_result *result)
{
    lean_object *bytes;
    int status = prepare(input, size, result, &bytes);
    if (status != BZ_OK)
        return status;
    return finish(bzip2_oracle_lean_decompress_stream(bytes), result);
}

int bzip2_oracle_compress(unsigned level, const uint8_t *input, size_t size,
                          bzip2_oracle_result *result)
{
    /* BZ2_bzBuffToBuffCompress rejects levels outside 1..9 (bzlib.c:1262-1267). */
    if (level < 1 || level > 9) {
        if (result != NULL)
            *result = (bzip2_oracle_result){0};
        return BZ_PARAM_ERROR;
    }
    lean_object *bytes;
    int status = prepare(input, size, result, &bytes);
    if (status != BZ_OK)
        return status;
    return finish(bzip2_oracle_lean_compress(level, bytes), result);
}
