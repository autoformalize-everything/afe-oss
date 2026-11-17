#ifndef BZIP2_ORACLE_H
#define BZIP2_ORACLE_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Other statuses use the BZ_* result codes in bzlib.h:42-55. */
#define BZIP2_ORACLE_UNIMPLEMENTED (-10)

typedef struct {
    uint8_t *data;
    size_t size;
    size_t consumed;
} bzip2_oracle_result;

/* Safe to call repeatedly. The Lean runtime and module initialize once per process. */
int bzip2_oracle_init(void);

/* Calls replace *result. Release any prior buffer before reuse and every successful output. */
int bzip2_oracle_decompress(const uint8_t *input, size_t size,
                            bzip2_oracle_result *result);
int bzip2_oracle_decompress_stream(const uint8_t *input, size_t size,
                                   bzip2_oracle_result *result);
int bzip2_oracle_compress(unsigned level, const uint8_t *input, size_t size,
                          bzip2_oracle_result *result);
void bzip2_oracle_result_free(bzip2_oracle_result *result);

#ifdef __cplusplus
}
#endif

#endif
