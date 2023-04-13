#pragma once

#include "bike_defs.h"
#include "decode_internals.h"
#include <stdint.h>

// Please notice that the 3 definitions bellow are defined just to allow
// for a cleaner code. THEY MUST NOT BE CHANGED!
#define COUNTING_SORT_BUCKETS            8
#define COUNTING_SORT_AVX512_VECTOR_SIZE 32 // = 512/16
#define COUNTING_LEVELS                  3
///////////////////////////////////////////////////////////////////////////////

// USE_UNSAFE_CODE_FOR_EXTRAPOLATION should NOT be defined in production code.
// That is, you should define USE_RANDOMIZED_SELECTION_OF_EQ_THRESHOLD_BITS
// except when testing for extrapolation purposes.
#ifndef USE_UNSAFE_CODE_FOR_EXTRAPOLATION
    #define USE_RANDOMIZED_SELECTION_OF_EQ_THRESHOLD_BITS
#endif

// Notice that this function is significantly different from LOG2_MSB from
// BIKE's Additional Implementation.
#define LOG2(v)                                                      \
    ((v) <= 1                                                        \
         ? 0                                                         \
         : ((v) <= 2                                                 \
                ? 1                                                  \
                : ((v) <= 4                                          \
                       ? 2                                           \
                       : ((v) <= 8                                   \
                              ? 3                                    \
                              : ((v) <= 16                           \
                                     ? 4                             \
                                     : ((v) <= 32                    \
                                            ? 5                      \
                                            : ((v) <= 64             \
                                                   ? 6               \
                                                   : ((v) <= 128 ? 7 \
                                                                 : ((v) <= 256 ? 8 : 9)))))))))

// The value of FIXFLIP_HEAD_N_FLIPS for each security level.
// This is the value of n_flips that is used in the first iteration of FixFlip.
#if (LEVEL == 1)
#    define FIXFLIP_HEAD_N_FLIPS 55
#    define FIND_X_COUNT 110
#elif (LEVEL == 3)
#    define FIXFLIP_HEAD_N_FLIPS 65
#    define FIND_X_COUNT 130
#elif (LEVEL == 5)
#    define FIXFLIP_HEAD_N_FLIPS 100
#    define FIND_X_COUNT 200
#else
#    error
#endif


typedef struct fixflip_threshold_s {
    uint8_t threshold;
    uint8_t n_equal_threshold;
    uint32_t total_equal_threshold;
} fixflip_threshold_t;

ALIGN(64) typedef struct fixflip_upc_s { uint8_t blocks[N0][R_QW * 64]; } fixflip_upc_t;

ret_t
decode_pickyfix(OUT split_e_t *e,
                IN const syndrome_t *original_s,
                IN const ct_t *ct,
                IN const sk_t *sk);

ret_t
fixflip_iter(OUT split_e_t *e,
             OUT syndrome_t *  syndrome,
             IN const uint32_t n_flips,
             IN const ct_t *ct,
             IN const sk_t *sk);

ret_t
pickyflip_iter(OUT split_e_t *e,
               IN OUT syndrome_t *  syndrome,
               IN const uint8_t threshold_in,
               IN const uint8_t threshold_out,
               IN const ct_t *ct,
               IN const sk_t *sk);

uint32_t
flip_worst_fit_indexes(OUT split_e_t *e, IN fixflip_upc_t *ff_upc, IN uint32_t n);

void
get_upc(OUT fixflip_upc_t *ff_upc,
        IN const syndrome_t *           syndrome,
        IN const compressed_idx_dv_ar_t wlist);

ret_t
get_separate_counters(OUT int counters_right[],
                      OUT int counters_wrong[],
                      IN split_e_t *true_error,
                      IN const syndrome_t *original_s,
                      IN const sk_t *sk);

_INLINE_ uint8_t
upc_for_index(fixflip_upc_t *ff_upc, uint32_t index) {
    return ff_upc->blocks[index / R_BITS][index % R_BITS];
}

_INLINE_ void
decompress_e(OUT uint8_t e_decomp[], IN split_e_t *e) {
    for (uint32_t i = 0; i < N0; i++) {
        for (uint32_t j = 0; j < R_SIZE; j++) {
            size_t nblocks = j < (R_SIZE - 1) ? 8 : R_BITS % 8;
            for (uint32_t k = 0; k < nblocks; k++) {
                e_decomp[i * R_BITS + j * 8 + k] = (e->val[i].raw[j] >> k) % 2;
            }
        }
    }
}

_INLINE_ void
compress_e(OUT split_e_t *e, IN uint8_t e_decomp[]) {
    for (uint32_t i = 0; i < N0; i++) {
        for (uint32_t j = 0; j < R_SIZE; j++) {
            e->val[i].raw[j] = 0;

            size_t nblocks = j < (R_SIZE - 1) ? 8 : R_BITS % 8;
            for (uint32_t k = 0; k < nblocks; k++) {
                e->val[i].raw[j] |= (e_decomp[i * R_BITS + j * 8 + k] << k);
            }
        }
    }
}

void
reduce_upcs_then_count(OUT uint8_t *sc,
                       IN fixflip_upc_t *ff_upc,
                       IN uint32_t       base,
                       IN uint32_t       step);

void
get_fixflip_threshold(OUT fixflip_threshold_t *ff_threshold,
                      IN fixflip_upc_t *ff_upc,
                      IN uint32_t       n_flips);


#ifdef USE_RANDOMIZED_SELECTION_OF_EQ_THRESHOLD_BITS

#if (LEVEL == 1)

#define N_FLIP_FLAGS_BLOCKS 3 // ceil(146 / 64)
#define N_RANDOM_BITS_FOR_FISHER_YATES 128

#elif (LEVEL == 3)

#define N_FLIP_FLAGS_BLOCKS 4 // ceil(206 / 64)
#define N_RANDOM_BITS_FOR_FISHER_YATES 192

#elif (LEVEL == 5)

#define N_FLIP_FLAGS_BLOCKS 5 // ceil(260 / 64)
#define N_RANDOM_BITS_FOR_FISHER_YATES 256

#if N_FLIP_FLAGS_BLOCKS > 4
uint32_t compute_total_equal_threshold(fixflip_upc_t *ff_upc, uint8_t threshold);
#endif

#else
#    error
#endif



#define N_32_BIT_BLOCKS_FOR_RANDOM_BITS_FOR_FISHER_YATES (N_RANDOM_BITS_FOR_FISHER_YATES / 32)

void
init_eq_flip_flags(OUT uint64_t eq_flip_flags[N_FLIP_FLAGS_BLOCKS],
                       IN fixflip_threshold_t *ff_threshold);

void
secure_shuffle_eq_flip_flags(OUT uint64_t eq_flip_flags[N_FLIP_FLAGS_BLOCKS],
                             IN fixflip_threshold_t *ff_threshold,
                             IN uint32_t total_upc_counters_eq_threshold);


#endif