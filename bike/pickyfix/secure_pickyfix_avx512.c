#include "decode.h"
#include "gf2x.h"
#include "utilities.h"
#include <assert.h>
#include <immintrin.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "decode_internals.h"
#include "pickyfix.h"

__m512i
get_last_mask(uint32_t n) {
    uint32_t           tgt_mask = n % (COUNTING_SORT_AVX512_VECTOR_SIZE * 2);
    ALIGN(64) uint16_t mask_vec[COUNTING_SORT_AVX512_VECTOR_SIZE] = {0};
    for (uint32_t i = 0; i < tgt_mask; i++) {
        if (i % 2 == 0)
            mask_vec[i / 2] |= 0x00FF;
        else
            mask_vec[i / 2] |= 0xFF00;
    }

    return _mm512_load_si512((__m512i *)(mask_vec));
}

void
print_m512i_as_i16(__m512i v) {
    ALIGN(64) uint16_t output[32];
    _mm512_store_si512((__m512i *)output, v);

    for (int i = 0; i < 32; i++) {
        printf("%04x ", output[i]);
    }
    printf("\n");
}

void
get_upc(OUT fixflip_upc_t *ff_upc,
        IN const syndrome_t *           syndrome,
        IN const compressed_idx_dv_ar_t wlist) {
    DEFER_CLEANUP(syndrome_t rotated_syndrome = {0}, syndrome_cleanup);

    for (uint32_t i = 0; i < N0; i++) {

        for (size_t j = 0; j < DV; j++) {
            rotate_right(&rotated_syndrome, syndrome, wlist[i].val[j]);
            for (int k = 0; k < R_QW; k++) {
                __m512i current   = _mm512_loadu_epi8(&ff_upc->blocks[i][k * 64]);
                __m512i synd_bits = _mm512_maskz_set1_epi8(rotated_syndrome.qw[k], 0x01);
                current           = _mm512_add_epi8(current, synd_bits);
                _mm512_storeu_epi8(&ff_upc->blocks[i][k * 64], current);
            }
        }
    }
}

void
print_m512i_as_i8(__m512i v) {
    ALIGN(64) uint8_t output[512 / 8];
    _mm512_store_si512((__m512i *)output, v);

    for (uint32_t i = 0; i < 512 / 8; i++) {
        printf("%02x", output[i]);
    }
    printf("\n");
}

_INLINE_ __m512i
get_reduced_counters_avx512(IN fixflip_upc_t *ff_upc,
                            IN __m512i        base_min,
                            IN __m512i        base_max,
                            IN __m512i        shift_mask,
                            IN uint32_t       n_right_shift,
                            IN uint32_t       i,
                            IN uint32_t       j) {
    __m512i out = _mm512_load_si512((__m512i *)(&ff_upc->blocks[i][j * 64]));

    uint64_t under_min  = _mm512_cmp_epu8_mask(out, base_min, 1); // 1 = LT
    uint64_t over_max   = _mm512_cmp_epu8_mask(base_max, out, 1); // 1 = LT
    uint64_t out_bounds = under_min | over_max;

    out = _mm512_subs_epu8(out, base_min);
    out = _mm512_srli_epi16(out, n_right_shift);
    out = _mm512_and_si512(out, shift_mask);

    out = _mm512_mask_set1_epi8(out, out_bounds, -1);

    return out;
}

_INLINE_ __m512i
get_zipped_shifts(__m512i reduced_counters) {
    __m512i x      = _mm512_mask_set1_epi8(reduced_counters, 0xAAAAAAAAAAAAAAAA, 0x00);
    __m512i ones1  = _mm512_set1_epi16(1);
    __m512i shift1 = _mm512_sllv_epi16(ones1, x);

    __m512i x2 = _mm512_mask_set1_epi8(reduced_counters, 0x5555555555555555, 0x00);
    x2         = _mm512_srli_epi16(x2, 8);

    __m512i ones2  = _mm512_set1_epi16(1 << 8);
    __m512i shift2 = _mm512_sllv_epi16(ones2, x2);

    return _mm512_xor_si512(shift1, shift2);
}

/* Performs a partial counting sort, over values in ff_upc and stores the
 * sorting counters in counts. The resolution of the counting sort is given
 * by parameter n_counting_step, where n_counting_step = 0 is equal to the
 * lowest resolution.
 */
void
reduce_upcs_then_count(OUT uint8_t *counts,
                       IN fixflip_upc_t *ff_upc,
                       IN uint32_t       base,
                       IN uint32_t       step) {

    __m512i base_min = _mm512_set1_epi8(base);
    __m512i base_max = _mm512_set1_epi8(min32(base + step * 8 - 1, 0xFF));

    // uint8_t n_right_shift = (LOG8 * (N_SORTS - n_counting_step - 1));
    uint8_t n_right_shift = LOG2(step);

    __m512i shift_mask = _mm512_set1_epi8(0xFF >> n_right_shift);

    __m512i bucket_shares = _mm512_set1_epi8(0);
    __m512i max_counters  = _mm512_set1_epi8(-1);

    // The two following loops are responsible for reducing the UPC counter and
    // counting it simultaneously.
    for (uint32_t i = 0; i < N0; i++) {
        for (uint32_t j = 0; j < R_QW; j++) {

            __m512i reduced_counters = get_reduced_counters_avx512(
                ff_upc, base_min, base_max, shift_mask, n_right_shift, i, j);
            __m512i shift = get_zipped_shifts(reduced_counters);

            // Masks the padding in the last block, if this is the case:
            if (j == R_QW - 1) {
                shift = _mm512_and_si512(shift, get_last_mask(R_BITS));
            }

            ALIGN(64) uint64_t shifts_array[8] = {0};
            _mm512_store_si512((__m512i *)shifts_array, shift);

            for (uint32_t k = 0; k < 8; k++) {
                __m512i  counter_shares = _mm512_maskz_set1_epi8(shifts_array[k], 0x01);
                uint64_t notmax_mask    = _mm512_cmpneq_epi8_mask(bucket_shares, max_counters);
                bucket_shares =
                    _mm512_mask_add_epi8(max_counters, notmax_mask, bucket_shares, counter_shares);
            }
        }
    }
    ALIGN(64) uint8_t bucket_shares_array[64] = {0};
    _mm512_store_si512((__m512i *)bucket_shares_array, bucket_shares);

    for (int i = 0; i < 64; i++) {
        counts[i % 8] = min32((uint32_t)counts[i % 8] + bucket_shares_array[i], 0xFF);
    }
}

_INLINE_ void
flip_e(uint8_t *v, uint64_t flip_mask) {
    v[0] ^= flip_mask >> 0;
    v[1] ^= flip_mask >> 8;
    v[2] ^= flip_mask >> 16;
    v[3] ^= flip_mask >> 24;
    v[4] ^= flip_mask >> 32;
    v[5] ^= flip_mask >> 40;
    v[6] ^= flip_mask >> 48;
    v[7] ^= flip_mask >> 56;
}

_INLINE_ uint64_t
get_eq_threshold_flip_mask(OUT uint32_t *out_weight, IN uint64_t eq_mask, IN uint32_t max_weight) {
    uint32_t total_weight = 0;
    __m512i  ones         = _mm512_set1_epi32(0xFFFF);

    uint64_t flip_mask = 0;
    for (uint32_t i = 0; i < 4; i++) {
        uint16_t value = eq_mask >> (i * 16);

        uint32_t weight = __builtin_popcount(value);

        uint32_t lt_mask       = ~secure_l32_mask(max_weight, total_weight + weight);
        uint32_t target_weight = (weight & ~lt_mask) | ((max_weight - total_weight) & lt_mask);

        total_weight += target_weight;

        __m512i supp     = _mm512_maskz_set1_epi32(0xFFFF >> (16 - target_weight), 0xFFFF);
        __m512i exp_supp = _mm512_maskz_expand_epi32(value, supp);
        uint16_t new     = _mm512_mask_cmp_epi32_mask(value, exp_supp, ones, 0);

        flip_mask |= ((uint64_t) new) << (i * 16);
    }
    *out_weight = total_weight;
    return flip_mask;
}


#ifdef USE_RANDOMIZED_SELECTION_OF_EQ_THRESHOLD_BITS

uint64_t
get_randomized_eq_flip_mask(uint64_t eq_flip_flags[N_FLIP_FLAGS_BLOCKS],
                            uint32_t *current_eq_weight,
                            uint64_t eq_threshold_mask) {

    // We start by building the compressed vector of shuffled flipping flags
    // corresponding to the current_eq_weight.

    uint64_t output = 0;
    uint32_t factor = 0;

    __m512i ones  = _mm512_set1_epi32(1);

    for (int i = 0; i < 4; i++) {
        uint16_t next_16_flags = 0;

        uint32_t flip_block = *current_eq_weight >> 6; // Division by 64.
        uint32_t flip_offset = *current_eq_weight - flip_block*64;

        for (uint32_t k = 0; k < N_FLIP_FLAGS_BLOCKS; k++) {

            uint64_t tmp_next_64_flags = eq_flip_flags[k] >> flip_offset;

            // We don't need to hide k!
            if (k < N_FLIP_FLAGS_BLOCKS - 1) {
                tmp_next_64_flags |= eq_flip_flags[k + 1] << (64 - flip_offset);
            }

            // Use condition mask to update next_16_flags if we are in the right block.
            uint16_t right_block_mask = -secure_cmp32(flip_block, k);
            next_16_flags = (tmp_next_64_flags & right_block_mask) | (next_16_flags & ~right_block_mask);
        }

        __m512i next_16_flags_as_32pack = _mm512_maskz_set1_epi32(next_16_flags, 1);

        uint16_t eq_threshold_mask_part = eq_threshold_mask >> factor;
        uint32_t weight = __builtin_popcountl(eq_threshold_mask_part);

        __m512i e = _mm512_maskz_expand_epi32(eq_threshold_mask_part, next_16_flags_as_32pack);

        uint64_t partial_out = _mm512_cmp_epi32_mask(ones, e, 0);

        *current_eq_weight += weight;
        output |= partial_out << factor;

        factor += 16;
    }

    return output;
}

uint32_t
flip_worst_fit_indexes(OUT split_e_t *e, IN fixflip_upc_t *ff_upc, IN uint32_t n) {
    fixflip_threshold_t ff_threshold = {0};

    get_fixflip_threshold(&ff_threshold, ff_upc, n);

    __m512i threshold512 = _mm512_set1_epi8(ff_threshold.threshold);

    uint32_t current_eq_weight = 0;
    uint32_t total_eq_weight = 0;
    uint32_t total_gt_weight = 0;

    uint32_t total_upc_counters_eq_threshold = ff_threshold.total_equal_threshold;

    uint64_t eq_flip_flags[N_FLIP_FLAGS_BLOCKS] = {0};
    init_eq_flip_flags(eq_flip_flags, &ff_threshold);
    secure_shuffle_eq_flip_flags(eq_flip_flags, &ff_threshold, total_upc_counters_eq_threshold);

    for (uint32_t i = 0; i < N0; i++) {
        for (uint32_t j = 0; j < R_QW; j++) {
            uint8_t *e_part = &(e->val[i].raw[j * 8]);

            __m512i counters = _mm512_load_si512((__m512i *)(&ff_upc->blocks[i][j * 64]));

            uint64_t last_mask = j == (R_QW - 1) ? LAST_R_QW_MASK : 0xFFFFFFFFFFFFFFFF;

            uint64_t gt_threshold = _mm512_cmp_epu8_mask(threshold512, counters, 1); // 1 = LT
            uint64_t eq_threshold = _mm512_cmp_epu8_mask(threshold512, counters, 0); // 0 = EQ

            gt_threshold &= last_mask;
            eq_threshold &= last_mask;


            uint64_t eq_flip_mask = get_randomized_eq_flip_mask(eq_flip_flags,
                                                                &current_eq_weight,
                                                                eq_threshold);

            total_gt_weight += __builtin_popcountl(gt_threshold);
            total_eq_weight += __builtin_popcountl(eq_flip_mask);

            assert((gt_threshold & eq_flip_mask) == 0);

            flip_e(e_part, gt_threshold | eq_flip_mask);

        }
    }
    assert(total_eq_weight == ff_threshold.n_equal_threshold);
    assert(total_gt_weight + total_eq_weight == n);

    return ff_threshold.threshold;
}

#if (N_FLIP_FLAGS_BLOCKS > 4)

uint32_t compute_total_equal_threshold(fixflip_upc_t *ff_upc, uint8_t threshold) {

    __m512i threshold512 = _mm512_set1_epi8(threshold);

    uint32_t total_eq_weight = 0;
    for (uint32_t i = 0; i < N0; i++) {
        for (uint32_t j = 0; j < R_QW; j++) {
            __m512i counters = _mm512_load_si512((__m512i *)(&ff_upc->blocks[i][j * 64]));
            uint64_t eq_threshold = _mm512_cmp_epu8_mask(threshold512, counters, 0); // 0 = EQ

            uint64_t last_mask = j == (R_QW - 1) ? LAST_R_QW_MASK : 0xFFFFFFFFFFFFFFFF;
            eq_threshold &= last_mask;

            total_eq_weight += __builtin_popcountl(eq_threshold);
        }
    }
    return total_eq_weight;

}
#endif

#else

uint32_t
flip_worst_fit_indexes(OUT split_e_t *e, IN fixflip_upc_t *ff_upc, IN uint32_t n) {
    fixflip_threshold_t ff_threshold = {0};

    get_fixflip_threshold(&ff_threshold, ff_upc, n);

    __m512i threshold512 = _mm512_set1_epi8(ff_threshold.threshold);

    uint32_t total_eq_weight = 0;
    uint32_t total_gt_weight = 0;

    for (uint32_t i = 0; i < N0; i++) {
        for (uint32_t j = 0; j < R_QW; j++) {
            uint8_t *e_part = &(e->val[i].raw[j * 8]);

            __m512i counters = _mm512_load_si512((__m512i *)(&ff_upc->blocks[i][j * 64]));

            uint64_t last_mask = j == (R_QW - 1) ? LAST_R_QW_MASK : 0xFFFFFFFFFFFFFFFF;

            uint64_t gt_threshold = _mm512_cmp_epu8_mask(threshold512, counters, 1); // 1 = LT
            uint64_t eq_threshold = _mm512_cmp_epu8_mask(threshold512, counters, 0); // 0 = EQ

            gt_threshold &= last_mask;
            eq_threshold &= last_mask;

            uint32_t lt_mask = secure_l32_mask(ff_threshold.n_equal_threshold, total_eq_weight);
            uint32_t max_eq_weight = (ff_threshold.n_equal_threshold - total_eq_weight) & lt_mask;

            uint32_t eq_weight = 0;
            uint64_t eq_flip_mask =
                get_eq_threshold_flip_mask(&eq_weight, eq_threshold, max_eq_weight);

            total_eq_weight += eq_weight;
            total_gt_weight += __builtin_popcountl(gt_threshold);

            assert((gt_threshold & eq_flip_mask) == 0);

            flip_e(e_part, gt_threshold | eq_flip_mask);

        }
    }
    assert(total_eq_weight == ff_threshold.n_equal_threshold);
    assert(total_gt_weight + total_eq_weight == n);

    return ff_threshold.threshold;
}

#endif
