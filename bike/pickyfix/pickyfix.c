// File fixlip.c
// -------------
//
// Author: Anonymized for CHES submission
//
// This file contains the entry point for our contribution: FixFlip a new decoding algorithm
// for BIKE.
//

#include "decode.h"
#include "utilities.h"
#include <assert.h>
#include <m4ri/m4ri.h>
#include <stdlib.h>
#include <string.h>

#include "decode_internals.h"
#include "pickyfix.h"

#define BLOCK      64
#define GUSS_BLOCK 8
#define EQ_COLUMN  21

// 使用高斯求解还是 m4ri 求解， 0 使用高斯，1 使用 m4ri
#define GUSS_OR_M4RI 0

// 用于交换两个数组
_INLINE_ void
swap(OUT uint8_t *a, OUT uint8_t *b, uint32_t eq_j, uint32_t guss_j_num) {
    uint8_t tmp_guss[guss_j_num];
    for (uint32_t change_i = eq_j; change_i < guss_j_num; change_i++) {
        tmp_guss[change_i] = a[change_i];
        a[change_i]        = b[change_i];
        b[change_i]        = tmp_guss[change_i];
    }
}

// 64 位异或
_INLINE_ ret_t
xor_8(OUT uint8_t      *res,
      IN const uint8_t *a,
      IN const uint8_t *b,
      IN const uint64_t bytelen,
      IN const uint64_t r_bytelen) {
    for (uint64_t i = r_bytelen; i < bytelen; i++) {
        res[i] = a[i] ^ b[i];
    }
    return SUCCESS;
}

// 将 增广常数数组 传递给 equations 的最后一列
_INLINE_ void
term_to_equations(OUT uint32_t equations[][EQ_COLUMN], IN const syndrome_t *pad_constant_term) {
    // 处理前 11776 位
    for (uint32_t i = 0; i < R_QW - 1; i++) {
        for (uint64_t index = 0, location = 1; location != 0; location <<= 1) {
            if ((pad_constant_term->qw[i] & location) != 0) {
                equations[64 * i + index][EQ_COLUMN - 1] = 1;
            }
            index++;
        }
    }
    // 处理最后三位
    for (uint64_t index = 0, location = 1; location <= MASK(LAST_R_QW_LEAD); location <<= 1) {
        if ((pad_constant_term->qw[R_QW - 1] & location) != 0) {
            equations[64 * (R_QW - 1) + index][EQ_COLUMN - 1] = 1;
        }
        index++;
    }
}

// 利用解出来的 b 和 ct 还原 e()
_INLINE_ void
solving_equations_e(OUT split_e_t *e_verify, IN split_e_t *ct_verify, IN uint32_t b[]) {
    // 放 0 用 '与', 放 1 用 '或'
    // 定义 11111111 和 00000001 用于计算
    uint8_t mask_1 = 1;
    int     bit_u  = 8;
    // 对第一组操作
    for (int i_v = 0; i_v < R_BITS; i_v++) {
        if (b[i_v] == 2) {
            if (((mask_1 << (i_v % bit_u)) & (ct_verify->val[0].raw[i_v / bit_u])) != 0) {
                e_verify->val[0].raw[i_v / bit_u] += mask_1 << (i_v % bit_u);
            }
        } else if (b[i_v] == 1) {
            if (((mask_1 << (i_v % bit_u)) & (ct_verify->val[0].raw[i_v / bit_u])) == 0) {
                e_verify->val[0].raw[i_v / bit_u] += mask_1 << (i_v % bit_u);
            }
        }
    }
    // 对第二组操作
    for (int i_v = R_BITS; i_v < 2 * R_BITS; i_v++) {
        if (b[i_v] == 2) {
            if (((mask_1 << ((i_v - R_BITS) % bit_u)) &
                 (ct_verify->val[1].raw[(i_v - R_BITS) / bit_u])) != 0) {
                e_verify->val[1].raw[(i_v - R_BITS) / bit_u] += mask_1 << ((i_v - R_BITS) % bit_u);
            }
        } else if (b[i_v] == 1) {
            if (((mask_1 << ((i_v - R_BITS) % bit_u)) &
                 (ct_verify->val[1].raw[(i_v - R_BITS) / bit_u])) == 0) {
                e_verify->val[1].raw[(i_v - R_BITS) / bit_u] += mask_1 << ((i_v - R_BITS) % bit_u);
            }
        }
    }
}

// 对 bytelen 长字节流, a 取反并和 b 与 (res = ~a & b)
_INLINE_ ret_t
negate_and(OUT uint8_t *res, IN const uint8_t *a, IN const uint8_t *b, IN const uint64_t bytelen) {
    for (uint64_t i = 0; i < bytelen; i++) {
        res[i] = (~a[i]) & b[i];
    }
    return SUCCESS;
}

// 对两个数组进行或操作
// a = (a | b)
_INLINE_ void
array_or(IN OUT uint8_t *a, IN const uint8_t *b, IN const uint64_t bytelen) {
    for (uint64_t i = 0; i < bytelen; i++) {
        a[i] = a[i] | b[i];
    }
}

// Function:  find_threshold_bucket
// --------------------------------
//
// Given a list of counting buckets (counts) whose UPC ranges starts at a certain value (base),
// and a target number of flips (nflips), this function finds out which of the buckets contains
// the threshold.
//
// Suppose n_flips = 40 and counts is the following vector:
// counts = [10, 20, 30, 40, 40, 30, 20, 10]
//
// The function runs through counts in reversed order until it finds a number >= n_flips of
// counters. Therefore, in this case, the function returns Bucket 5.
//
// Input Arguments:
//  -uint8_t    counts[]: The values of the 8 counting buckets
//  -uint32_t   n_flips: The target number of flips
//
// Output Arguments:
//  -uint8_t *threshold_bucket: The bucket where the threshold lives
//  -uint32_t *n_gt_threshold: The current count of UPC counters that are greater than the
//                             maximum value in the range represented by the current
//                             threshold_bucket. (Remember that, on each call
//                             find_threshold_bucket, the resolution of the buckets in `counts`
//                             is increased by a factor of 8.)
//
_INLINE_ void
find_threshold_bucket(OUT uint8_t  *threshold_bucket,
                      OUT uint32_t *n_gt_threshold,
                      IN uint8_t    counts[],
                      IN uint32_t   n_flips) {
    uint32_t sum                         = 0;
    uint32_t found_threshold_bucket_mask = 0;

    for (uint32_t k = 0; k < COUNTING_SORT_BUCKETS; k++) {
        // Runs through UPC buckets in reversed order
        uint8_t current_bucket = COUNTING_SORT_BUCKETS - 1 - k;

        // Sums the number counters of each bucket.
        // The idea is that the bucket where the threshold lives is the first one in which
        // sum + *n_gt_threshold >= n_flips, when buckets are accounted in reversed order.
        sum += counts[current_bucket];

        // Updates the threshold bucket only if ~found_threshold_bucket_mask
        *threshold_bucket = (current_bucket & (~found_threshold_bucket_mask)) |
                            (*threshold_bucket & found_threshold_bucket_mask);

        // This mask is equal to 0xFFFFFFFFFF only once in the loop
        uint32_t is_this_the_threshold_bucket_mask =
            (~secure_l32_mask(n_flips - 1, *n_gt_threshold + sum)) &
            (~found_threshold_bucket_mask);

        // Do not be fooled by the += below!
        // The value of *n_gt_threshold is updated exactly once, because it depends on
        // is_this_the_threshold_bucket_mask to be == 0xFFFFFFFF
        *n_gt_threshold += (sum - counts[current_bucket]) & is_this_the_threshold_bucket_mask;

        found_threshold_bucket_mask |= is_this_the_threshold_bucket_mask;
    }
}

// Function:  get_fixflip_threshold
// --------------------------------
//
// Finds the FixFlip threshold data used by fixflip_iter to flip a fixed number (n_flips) of bits.
// Remember that the FixFlip threshold data is defined not only by a threshold number, but by a
// pair: (tau, n_tau), which, in this implementation is represented by the type
// fixflip_threshold_t defined in fixflip.h as follows:
//      typedef struct fixflip_threshold_s {
//          uint8_t  threshold;                     // Represents threshold tau
//          uint8_t  n_equal_threshold;             // Represents n_tau
//      } fixflip_threshold_t;
//
//  Function fixflip_iter then flips n_flips bits doing the following:
//      - If the bit UPC counter is greater than `threshold`: flip the bit
//      - Flip only `n_equal_threshold` bits whose UPC counter is equal `threshold`
//
// Input Arguments:
//  - fixflip_upc_t *ff_upc: The UPC counter values
//  - uint32_t       n_flips: The number of bits to be flipped
//
// Output Argument:
//  - fixflip_threshold_t *ff_threshold: The fixflip threshold data to be used by fixflip_iter
//                                       when deciding which bits to flip.
//
//  Implementation:
//      This function performs COUNTING_LEVELS = 3 rounds of countings to find the threshold
//      values. In each level, the resolution of the counting buckets the search gets smaller. In
//      the first iteration each bucket represents a range of numbers, and by the last iteration
//      buckets represents only one number. The idea is that each iteration decides in which
//      bucket the threshold lives, and this bucket is expanded in the next iteration.
//
void
get_fixflip_threshold(OUT fixflip_threshold_t *ff_threshold,
                      IN fixflip_upc_t        *ff_upc,
                      IN uint32_t              n_flips) {

    uint32_t base = 0;

    ff_threshold->threshold         = 0;
    ff_threshold->n_equal_threshold = 0;

    // This variable counts the number of elements in buckets that are greater than
    // the current threshold_bucket
    uint32_t n_gt_threshold = 0;

    // As described in the paper, the search for the threshold is done in COUNTING_LEVELS =
    // iterations. In each iteration, the algorithm expands the bucket of reduced counters where
    // the threshold should be in.
    for (int i = 0; i < COUNTING_LEVELS; i++) {

        uint8_t counts[COUNTING_SORT_BUCKETS] = {0};

        // The step size resolution is increased in each iteration, which narrows down the value
        // of the fixflip threshold.
        //
        // In particular, step = 8 ^ (COUNTING_LEVELS - 1 - i)
        //
        // That is:
        //      - when i = 0: step = 64
        //      - when i = 1: step = 8
        //      - when i = 2: step = 1

        uint32_t step = 1 << (3 * (COUNTING_LEVELS - 1 - i));

        // Get the reduced counters counted into the following 8 UPC buckets
        // Bucket 0: [base, base + step[
        // Bucket 1: [base + step, base + 2*step[
        //  ...,
        // Bucket 7: [base + 7*step, base + 8*step[
        reduce_upcs_then_count(counts, ff_upc, base, step);

        // Find out which of the 8 buckets above contains the threshold tau
        uint8_t threshold_bucket = 0;
        find_threshold_bucket(&threshold_bucket, &n_gt_threshold, counts, n_flips);

        // Move base to the start of the bucket where the threshold lives
        base += threshold_bucket * step;

#if defined(USE_RANDOMIZED_SELECTION_OF_EQ_THRESHOLD_BITS) && (N_FLIP_FLAGS_BLOCKS <= 4)
        // For levels 1 and 3, we can extract Ntau from the last buckets
        if (i == COUNTING_LEVELS - 1) {
            for (uint32_t k = 0; k < COUNTING_SORT_BUCKETS; k++) {
                uint32_t count        = counts[k];
                uint32_t right_bucket = -secure_cmp32(k, threshold_bucket);
                ff_threshold->total_equal_threshold =
                    (count & right_bucket) | (ff_threshold->total_equal_threshold & ~right_bucket);
            }
        }
#endif
    }
    ff_threshold->threshold = base;

#if defined(USE_RANDOMIZED_SELECTION_OF_EQ_THRESHOLD_BITS)

#    if (N_FLIP_FLAGS_BLOCKS > 4)
    ff_threshold->total_equal_threshold =
        compute_total_equal_threshold(ff_upc, ff_threshold->threshold);
#    endif

    uint32_t lower_than_2kappa_mask =
        secure_l32_mask(N_FLIP_FLAGS_BLOCKS * 64 - 1, ff_threshold->total_equal_threshold);

    ff_threshold->n_equal_threshold = (n_flips - n_gt_threshold) & lower_than_2kappa_mask;
#else

    ff_threshold->n_equal_threshold = n_flips - n_gt_threshold;

#endif
}

// Function: fixflip_iter
// ----------------------
//
//  Flips `n_flips` bits of a partial error vector `e` inplace. Additionally, the syndrome is
//  recomputed for the new value of `e` and `syndrome` is updated.
//
// Input arguments:
//  - split e_t *e: The partial error vector up to this point.
//  - syndrome_t *syndrome: The syndrome
//  - uint32_t n_flips: The number of bits to be flipped
//  - ct_t *ct: The ciphertext (used to recomputed the syndrome after flipping bits of e)
//  - sk_t *sk: The secret key (used to recomputed the syndrome after flipping bits of e)
//
// Output arguments:
//  - split_e_t *e: The partial error vectors after the nflips bits were flipped
//  - syndrome_t *syndrome: The recomputed syndrome for the new error vector `e`
//
ret_t
fixflip_iter(OUT split_e_t    *e,
             OUT syndrome_t   *syndrome,
             IN const uint32_t n_flips,
             IN const ct_t    *ct,
             IN const sk_t    *sk) {

    fixflip_upc_t ff_upc;
    memset(&ff_upc, 0, sizeof(ff_upc));

    get_upc(&ff_upc, syndrome, sk->wlist);
    flip_worst_fit_indexes(e, &ff_upc, n_flips);

    GUARD(recompute_syndrome(syndrome, ct, sk, e));
    return SUCCESS;
}

// Function: pickyflip_iter
// ----------------------
//
//  IMPORTANT NOTICE:
//  ================
//  TO IMPLEMENT pickyflip_iter, WE REUSED FUNCTION find_err1, ORIGINALLY IMPLEMENTED BY
//  Nir Drucker, Shay Gueron, and Dusan Kostic, AWS Cryptographic Algorithms Group.
//  (ndrucker@amazon.com, gueron@amazon.com, dkostic@amazon.com)
//  ===========================================================================
//
//
//  Flips `n_flips` bits of a partial error vector `e` inplace. Additionally, the syndrome is
//  recomputed for the new value of `e` and `syndrome` is updated.
//
// Input arguments:
//  - split e_t *e: The partial error vector up to this point.
//  - syndrome_t *syndrome: The syndrome
//  - uint8_t threshold_in: The UPC threshold for flipping a bit from 0 to 1
//  - uint8_t threshold_out: The UPC threshold for flipping a bit from 1 to 0
//  - ct_t *ct: The ciphertext (used to recomputed the syndrome after flipping bits of e)
//  - sk_t *sk: The secret key (used to recomputed the syndrome after flipping bits of e)
//
// Output arguments:
//  - split_e_t *e: The partial error vectors after the nflips bits were flipped
//  - syndrome_t *syndrome: The recomputed syndrome for the new error vector `e`
//
ret_t
pickyflip_iter(OUT split_e_t     *e,
               IN OUT syndrome_t *syndrome,
               IN const uint8_t   threshold_in,
               IN const uint8_t   threshold_out,
               IN const ct_t     *ct,
               IN const sk_t     *sk) {
    DEFER_CLEANUP(syndrome_t rotated_syndrome = {0}, syndrome_cleanup);
    DEFER_CLEANUP(upc_t upc, upc_cleanup);

    split_e_t e_copy;
    memcpy(&e_copy, e, sizeof(*e));

    assert(threshold_in >= threshold_out);

    for (uint32_t i = 0; i < N0; i++) {
        // UPC must start from zero at every iteration
        memset(&upc, 0, sizeof(upc));

        // 1) Right-rotate the syndrome for every secret key set bit index
        //    Then slice-add it to the UPC array.
        for (size_t j = 0; j < DV; j++) {
            rotate_right(&rotated_syndrome, syndrome, sk->wlist[i].val[j]);
            bit_sliced_adder(&upc, &rotated_syndrome, LOG2_MSB(j + 1));
        }

        // 2) Subtract the threshold from the UPC counters
        bit_slice_full_subtract(&upc, threshold_out); // threshold_in > threshold_out

        // 3) Update the errors vector.
        //    The last slice of the UPC array holds the MSB of the accumulated
        //    values minus the threshold. Every zero bit indicates a potential
        //    error bit.
        const r_t *last_slice_out = &(upc.slice[SLICES - 1].u.r.val);
        for (size_t j = 0; j < R_SIZE; j++) {
            const uint8_t sum_msb = (~last_slice_out->raw[j]);
            e->val[i].raw[j] ^= ((e_copy.val[i].raw[j]) & sum_msb);
        }
        e->val[i].raw[R_SIZE - 1] &= LAST_R_BYTE_MASK;

        // Now we have to consider the bits that are 0 to be flipped to 1.
        // This is controlled by theshold_in. Since upc was already
        // subtracted by threshold_out, we just need to subtract it by
        // (threshold_in - threshold_out)
        bit_slice_full_subtract(&upc, threshold_in - threshold_out);
        const r_t *last_slice_in = &(upc.slice[SLICES - 1].u.r.val);
        for (size_t j = 0; j < R_SIZE; j++) {
            const uint8_t sum_msb = (~last_slice_in->raw[j]);
            e->val[i].raw[j] ^= (~(e_copy.val[i].raw[j]) & sum_msb);
        }

        // Ensure that the padding bits (upper bits of the last byte) are zero so
        // they will not be included in the multiplication and in the hash
        // function.
        e->val[i].raw[R_SIZE - 1] &= LAST_R_BYTE_MASK;
    }

    GUARD(recompute_syndrome(syndrome, ct, sk, e));
    return SUCCESS;
}

// 新增函数，只用于寻找大于 th 的位置集合
ret_t
pickyflip_find_x_th(OUT split_e_t       *x_collection,
                    IN const syndrome_t *syndrome,
                    IN const uint8_t     threshold,
                    IN const sk_t       *sk) {
    DEFER_CLEANUP(syndrome_t rotated_syndrome = {0}, syndrome_cleanup);
    DEFER_CLEANUP(upc_t upc, upc_cleanup);

    for (uint32_t i = 0; i < N0; i++) {
        // UPC must start from zero at every iteration
        memset(&upc, 0, sizeof(upc));

        // 1) Right-rotate the syndrome for every secret key set bit index
        //    Then slice-add it to the UPC array.
        for (size_t j = 0; j < DV; j++) {
            rotate_right(&rotated_syndrome, syndrome, sk->wlist[i].val[j]);
            bit_sliced_adder(&upc, &rotated_syndrome, LOG2_MSB(j + 1));
        }

        // 2) Subtract the threshold from the UPC counters
        bit_slice_full_subtract(&upc, threshold); // upc - threshold

        // 3) Update the errors vector.
        //    The last slice of the UPC array holds the MSB of the accumulated
        //    values minus the threshold. Every zero bit indicates a potential
        //    error bit.
        const r_t *last_slice_out = &(upc.slice[SLICES - 1].u.r.val);
        for (size_t j = 0; j < R_SIZE; j++) {
            const uint8_t sum_msb = (~last_slice_out->raw[j]);
            // 仅仅记录大于 th 的集合
            x_collection->val[i].raw[j] = sum_msb;
        }
    }

    return SUCCESS;
}

// Function: decode_pickyfix
// ------------------------
//
//  The full decoding of an error vector, given a ciphertext. This is the entry
//  point of the contribution of our paper.
//
//  We propose this algorithm as a replacement for BGF. The reader is invited
//  to inspect the code for decode_bgf in decode/decode.c to see the similarities
//  (and differences) between the two.
//
//  Notice that: for each security level, a different number of flips is made
//  in the first iteration. This is defined by the constant FIXFLIP_HEAD_N_FLIPS.
//  Furthermore, notice that the threshold used by bitflip_iter is the same
//  as the one used in BGF, but in FixFlip, they are used at different times.
//
// Input arguments:
//  - syndrome_t *original_s: The target syndrome
//  - ct_t *ct: The ciphertext
//  - sk_t *sk: The secret key
//
// Output arguments:
//  - split_e_t *e: The error vector that will be recovered from the ciphertext
//
ret_t
decode_pickyfix(OUT split_e_t       *e,
                IN const syndrome_t *original_s,
                IN const ct_t       *ct,
                IN const sk_t       *sk) {
    syndrome_t s;

    // 新增求解集合
    split_e_t x_collection = {0};
    // 临时变量 s_tmp
    syndrome_t s_tmp = {0};
    // 新增临时解集合
    split_e_t x_collection_tmp = {0};

    memset(e, 0, sizeof(*e));
    memcpy(&s_tmp, original_s, sizeof(*original_s));
    s = *original_s;
    dup(&s);
    dup(&s_tmp);

    for (int i = 0; i < MAX_IT; i++) {
        if (i == 0) {
            GUARD(fixflip_iter(e, &s, FIXFLIP_HEAD_N_FLIPS, ct, sk));
            // -----------------------------------------------------------------------------------------
            // 增加可疑未知数的搜寻算法
            GUARD(fixflip_iter(&x_collection, &s_tmp, FIND_X_COUNT, ct, sk));
            // 判断 e 和 x_collection 是否相等---test---
            split_e_t test_e = {0};
            // 与一下 e 和 x_collection
            for (uint16_t test_i = 0; test_i < R_SIZE; test_i++) {
                test_e.val[0].raw[test_i] =
                    x_collection.val[0].raw[test_i] & e->val[0].raw[test_i];
                test_e.val[1].raw[test_i] =
                    x_collection.val[1].raw[test_i] & e->val[1].raw[test_i];
            }
            // 获取测试的个数
            uint32_t test_weight = r_bits_vector_weight((r_t *)test_e.val[0].raw) +
                                   r_bits_vector_weight((r_t *)test_e.val[1].raw);
            // 获取测试的个数
            uint32_t e_test_weight = r_bits_vector_weight((r_t *)e->val[0].raw) +
                                     r_bits_vector_weight((r_t *)e->val[1].raw);
            // 获取测试的个数
            uint32_t x_test_weight = r_bits_vector_weight((r_t *)x_collection.val[0].raw) +
                                     r_bits_vector_weight((r_t *)x_collection.val[1].raw);
            printf("\n\n第一轮第一步测试 与 个数: %u, e的个数: %u , x 个数: %u \n", test_weight,
                   e_test_weight, x_test_weight);

            // 获取大于 th 的集合, 合并两个数组
            GUARD(pickyflip_find_x_th(&x_collection_tmp, &s, get_threshold(&s), sk));
            for (uint8_t i_N0 = 0; i_N0 < N0; i_N0++) {
                array_or((uint8_t *)&x_collection.val[i_N0].raw, x_collection_tmp.val[i_N0].raw,
                         R_SIZE);
            }
            // -----------------------------------------------------------------------------------------
            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));
            // -----------------------------------------------------------------------------------------
            // 获取大于 th 的集合, 合并两个数组
            GUARD(pickyflip_find_x_th(&x_collection_tmp, &s, get_threshold(&s), sk));
            for (uint8_t i_N0 = 0; i_N0 < N0; i_N0++) {
                array_or((uint8_t *)&x_collection.val[i_N0].raw, x_collection_tmp.val[i_N0].raw,
                         R_SIZE);
            }
            // -----------------------------------------------------------------------------------------
            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));
        } else {
            // -----------------------------------------------------------------------------------------
            // 获取大于 th 的集合, 合并两个数组
            GUARD(pickyflip_find_x_th(&x_collection_tmp, &s, get_threshold(&s), sk));
            for (uint8_t i_N0 = 0; i_N0 < N0; i_N0++) {
                array_or((uint8_t *)&x_collection.val[i_N0].raw, x_collection_tmp.val[i_N0].raw,
                         R_SIZE);
            }
            // -----------------------------------------------------------------------------------------
            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));
        }
    }

    // 获取未知数的个数
    uint32_t x_weight = r_bits_vector_weight((r_t *)x_collection.val[0].raw) +
                        r_bits_vector_weight((r_t *)x_collection.val[1].raw);

    printf("\n需要求解的未知数个数: %u\n", x_weight);

    // pickyfix 翻转的 e 的个数
    uint32_t e_weight =
        r_bits_vector_weight((r_t *)e->val[0].raw) + r_bits_vector_weight((r_t *)e->val[1].raw);

    printf("\npickyfix 求解的 e 的个数: %u\n", e_weight);

    // ===========================↓进行方程组求解算法↓===============================
    ct_t       ct_pad            = {0};
    sk_t       sk_transpose      = {0};
    ct_t       ct_remove_BG      = {0};
    syndrome_t pad_constant_term = {0};

    for (uint32_t i = 0; i < N0; i++) {
        // 获取 ct 的值
        ct_pad.val[i] = ct->val[i];

        // 构造 sk 转置 sk_transpose
        // 获取 sk 转置的首行索引
        // 𝜑(A)' = a0 + ar-1X + ar-2X^2 ...
        for (uint8_t i_DV = 0; i_DV < DV; i_DV++) {
            if (sk->wlist[i].val[i_DV] != 0) {
                sk_transpose.wlist[i].val[i_DV] = R_BITS - sk->wlist[i].val[i_DV];
            } else {
                sk_transpose.wlist[i].val[i_DV] = sk->wlist[i].val[i_DV];
            }
        }

        // 去除 c 中的未知数位，将 black_or_gray_e 取反后与 c 做与操作
        GUARD(negate_and(ct_remove_BG.val[i].raw, x_collection.val[i].raw, ct_pad.val[i].raw,
                         R_SIZE));
    }

    // 构造 m4ri 解数组
    uint32_t b[2 * R_BITS] = {0};

    if (GUSS_OR_M4RI == 0) {
        // ----------------------- 高斯消元求解 -----------------------

        // 对方程组未知数进行构建，将 x0-xall 的对应关系列出来
        // x_collection 的每个位置对应 旋转 h 的位置满足 (e+r-h) % r
        // 对每个 x_collection 进行 and 寻找是否存在未知数, guss_j_num 最后一个字用来存储 b
        uint32_t guss_j_num = 0;
        if (x_weight % GUSS_BLOCK == 0) {
            guss_j_num = x_weight / GUSS_BLOCK + 1;
        } else {
            guss_j_num = x_weight / GUSS_BLOCK + 2;
        }
        uint8_t equations_guss_byte[R_BITS][guss_j_num];
        memset(equations_guss_byte, 0, sizeof(equations_guss_byte));

        uint8_t  mask_e       = 1;
        uint8_t  mask_e_byte  = 1;
        uint32_t e_count      = 0;
        uint32_t e_index      = 0;
        uint32_t e_index_byte = 0;
        uint32_t x_arr[x_weight];
        memset(x_arr, 0, sizeof(x_arr));
        for (uint8_t i = 0; i < N0; i++) {
            for (uint32_t i_e_x = 0; i_e_x < R_BITS; i_e_x++) {
                if (i_e_x % GUSS_BLOCK == 0) {
                    mask_e  = 1;
                    e_index = i_e_x / GUSS_BLOCK;
                }
                if ((mask_e & x_collection.val[i].raw[e_index]) != 0) {
                    if (e_count % GUSS_BLOCK == 0) {
                        mask_e_byte  = 1;
                        e_index_byte = e_count / GUSS_BLOCK;
                    }
                    uint32_t e_add_R = i_e_x + R_BITS;
                    x_arr[e_count]   = i_e_x + i * R_BITS;
                    e_count += 1;
                    // 根据 e 的和 h 的位置来确定 equations_guss_byte 的构建 (e+r-h) % r
                    for (uint32_t wlist_i = 0; wlist_i < DV; wlist_i++) {
                        equations_guss_byte[(e_add_R - sk_transpose.wlist[i].val[wlist_i]) %
                                            R_BITS][e_index_byte] += mask_e_byte;
                    }
                    mask_e_byte <<= 1;
                }
                mask_e <<= 1;
            }
        }

        // 将 ct_remove_BG 和 H 相乘, 使用 gf2x_mod_mul(), 得到结果 constant_term
        // 这里计算方式与 compute_syndrome() 计算方式一致, 可调用此函数构建
        GUARD(compute_syndrome(&pad_constant_term, &ct_remove_BG, sk));

        // ---- test ---- 打印 pad_constant_term 的值
        print("\npad_constant_term: \n", (uint64_t *)pad_constant_term.qw, R_BITS);

        uint32_t equations[R_BITS][EQ_COLUMN] = {0};
        // 将增广常数 pad_constant_term 赋值给 equations[i][EQ_COLUMN]
        term_to_equations(equations, (syndrome_t *)&pad_constant_term);

        // equations_guss_byte 加入常数列
        for (uint32_t i_b = 0; i_b < R_BITS; i_b++) {
            if (equations[i_b][EQ_COLUMN - 1] == 1) {
                equations_guss_byte[i_b][guss_j_num - 1] = 1;
            }
        }

        // 设置 x 主元表
        uint8_t guss_x_main[R_BITS] = {0};
        // 开始消元
        for (uint32_t guss_j = 0; guss_j < x_weight; guss_j++) {
            uint8_t  mask_1    = 1;
            uint8_t  mask_guss = (mask_1 << (guss_j % GUSS_BLOCK));
            uint32_t eq_j      = guss_j / GUSS_BLOCK;
            for (uint32_t guss_i = guss_j; guss_i < R_BITS; guss_i++) {
                if ((mask_guss & equations_guss_byte[guss_i][eq_j]) != 0) {
                    if (guss_x_main[guss_j] == 0) {
                        // 如果此列没有主元优先挑选主元
                        // 将此行作为当前列主元，交换第一行并继续向后消元
                        guss_x_main[guss_j] = 1;
                        swap(equations_guss_byte[guss_j], equations_guss_byte[guss_i], eq_j,
                             guss_j_num);
                    } else {
                        // 使用第 guss_j 行消此行
                        GUARD(xor_8(equations_guss_byte[guss_i], equations_guss_byte[guss_i],
                                    equations_guss_byte[guss_j], guss_j_num, eq_j));
                    }
                }
            }
        }
        // 倒着求解
        for (int guss_j = x_weight - 1; guss_j >= 0; guss_j--) {
            uint32_t eq_j = guss_j / GUSS_BLOCK;
            for (uint32_t guss_i = guss_j; guss_i > 0; guss_i--) {
                if ((equations_guss_byte[guss_j][eq_j] & equations_guss_byte[guss_i - 1][eq_j]) !=
                    0) {
                    equations_guss_byte[guss_i - 1][eq_j] ^= equations_guss_byte[guss_j][eq_j];
                    equations_guss_byte[guss_i - 1][guss_j_num - 1] ^=
                        equations_guss_byte[guss_j][guss_j_num - 1];
                }
            }
        }

        for (uint32_t i = 0; i < x_weight; i++) {
            if (equations_guss_byte[i][guss_j_num - 1] == 0) {
                b[x_arr[i]] = 2;
            } else {
                b[x_arr[i]] = 1;
            }
        }

        // ----------------------- 高斯消元求解结束 -----------------------
    } else {

        // ----------------------- m4ri 求解 -----------------------

        // 对方程组未知数进行构建，将 x0-xall 的对应关系列出来, x_collection 的每个位置对应 旋转 h
        // 的位置满足 (e+r-h) % r 对每个 x_collection 进行 and 寻找是否存在未知数, guss_j_num
        // 最后一个字用来存储 b

        uint32_t guss_j_num = 0;
        if (x_weight % BLOCK == 0) {
            guss_j_num = x_weight / BLOCK + 1;
        } else {
            guss_j_num = x_weight / BLOCK + 2;
        }
        uint64_t equations_guss_byte[R_BITS][guss_j_num];
        memset(equations_guss_byte, 0, sizeof(equations_guss_byte));

        uint8_t  mask_e       = 1;
        uint64_t mask_e_byte  = 1;
        uint32_t e_count      = 0;
        uint32_t e_index      = 0;
        uint32_t e_index_byte = 0;
        // 保存每个 x 对应的位置
        uint32_t x_arr[x_weight];
        memset(x_arr, 0, sizeof(x_arr));

        // 填充 equations_guss_byte
        for (uint8_t i = 0; i < N0; i++) {
            for (uint32_t i_e_x = 0; i_e_x < R_BITS; i_e_x++) {
                if (i_e_x % 8 == 0) {
                    mask_e  = 1;
                    e_index = i_e_x / 8;
                }
                if ((mask_e & x_collection.val[i].raw[e_index]) != 0) {
                    if (e_count % BLOCK == 0) {
                        mask_e_byte  = 1;
                        e_index_byte = e_count / BLOCK;
                    }
                    uint32_t e_add_R = i_e_x + R_BITS;
                    x_arr[e_count]   = i_e_x + i * R_BITS;
                    e_count += 1;
                    // 根据 e 的和 h 的位置来确定 equations_guss_byte 的构建 (e+r-h) % r
                    for (uint32_t wlist_i = 0; wlist_i < DV; wlist_i++) {
                        equations_guss_byte[(e_add_R - sk_transpose.wlist[i].val[wlist_i]) %
                                            R_BITS][e_index_byte] += mask_e_byte;
                    }
                    mask_e_byte <<= 1;
                }
                mask_e <<= 1;
            }
        }

        // 将 ct_remove_BG 和 H 相乘, 使用 gf2x_mod_mul(), 得到结果 constant_term
        // 这里计算方式与 compute_syndrome() 计算方式一致, 可调用此函数构建
        GUARD(compute_syndrome(&pad_constant_term, &ct_remove_BG, sk));

        // 处理前整个块位
        for (uint32_t i = 0; i < R_QW - 1; i++) {
            for (uint64_t index = 0, location = 1; location != 0; location <<= 1) {
                if ((pad_constant_term.qw[i] & location) != 0) {
                    equations_guss_byte[64 * i + index][guss_j_num - 1] = 1;
                }
                index++;
            }
        }
        // 处理溢出位
        for (uint64_t index = 0, location = 1; location <= MASK(LAST_R_QW_LEAD); location <<= 1) {
            if ((pad_constant_term.qw[R_QW - 1] & location) != 0) {
                equations_guss_byte[64 * (R_QW - 1) + index][guss_j_num - 1] = 1;
            }
            index++;
        }

        // 开始求解

        mzd_t *A = mzd_init(R_BITS, x_weight);
        mzd_t *B = mzd_init(R_BITS, 1);
        // 给 A 填充信息
        wi_t const width_A    = A->width - 1;
        word const mask_end_A = A->high_bitmask;
        for (rci_t i = 0; i < A->nrows; ++i) {
            word *row = mzd_row(A, i);
            for (wi_t j = 0; j < width_A; ++j)
                row[j] = ((uint64_t *)(equations_guss_byte[i]))[j];
            row[width_A] ^=
                (row[width_A] ^ ((uint64_t *)equations_guss_byte[i])[width_A]) & mask_end_A;
        }
        __M4RI_DD_MZD(A);

        // 给 B 填充信息
        wi_t const width_B    = B->width - 1;
        word const mask_end_B = B->high_bitmask;
        for (rci_t i = 0; i < B->nrows; ++i) {
            word *row = mzd_row(B, i);
            for (wi_t j = 0; j < width_B; ++j)
                row[j] = ((uint64_t *)(equations_guss_byte[i]))[width_A + 1];
            row[width_B] ^=
                (row[width_B] ^ ((uint64_t *)equations_guss_byte[i])[width_A + 1]) & mask_end_B;
        }
        __M4RI_DD_MZD(B);

        int consistency = mzd_solve_left(A, B, 0, 0);

        if (consistency == -1) {
            printf("\nm4ri 未能找到一组解\n");
        } else {
            printf("\nm4ri 成功找到一组解\n");
        }

        // 将结果从 B 中取出来
        for (uint32_t i = 0; i < x_weight; i++) {
            word const *row = mzd_row_const(B, i);
            if ((row[0] & 1) == 1) {
                b[x_arr[i]] = 1;
            } else {
                b[x_arr[i]] = 2;
            }
        }

        // ----------------------- m4ri 求解结束 -----------------------
    }

    // ===========================↑求解算法↑===============================

    // 用于还原 e
    split_e_t ct_verify = {0};
    ct_verify.val[0]    = ct->val[0];
    ct_verify.val[1]    = ct->val[1];

    // 还原 e
    split_e_t e_verify = {0};
    solving_equations_e(&e_verify, &ct_verify, b);
    uint32_t e_verify_weight = r_bits_vector_weight((r_t *)e_verify.val[0].raw) +
                               r_bits_vector_weight((r_t *)e_verify.val[1].raw);
    printf("\n解方程还原的 e 的重量: %u\n", e_verify_weight);

    // 利用还原的 e 计算 s
    syndrome_t s_verify = {0};
    GUARD(recompute_syndrome(&s_verify, ct, sk, &e_verify));

    // 判断成功与否
    if (r_bits_vector_weight((r_t *)s_verify.qw) > 0) {
        printf("\n解方程失败, 未能还原 e\n");
    } else {
        printf("\n解方程成功, 成功还原 e\n");
    }

    if (r_bits_vector_weight((r_t *)s.qw) > 0) {
        printf("\npickyfix 译码失败\n");
        DMSG("    Weight of e: %lu\n",
             r_bits_vector_weight(&e->val[0]) + r_bits_vector_weight(&e->val[1]));
        DMSG("    Weight of syndrome: %lu\n", r_bits_vector_weight((r_t *)s.qw));
        BIKE_ERROR(E_DECODING_FAILURE);
    }

    printf("\npickyfix 译码成功, 成功还原 e\n");

    return SUCCESS;
}

#ifdef USE_RANDOMIZED_SELECTION_OF_EQ_THRESHOLD_BITS

// Simple constant-time modulo computation. Hides both the numerator parts `ns` and `d`.
// See https://soatok.blog/2020/08/27/soatoks-guide-to-side-channel-attacks/
// for reference.
_INLINE_ uint32_t
secure_modulo_big_n(uint32_t ns[N_32_BIT_BLOCKS_FOR_RANDOM_BITS_FOR_FISHER_YATES], uint32_t d) {
    uint32_t valid_mask = ~secure_l32_mask(0, d);

    uint32_t r = 0;

    for (uint32_t b = 0; b < N_32_BIT_BLOCKS_FOR_RANDOM_BITS_FOR_FISHER_YATES; b++) {

        for (uint32_t _i = 0; _i < 32; _i++) {
            uint32_t i   = 31 - _i;
            r            = r << 1;
            uint32_t n_i = (ns[b] >> i) & 1;
            r &= ~1;
            r |= n_i;

            uint32_t swap    = secure_l32_mask(r, d);
            uint32_t r_prime = r - d;

            r = (swap & r_prime) | (~swap & r);
        }
    }

    return (r & valid_mask) | (-1 & ~valid_mask);
}

void
init_eq_flip_flags(OUT uint64_t            eq_flip_flags[N_FLIP_FLAGS_BLOCKS],
                   IN fixflip_threshold_t *ff_threshold) {

    uint32_t weight = ff_threshold->n_equal_threshold;

    for (uint32_t i = 0; i < N_FLIP_FLAGS_BLOCKS; i++) {
        eq_flip_flags[i] = 0;

        uint64_t mask_gt_64            = (1 + secure_l32_mask(weight, 64)) - 1ULL;
        uint64_t mask_gt_0             = (1 + secure_l32_mask(weight, 1)) - 1ULL;
        uint64_t mask_between_0_and_64 = mask_gt_0 & ~mask_gt_64;

        uint64_t final_block_value = (0xffffffffffffffff) >> (64 - weight);

        eq_flip_flags[i] = (mask_gt_64) | (final_block_value & mask_between_0_and_64);

        weight -= (64 & mask_gt_64) | (0 & ~mask_gt_64);
        weight = (0 & mask_between_0_and_64) | (weight & ~mask_between_0_and_64);
    }
}

// Max is not included
_INLINE_ uint32_t
secure_get_random_index(uint32_t min, uint32_t max) {

    uint32_t valid_mask = ~secure_l32_mask(min, max);

    uint32_t random_blocks[N_32_BIT_BLOCKS_FOR_RANDOM_BITS_FOR_FISHER_YATES] = {0};
    for (uint32_t b = 0; b < N_32_BIT_BLOCKS_FOR_RANDOM_BITS_FOR_FISHER_YATES; b++) {
        random_blocks[b] = rand();
    }
    uint32_t ret = min + secure_modulo_big_n(random_blocks, max - min);

    return (ret & valid_mask) | (min & ~valid_mask);
}

_INLINE_ void
secure_swap_hiding_index2(uint64_t eq_flip_flags[N_FLIP_FLAGS_BLOCKS],
                          uint32_t index1,
                          uint32_t index2,
                          uint64_t swap_flag) {

    // Remember that index1 does not need to be blinded
    uint64_t b1   = index1 / 64;
    uint64_t o1   = index1 % 64;
    uint64_t bit1 = (eq_flip_flags[b1] >> o1) & 1;
    eq_flip_flags[b1] &= ~((1ULL & swap_flag) << o1);

    // Now, we have to hide index2
    uint64_t b2 = index2 >> 6;        // b2 = index2 % 64
    uint64_t o2 = index2 - (b2 * 64); // index2 % 64

    uint64_t bit2 = 0;
    for (uint32_t i = 0; i < N_FLIP_FLAGS_BLOCKS; i++) {
        uint64_t right_block_mask = (1ULL - secure_cmp32(i, b2)) - 1ULL;
        right_block_mask &= swap_flag;

        uint32_t bit = (eq_flip_flags[b2] >> o2) & 1;
        bit2         = (bit & right_block_mask) | (bit2 & ~right_block_mask);

        eq_flip_flags[b2] &= (~(1ULL << o2) & right_block_mask) | (~right_block_mask);

        eq_flip_flags[b2] |= ((bit1 << o2) & right_block_mask);
    }
    eq_flip_flags[b1] |= (bit2 & swap_flag) << o1;
}

void
secure_shuffle_eq_flip_flags(OUT uint64_t            eq_flip_flags[N_FLIP_FLAGS_BLOCKS],
                             IN fixflip_threshold_t *ff_threshold,
                             IN uint32_t             total_upc_counters_eq_threshold) {

    for (uint32_t i = 0; i < FIXFLIP_HEAD_N_FLIPS; i++) {
        uint32_t random    = secure_get_random_index(i, total_upc_counters_eq_threshold);
        uint64_t swap_flag = (1 + secure_l32_mask(ff_threshold->n_equal_threshold, i)) - 1UL;
        secure_swap_hiding_index2(eq_flip_flags, i, random, swap_flag);
    }
}

#endif