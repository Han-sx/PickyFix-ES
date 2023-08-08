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
#include <stdlib.h>
#include <string.h>

#include "decode_internals.h"
#include "pickyfix.h"

// 错误数据是否写入文件 0 不写入，1 写入
#define W_E_FLAG 1

// 将正确数据写入文件 0 不写入，1 写入
#define W_R_FLAG 0

// 用于计算出upc切片的值并保存在文件中
_INLINE_ void
compute_upc_and_save_test(IN upc_t upc)
{
  // ---- test ---- 将 upc 切片的值计算出来并保存
  uint64_t mask_1 = 1;
  // 处理前 R_QW - 1 位
  // 将每层累计得到的 upc_i 写入文件
  FILE *fp_2;
  fp_2 = fopen("iter_data_all.txt", "a");
  for(uint16_t i_upc = 0; i_upc < R_QW - 1; i_upc++)
  {
    for(uint64_t location = 1; location != 0; location <<= 1)
    {
      // 用于保存每个upc[i]的值
      uint16_t upc_i = 0;
      for(uint8_t location_s = 1, i_upc_s = 0; i_upc_s < SLICES - 1;
          i_upc_s++, location_s <<= 1)
      {
        if((upc.slice[i_upc_s].u.qw[i_upc] & location) != 0)
        {
          upc_i += location_s;
        }
      }
      fprintf(fp_2, "%u ", upc_i);
    }
  }
  // 处理最后 R_BITS - (R_QW - 1) * 64 位
  for(uint64_t location = 1; location < (mask_1 << (R_BITS - (R_QW - 1) * 64));
      location <<= 1)
  {
    // 用于保存每个upc[i]的值
    uint16_t upc_i = 0;
    for(uint8_t location_s = 1, i_upc_s = 0; i_upc_s < SLICES - 1;
        i_upc_s++, location_s <<= 1)
    {
      if((upc.slice[i_upc_s].u.qw[R_QW - 1] & location) != 0)
      {
        upc_i += location_s;
      }
    }
    fprintf(fp_2, "%u ", upc_i);
  }
  fclose(fp_2);
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

void
find_upc(OUT upc_all_t                  *upc_out,
         IN const syndrome_t            *syndrome,
         IN const compressed_idx_dv_ar_t wlist) {
    DEFER_CLEANUP(syndrome_t rotated_syndrome = {0}, syndrome_cleanup);
    DEFER_CLEANUP(upc_t upc, upc_cleanup);
    for (uint32_t i = 0; i < N0; i++) {
        memset(&upc, 0, sizeof(upc));
        for (size_t j = 0; j < DV; j++) {
            rotate_right(&rotated_syndrome, syndrome, wlist[i].val[j]);
            bit_sliced_adder(&upc, &rotated_syndrome, LOG2_MSB(j + 1));
        }
        // 保存 upc 到 upc_out
        for (uint8_t slice_i = 0; slice_i < SLICES; slice_i++) {
            upc_out->val[i].slice[slice_i] = upc.slice[slice_i];
        }
    }
}

ret_t
fixflip_th(OUT fixflip_threshold_t *fixflip_threshold,
           IN const syndrome_t     *syndrome,
           IN const uint32_t        n_flips,
           IN const sk_t           *sk) {

    fixflip_upc_t ff_upc;
    memset(&ff_upc, 0, sizeof(ff_upc));

    get_upc(&ff_upc, syndrome, sk->wlist);
    fixflip_find_th(fixflip_threshold, &ff_upc, n_flips);

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
pickyflip_iter(OUT split_e_t   *e,
               IN syndrome_t   *syndrome,
               IN const uint8_t threshold_in,
               IN const uint8_t threshold_out,
               IN const ct_t   *ct,
               IN const sk_t   *sk) {
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
                IN const split_e_t  *R_e,
                IN const syndrome_t *original_s,
                IN const ct_t       *ct,
                IN const sk_t       *sk) {
    syndrome_t s;

    memset(e, 0, sizeof(*e));
    s = *original_s;
    dup(&s);

    // 临时变量 s_tmp
    syndrome_t s_tmp = {0};
    memcpy(&s_tmp, original_s, sizeof(*original_s));
    dup(&s_tmp);

    // 用于保存 s 的重量
    uint32_t s_array[MAX_IT + 2] = {0};
    // 用于保存 th
    uint32_t th_array[MAX_IT + 2] = {0};
    // 用于保存 upc 的值
    upc_all_t upc_array[MAX_IT + 2] = {0};
    // 记录 e
    split_e_t e_array[MAX_IT + 2] = {0};
    // 记录 black_e
    split_e_t black_e_array[MAX_IT + 2] = {0};
    // 记录 gray_e
    split_e_t gray_e_array[MAX_IT + 2] = {0};

    // 将 p_p x 加入文件尾部, 并断行
    double p_p_array[MAX_IT + 2] = {0};
    double x_array[MAX_IT + 2]   = {0};

    for (int i = 0; i < MAX_IT; i++) {
        if (i == 0) {
            // ---------------------------------------------------------------------
            // 记录 s
            uint16_t s_weight_0 = r_bits_vector_weight((const r_t *)s.qw);
            s_array[0]          = s_weight_0;
            // 记录 th，获取 fixflip_iter 的 th
            fixflip_threshold_t fixflip_threshold = {0};
            GUARD(fixflip_th(&fixflip_threshold, &s_tmp, FIXFLIP_HEAD_N_FLIPS, sk));
            th_array[0] = fixflip_threshold.threshold;
            // 寻找 upc
            find_upc(&upc_array[0], &s, sk->wlist);

            GUARD(fixflip_iter(e, &s, FIXFLIP_HEAD_N_FLIPS, ct, sk));

            e_array[0].val[0]       = e->val[0];
            e_array[0].val[1]       = e->val[1];
            black_e_array[0].val[0] = e->val[0];
            black_e_array[0].val[1] = e->val[1];
            gray_e_array[0].val[0]  = e->val[0];
            gray_e_array[0].val[1]  = e->val[1];
            p_p_array[0]            = 0;
            x_array[0]              = 0;
            // ---------------------------------------------------------------------
            uint16_t s_weight_1 = r_bits_vector_weight((const r_t *)s.qw);
            s_array[1]          = s_weight_1;
            th_array[1]         = get_threshold(&s);
            find_upc(&upc_array[1], &s, sk->wlist);

            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));

            e_array[1].val[0]       = e->val[0];
            e_array[1].val[1]       = e->val[1];
            black_e_array[1].val[0] = e->val[0];
            black_e_array[1].val[1] = e->val[1];
            gray_e_array[1].val[0]  = e->val[0];
            gray_e_array[1].val[1]  = e->val[1];
            p_p_array[1]            = 0;
            x_array[1]              = 0;
            // ---------------------------------------------------------------------
            uint16_t s_weight_2 = r_bits_vector_weight((const r_t *)s.qw);
            s_array[2]          = s_weight_2;
            th_array[2]         = get_threshold(&s);
            find_upc(&upc_array[2], &s, sk->wlist);

            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));

            e_array[2].val[0]       = e->val[0];
            e_array[2].val[1]       = e->val[1];
            black_e_array[2].val[0] = e->val[0];
            black_e_array[2].val[1] = e->val[1];
            gray_e_array[2].val[0]  = e->val[0];
            gray_e_array[2].val[1]  = e->val[1];
            p_p_array[2]            = 0;
            x_array[2]              = 0;
            // ---------------------------------------------------------------------
        } else {
            uint16_t s_weight = r_bits_vector_weight((const r_t *)s.qw);
            s_array[i + 2]    = s_weight;
            th_array[i + 2]   = get_threshold(&s);
            find_upc(&upc_array[i + 2], &s, sk->wlist);

            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));

            e_array[i + 2].val[0]       = e->val[0];
            e_array[i + 2].val[1]       = e->val[1];
            black_e_array[i + 2].val[0] = e->val[0];
            black_e_array[i + 2].val[1] = e->val[1];
            gray_e_array[i + 2].val[0]  = e->val[0];
            gray_e_array[i + 2].val[1]  = e->val[1];
            p_p_array[i + 2]            = 0;
            x_array[i + 2]              = 0;
        }
    }
    if (r_bits_vector_weight((r_t *)s.qw) > 0) {
        // FILE *fp_3;
        // fp_3 = fopen("weight_bad.txt", "a");
        // fprintf(fp_3, "R_BITS: %d pickyfix 译码失败\n", R_BITS);
        // fclose(fp_3);

        if (W_E_FLAG == 1) {
            // ---- 将记录的数据写入文件 ----
            // 首先写入 R_e
            fprintf_LE_test((const uint64_t *)R_e->val[0].raw, R_BITS);
            fprintf_LE_test((const uint64_t *)R_e->val[1].raw, R_BITS);
            // 断行
            FILE *fp_LE_test_1;
            fp_LE_test_1 = fopen("iter_data_all.txt", "a");
            fprintf(fp_LE_test_1, "\n");
            fclose(fp_LE_test_1);

            // 写入迭代数据
            for (uint8_t iter_i = 0; iter_i < MAX_IT + 2; iter_i++) {
                // 写入 s th
                FILE *fp_iter;
                fp_iter = fopen("iter_data_all.txt", "a");
                fprintf(fp_iter, "%u %u ", s_array[iter_i], th_array[iter_i]);
                fclose(fp_iter);
                // 写入 upc
                compute_upc_and_save_test(upc_array[iter_i].val[0]);
                compute_upc_and_save_test(upc_array[iter_i].val[1]);
                // 写入 e black_e gray_e p_p x
                // 记录当前的 e0
                fprintf_LE_test((uint64_t *)e_array[iter_i].val[0].raw, R_BITS);
                // 记录当前的 e1
                fprintf_LE_test((uint64_t *)e_array[iter_i].val[1].raw, R_BITS);
                // 记录当前的 black_e0
                fprintf_LE_test((uint64_t *)black_e_array[iter_i].val[0].raw, R_BITS);
                // 记录当前的 black_e1
                fprintf_LE_test((uint64_t *)black_e_array[iter_i].val[1].raw, R_BITS);
                // 记录当前的 gray_e0
                fprintf_LE_test((uint64_t *)gray_e_array[iter_i].val[0].raw, R_BITS);
                // 记录当前的 gray_e1
                fprintf_LE_test((uint64_t *)gray_e_array[iter_i].val[1].raw, R_BITS);
                // 将 p_p,x 加入尾部, 并断行
                FILE *fp_iter_2;
                fp_iter_2 = fopen("iter_data_all.txt", "a");
                fprintf(fp_iter_2, "%f %f", p_p_array[iter_i], x_array[iter_i]);
                fprintf(fp_iter_2, "\n");
                fclose(fp_iter_2);
            }
        }

        DMSG("    Weight of e: %lu\n",
             r_bits_vector_weight(&e->val[0]) + r_bits_vector_weight(&e->val[1]));
        DMSG("    Weight of syndrome: %lu\n", r_bits_vector_weight((r_t *)s.qw));
        BIKE_ERROR(E_DECODING_FAILURE);
    }

    if (W_R_FLAG == 1) {
        // ---- 将记录的数据写入文件 ----
        // 首先写入 R_e
        fprintf_LE_test((const uint64_t *)R_e->val[0].raw, R_BITS);
        fprintf_LE_test((const uint64_t *)R_e->val[1].raw, R_BITS);
        // 断行
        FILE *fp_LE_test_1;
        fp_LE_test_1 = fopen("iter_data_all.txt", "a");
        fprintf(fp_LE_test_1, "\n");
        fclose(fp_LE_test_1);

        // 写入迭代数据
        for (uint8_t iter_i = 0; iter_i < MAX_IT + 2; iter_i++) {
            // 写入 s th
            FILE *fp_iter;
            fp_iter = fopen("iter_data_all.txt", "a");
            fprintf(fp_iter, "%u %u ", s_array[iter_i], th_array[iter_i]);
            fclose(fp_iter);
            // 写入 upc
            compute_upc_and_save_test(upc_array[iter_i].val[0]);
            compute_upc_and_save_test(upc_array[iter_i].val[1]);
            // 写入 e black_e gray_e p_p x
            // 记录当前的 e0
            fprintf_LE_test((uint64_t *)e_array[iter_i].val[0].raw, R_BITS);
            // 记录当前的 e1
            fprintf_LE_test((uint64_t *)e_array[iter_i].val[1].raw, R_BITS);
            // 记录当前的 black_e0
            fprintf_LE_test((uint64_t *)black_e_array[iter_i].val[0].raw, R_BITS);
            // 记录当前的 black_e1
            fprintf_LE_test((uint64_t *)black_e_array[iter_i].val[1].raw, R_BITS);
            // 记录当前的 gray_e0
            fprintf_LE_test((uint64_t *)gray_e_array[iter_i].val[0].raw, R_BITS);
            // 记录当前的 gray_e1
            fprintf_LE_test((uint64_t *)gray_e_array[iter_i].val[1].raw, R_BITS);
            // 将 p_p,x 加入尾部, 并断行
            FILE *fp_iter_2;
            fp_iter_2 = fopen("iter_data_all.txt", "a");
            fprintf(fp_iter_2, "%f %f", p_p_array[iter_i], x_array[iter_i]);
            fprintf(fp_iter_2, "\n");
            fclose(fp_iter_2);
        }
    }

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