#include "decode.h"
#include "gf2x.h"
#include "utilities.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "decode_internals.h"
#include "pickyfix.h"

// Function:  unslice_upc
// ----------------------
//
// Converts a bitsliced representation of the UPCs to an array.
//
// Input Arguments
//  - upc_t *upc: UPC counters in bit-sliced format, as used by BIKE's original Additional
//                implementation
// Ouput Argument
//  - uint8_t upc_raw[]: An array where each of the R_BITS UPC counters for one of the N0 blocks
//                       will be stored.
//
// NOTICE: In total, there are 2*R_BITS UPC counters. Therefore, this function must be
// called N0 = 2 times.
//
_INLINE_ void
unslice_upc(OUT uint8_t upc_raw[R_BITS], IN upc_t *upc) {
    memset(upc_raw, 0, R_BITS * (sizeof(*upc_raw)));

    for (uint32_t j = 0; j < SLICES; j++) {
        uint8_t val = (1 << j);
        for (size_t k = 0; k < R_SIZE; k++) {
            // Since R_BITS is not a multiple of 8, there are blocks that we do not need to
            // consider. Therefore nblocks = R_BITS % 8 in this case.
            size_t nblocks = k < (R_SIZE - 1) ? 8 : R_BITS % 8;
            for (size_t l = 0; l < nblocks; l++) {
                upc_raw[k * 8 + l] += ((upc->slice[j].u.r.val.raw[k] >> l) % 2) * val;
            }
        }
    }
}

// Function:  get_upc
// ------------------
//
// Computes the UPC values for each of the 2*R_BITS bits given the syndrome and the secret key.
//
// Input Arguments
//  - syndrome_t *syndrome: The syndrome used to compute the UPC
//  - compressed_idx_dv_ar_t wlist: The secret sparse matrix H in compressed format
// Ouput Argument
//  - fixflip_upc_t *ff_upc: The UPC counters
//
// Implementation:
//      This function is adapted from BIKE's additional implementation.
//      First, it does the computations in bitsliced, as done by Tung Chou's QcBits
//      (https://eprint.iacr.org/2019/150).
//      Then we unslice the UPC values to each of the N0 blocks using the
//      unslice_upc function above.
//
// NOTICE: We preserved the comments from the function ctrs, by BIKE
// Additional Implementation's authors.
//
void
get_upc(OUT fixflip_upc_t *ff_upc,
        IN const syndrome_t *           syndrome,
        IN const compressed_idx_dv_ar_t wlist) {
    DEFER_CLEANUP(syndrome_t rotated_syndrome = {0}, syndrome_cleanup);
    DEFER_CLEANUP(upc_t upc, upc_cleanup);

    for (uint32_t i = 0; i < N0; i++) {
        // Comment from BIKE Additional Implementation:
        // UPC must start from zero at every iteration
        memset(&upc, 0, sizeof(upc));

        // Comment from BIKE Additional Implementation:
        // 1) Right-rotate the syndrome for every secret key set bit index
        //    Then slice-add it to the UPC array.
        for (size_t j = 0; j < DV; j++) {
            rotate_right(&rotated_syndrome, syndrome, wlist[i].val[j]);
            bit_sliced_adder(&upc, &rotated_syndrome, LOG2_MSB(j + 1));
        }
        unslice_upc(ff_upc->blocks[i], &upc);
    }
}

// Function:  partial_count
// -----------------------
//
// Given a list of integers in {0, 1, ..., 7}, counts them into 8 buckets.
// The count is truncated after 255 occurrences. That is, if 1 appears
// 256 times or more, then count[1] will be equal to 255.
//
// Input Argument:
//  - uint16_t *reduced_upcs: The values in {0, ..., 7} to be counted
//
// Output Argument:
//  - uint8_t *counts: The array with the partial counts
//
// Implementation:
//      To perform the count in constant time, we use a 64bit integer variable `counters`.
//      Each block of 8 bits of `counters` represents one counting bucket.
//      Initially, counters == 0, that is:
//      counters = 0x00|0x00|0x00|0x00|0x00|0x00|0x00
//
//      Suppose reduced_upcs[0] = 3. Then we sum 0x01 << 3 to counters, obtaining
//      counters = 0x00|0x00|0x00|0x00|0x01|0x00|0x00
//
//      We must be careful not to overflow to the next block, when performing this sum.
//      Therefore, the value to be added
//
_INLINE_ void
partial_count(OUT uint8_t *counts, IN uint16_t *reduced_upcs) {
    uint64_t counters = 0;

    for (uint32_t index = 0; index < 2 * R_BITS; index++) {
        uint32_t tgt_col        = reduced_upcs[index];
        uint32_t valid_col_mask = 1 + secure_l32_mask(tgt_col, COUNTING_SORT_BUCKETS);

        // BE CAREFUL: We assume the CPU uses a barrel shifter, otherwise tgt_col, which
        // is sensible, may leak.
        uint8_t val = counters >> tgt_col * COUNTING_SORT_BUCKETS;

        uint32_t not_FF_mask = ~(secure_cmp32(val, 0xFF));

        // Convert 32 bits mask to 64 bits
        uint64_t mask = (uint32_t)((valid_col_mask & not_FF_mask) + 1U) - 1ULL;

        counters += (uint64_t)(mask << tgt_col * COUNTING_SORT_BUCKETS);
    }
    for (uint32_t i = 0; i < COUNTING_SORT_BUCKETS; i++) {
        counts[i] = (uint8_t)(counters >> i * COUNTING_SORT_BUCKETS);
    }
}

/* Performs a partial counting sort over reduced_upcs in ff_upc and stores the
 * sorting counters in counts. The resolution of the counting sort is given
 * by parameter n_counting_step, where n_counting_step = 0 is equal to the
 * lowest resolution.
 */
void
reduce_upcs_then_count(OUT uint8_t *counts,
                       IN fixflip_upc_t *ff_upc,
                       IN uint32_t       base,
                       IN uint32_t       step) {

    uint16_t reduced_upcs[2 * R_BITS] = {0};
    uint32_t division_by_step_shift   = LOG2(step);

    // This loop is responsible for reducing the UPC counters. That is, it will take
    // an UPC in {0, 1, ..., 255} to {0, 1, ..., 7}.
    // The rule for this reduction depends on base and
    for (uint32_t index = 0; index < 2 * R_BITS; index++) {
        uint8_t reduced_upc = upc_for_index(ff_upc, index);

        uint8_t greater_mask = ~secure_l32_mask(base + step * 8 - 1, reduced_upc);
        uint8_t lower_mask   = ~secure_l32_mask(reduced_upc, base);

        reduced_upc -= base;
        reduced_upc = reduced_upc >> division_by_step_shift; // reduced_upc /= step;

        // if (reduced_upc > base + step * 8 || reduced_upc < base) reduced_upc = 0xFF;
        reduced_upc |= (lower_mask | greater_mask);

        reduced_upcs[index] = reduced_upc;
    }
    partial_count(counts, reduced_upcs);
}


#ifdef USE_RANDOMIZED_SELECTION_OF_EQ_THRESHOLD_BITS


uint32_t
update_next32_flags(uint64_t eq_flip_flags[N_FLIP_FLAGS_BLOCKS],
                    uint32_t current_eq_weight) {

    uint32_t flip_block = current_eq_weight >> 6; // Division by 64.
    uint32_t flip_offset = current_eq_weight - flip_block*64;
    uint32_t next_32_flags = 0;
    for (uint32_t k = 0; k < N_FLIP_FLAGS_BLOCKS; k++) {

        uint64_t tmp_next_64_flags = eq_flip_flags[k] >> flip_offset;

        // We don't need to hide k!
        if (k < N_FLIP_FLAGS_BLOCKS - 1) {
            tmp_next_64_flags |= eq_flip_flags[k + 1] << (64 - flip_offset);
        }

        // Use condition mask to update next_16_flags if we are in the right block.
        uint32_t right_block_mask = -secure_cmp32(flip_block, k);
        next_32_flags = (tmp_next_64_flags & right_block_mask) | (next_32_flags & ~right_block_mask);
    }

    return next_32_flags;
}


uint32_t
get_randomized_eq_flip_mask(uint32_t next_32_flags,
                            uint32_t *base,
                            uint32_t *current_eq_weight,
                            uint64_t eq_threshold_mask) {

    uint32_t out = (next_32_flags >> *base) & 1 & eq_threshold_mask;

    *current_eq_weight += eq_threshold_mask;
    *base += eq_threshold_mask;

    return out;
}

// 用于寻找 th
void
fixflip_find_th(IN OUT fixflip_threshold_t *fixflip_threshold, IN fixflip_upc_t *ff_upc, IN uint32_t n_flips) {
    fixflip_threshold_t ff_threshold = {0};
    get_fixflip_threshold(&ff_threshold, ff_upc, n_flips);
    fixflip_threshold->threshold = ff_threshold.threshold;
}

uint32_t
flip_worst_fit_indexes(OUT split_e_t *e, IN fixflip_upc_t *ff_upc, IN uint32_t n_flips) {
    DEFER_CLEANUP(uint32_t vals[DV + 1] = {0}, vals_cleanup);

    fixflip_threshold_t ff_threshold = {0};
    get_fixflip_threshold(&ff_threshold, ff_upc, n_flips);

    uint8_t e_decomp[2 * R_BITS] = {0};
    decompress_e(e_decomp, e);

    uint32_t total_upc_counters_eq_threshold = ff_threshold.total_equal_threshold;
    uint64_t eq_flip_flags[N_FLIP_FLAGS_BLOCKS] = {0};
    init_eq_flip_flags(eq_flip_flags, &ff_threshold);
    secure_shuffle_eq_flip_flags(eq_flip_flags, &ff_threshold, total_upc_counters_eq_threshold);
    uint32_t current_eq_weight = 0;

    // The two variables bellow count the number of UPC counters that are found to be
    // equal and greater than the FixFlip threshold computed by get_fixflip_threshold.
    uint32_t n_found_eq_thresh = 0;
    uint32_t n_found_gt_thresh = 0;
    // By the end of the loop, it is expected that:
    //      n_found_eq_thresh = ff_threshold.n_equal_threshold
    //      n_found_gt_thresh + n_found_eq_thresh = n_flips

    uint32_t next_32_flags = 0;
    uint32_t base = 0;

    // Runs through all the 2*R_BITS UPC counters
    for (uint32_t i = 0; i < 2 * R_BITS; i++) {
        uint8_t counter = upc_for_index(ff_upc, i);

        if (i % 32 == 0) {
            next_32_flags = update_next32_flags(eq_flip_flags, current_eq_weight);
            base = 0;
        }
        // mask_gt assumes the following values:
        //      0 if the current counter is <= ff_threshold.threshold
        //      1 otherwise.
        uint32_t mask_gt = 1 + secure_l32_mask(ff_threshold.threshold, counter);
        n_found_gt_thresh += mask_gt;

        // mask_eq assumes the following values:
        //      0 if current counter is == ff_threshold.threshold AND if
        //           n_found_eq_thresh < ff_threshold.n_equal_threshold
        //      1 otherwise.
        // Therefore, it controls if the corresponding index `i` will be chosen to
        // flipped, when its counter is equal to the FixFlip threshold.
        //
        // Remember that this is done because we cannot flip all bits whose counter is equal
        // to the threshold, because we risk flipping more than n_flips bits.
        uint32_t mask_eq = secure_cmp32(counter, ff_threshold.threshold);


        uint64_t eq_flip_mask = get_randomized_eq_flip_mask(next_32_flags,
                                                            &base,
                                                            &current_eq_weight,
                                                            mask_eq);

        n_found_eq_thresh += eq_flip_mask;
        e_decomp[i] ^= (mask_gt | eq_flip_mask);
    }
    assert(n_found_eq_thresh == ff_threshold.n_equal_threshold);
    assert(n_found_gt_thresh == n_flips - ff_threshold.n_equal_threshold);

    compress_e(e, e_decomp);

    return ff_threshold.threshold;
}


#if (N_FLIP_FLAGS_BLOCKS > 4)
uint32_t compute_total_equal_threshold(fixflip_upc_t *ff_upc, uint8_t threshold) {
    uint32_t total = 0;
    for (uint32_t index = 0; index < 2 * R_BITS; index++) {
        uint32_t upc = upc_for_index(ff_upc, index);
        total += secure_cmp32(upc, threshold);
    }
    return total;
}
#endif

#else


uint32_t
flip_worst_fit_indexes(OUT split_e_t *e, IN fixflip_upc_t *ff_upc, IN uint32_t n_flips) {
    DEFER_CLEANUP(uint32_t vals[DV + 1] = {0}, vals_cleanup);

    fixflip_threshold_t ff_threshold = {0};
    get_fixflip_threshold(&ff_threshold, ff_upc, n_flips);

    uint8_t e_decomp[2 * R_BITS] = {0};
    decompress_e(e_decomp, e);

    // The two variables bellow count the number of UPC counters that are found to be
    // equal and greater than the FixFlip threshold computed by get_fixflip_threshold.
    uint32_t n_found_eq_thresh = 0;
    uint32_t n_found_gt_thresh = 0;
    // By the end of the loop, it is expected that:
    //      n_found_eq_thresh = ff_threshold.n_equal_threshold
    //      n_found_gt_thresh + n_found_eq_thresh = n_flips

    // Runs through all the 2*R_BITS UPC counters
    for (uint32_t i = 0; i < 2 * R_BITS; i++) {
        uint8_t counter = upc_for_index(ff_upc, i);

        // mask_gt assumes the following values:
        //      0 if the current counter is <= ff_threshold.threshold
        //      1 otherwise.
        uint32_t mask_gt = 1 + secure_l32_mask(ff_threshold.threshold, counter);
        n_found_gt_thresh += mask_gt;

        // mask_eq assumes the following values:
        //      0 if current counter is == ff_threshold.threshold AND if
        //           n_found_eq_thresh < ff_threshold.n_equal_threshold
        //      1 otherwise.
        // Therefore, it controls if the corresponding index `i` will be chosen to
        // flipped, when its counter is equal to the FixFlip threshold.
        //
        // Remember that this is done because we cannot flip all bits whose counter is equal
        // to the threshold, because we risk flipping more than n_flips bits.
        uint32_t mask_eq = secure_cmp32(counter, ff_threshold.threshold);
        mask_eq &= 1 + secure_l32_mask(n_found_eq_thresh, ff_threshold.n_equal_threshold);

        n_found_eq_thresh += mask_eq;
        e_decomp[i] ^= (mask_gt | mask_eq);
    }
    assert(n_found_eq_thresh == ff_threshold.n_equal_threshold);
    assert(n_found_gt_thresh == n_flips - ff_threshold.n_equal_threshold);

    compress_e(e, e_decomp);

    return ff_threshold.threshold;
}

#endif