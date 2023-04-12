#pragma once

#include "gf2x.h"
#include "types.h"

/*
 *   Below, you'll find some static functions extracted from decode/decode.c.
 *
 *   The code below is already part of BIKE additional implementation.
 *   As such, it was written by Nir Drucker, Shay Gueron, and Dusan Kostic,
 *   AWS Cryptographic Algorithms Group.
 *   (ndrucker@amazon.com, gueron@amazon.com, dkostic@amazon.com)
 *
 */

_INLINE_ void
dup(IN OUT syndrome_t *s) {
    s->qw[R_QW - 1] = (s->qw[0] << LAST_R_QW_LEAD) | (s->qw[R_QW - 1] & LAST_R_QW_MASK);

    for (size_t i = 0; i < (2 * R_QW) - 1; i++) {
        s->qw[R_QW + i] = (s->qw[i] >> LAST_R_QW_TRAIL) | (s->qw[i + 1] << LAST_R_QW_LEAD);
    }
}

_INLINE_ ret_t
recompute_syndrome(OUT syndrome_t *syndrome,
                   IN const ct_t *ct,
                   IN const sk_t *sk,
                   IN const split_e_t *splitted_e) {
    ct_t tmp_ct = *ct;

    // Adapt the ciphertext
    GUARD(gf2x_add(tmp_ct.val[0].raw, tmp_ct.val[0].raw, splitted_e->val[0].raw, R_SIZE));
    GUARD(gf2x_add(tmp_ct.val[1].raw, tmp_ct.val[1].raw, splitted_e->val[1].raw, R_SIZE));

    // Recompute the syndrome
    GUARD(compute_syndrome(syndrome, &tmp_ct, sk));

    return SUCCESS;
}

// Use half-adder as described in [5].
_INLINE_ void
bit_sliced_adder(OUT upc_t *upc,
                 IN OUT syndrome_t *rotated_syndrome,
                 IN const size_t    num_of_slices) {
    // From cache-memory perspective this loop should be the outside loop
    for (size_t j = 0; j < num_of_slices; j++) {
        for (size_t i = 0; i < R_QW; i++) {
            const uint64_t carry = (upc->slice[j].u.qw[i] & rotated_syndrome->qw[i]);
            upc->slice[j].u.qw[i] ^= rotated_syndrome->qw[i];
            rotated_syndrome->qw[i] = carry;
        }
    }
}

_INLINE_ void
bit_slice_full_subtract(OUT upc_t *upc, IN uint8_t val) {
    // Borrow
    uint64_t br[R_QW] = {0};

    for (size_t j = 0; j < SLICES; j++) {

        const uint64_t lsb_mask = 0 - (val & 0x1);
        val >>= 1;

        // Perform a - b with c as the input/output carry
        // br = 0 0 0 0 1 1 1 1
        // a  = 0 0 1 1 0 0 1 1
        // b  = 0 1 0 1 0 1 0 1
        // -------------------
        // o  = 0 1 1 0 0 1 1 1
        // c  = 0 1 0 0 1 1 0 1
        //
        // o  = a^b^c
        //            _     __    _ _   _ _     _
        // br = abc + abc + abc + abc = abc + ((a+b))c

        for (size_t i = 0; i < R_QW; i++) {
            const uint64_t a      = upc->slice[j].u.qw[i];
            const uint64_t b      = lsb_mask;
            const uint64_t tmp    = ((~a) & b & (~br[i])) | ((((~a) | b) & br[i]));
            upc->slice[j].u.qw[i] = a ^ b ^ br[i];
            br[i]                 = tmp;
        }
    }
}

// Calculate the Unsatisfied Parity Checks (UPCs) and update the errors
// vector (e) accordingy. In addition, update the black and gray errors vector
// with the relevant values.

_INLINE_ void
find_err1(OUT split_e_t *e,
          OUT split_e_t *black_e,
          OUT split_e_t *gray_e,
          IN const syndrome_t *           syndrome,
          IN const compressed_idx_dv_ar_t wlist,
          IN const uint8_t                threshold) {
    // This function uses the bit-slice-adder methodology of [5]:
    DEFER_CLEANUP(syndrome_t rotated_syndrome = {0}, syndrome_cleanup);
    DEFER_CLEANUP(upc_t upc, upc_cleanup);

    for (uint32_t i = 0; i < N0; i++) {
        // UPC must start from zero at every iteration
        memset(&upc, 0, sizeof(upc));

        // 1) Right-rotate the syndrome for every secret key set bit index
        //    Then slice-add it to the UPC array.
        for (size_t j = 0; j < DV; j++) {
            rotate_right(&rotated_syndrome, syndrome, wlist[i].val[j]);
            bit_sliced_adder(&upc, &rotated_syndrome, LOG2_MSB(j + 1));
        }

        // 2) Subtract the threshold from the UPC counters
        bit_slice_full_subtract(&upc, threshold);

        // 3) Update the errors and the black errors vectors.
        //    The last slice of the UPC array holds the MSB of the accumulated
        //    values minus the threshold. Every zero bit indicates a potential
        //    error bit. The errors values are stored in the black array and xored
        //    with the errors Of the previous iteration.
        const r_t *last_slice = &(upc.slice[SLICES - 1].u.r.val);
        for (size_t j = 0; j < R_SIZE; j++) {
            const uint8_t sum_msb  = (~last_slice->raw[j]);
            black_e->val[i].raw[j] = sum_msb;
            e->val[i].raw[j] ^= sum_msb;
        }

        // Ensure that the padding bits (upper bits of the last byte) are zero so
        // they will not be included in the multiplication and in the hash
        // function.
        e->val[i].raw[R_SIZE - 1] &= LAST_R_BYTE_MASK;

        // 4) Calculate the gray error array by adding "DELTA" to the UPC array.
        //    For that we reuse the rotated_syndrome variable setting it to all
        //    "1".
        for (size_t l = 0; l < DELTA; l++) {
            memset((uint8_t *)rotated_syndrome.qw, 0xff, R_SIZE);
            bit_sliced_adder(&upc, &rotated_syndrome, SLICES);
        }

        // 5) Update the gray list with the relevant bits that are not
        //    set in the black list.
        for (size_t j = 0; j < R_SIZE; j++) {
            const uint8_t sum_msb = (~last_slice->raw[j]);
            gray_e->val[i].raw[j] = (~(black_e->val[i].raw[j])) & sum_msb;
        }
    }
}

// Recalculate the UPCs and update the errors vector (e) according to it
// and to the black/gray vectors.
_INLINE_ void
find_err2(OUT split_e_t *e,
          IN split_e_t *pos_e,
          IN const syndrome_t *           syndrome,
          IN const compressed_idx_dv_ar_t wlist,
          IN const uint8_t                threshold) {
    DEFER_CLEANUP(syndrome_t rotated_syndrome = {0}, syndrome_cleanup);
    DEFER_CLEANUP(upc_t upc, upc_cleanup);

    for (uint32_t i = 0; i < N0; i++) {
        // UPC must start from zero at every iteration
        memset(&upc, 0, sizeof(upc));

        // 1) Right-rotate the syndrome for every secret key set bit index
        //    Then slice-add it to the UPC array.
        for (size_t j = 0; j < DV; j++) {
            rotate_right(&rotated_syndrome, syndrome, wlist[i].val[j]);
            bit_sliced_adder(&upc, &rotated_syndrome, LOG2_MSB(j + 1));
        }

        // 2) Subtract the threshold from the UPC counters
        bit_slice_full_subtract(&upc, threshold);

        // 3) Update the errors vector.
        //    The last slice of the UPC array holds the MSB of the accumulated
        //    values minus the threshold. Every zero bit indicates a potential
        //    error bit.
        const r_t *last_slice = &(upc.slice[SLICES - 1].u.r.val);
        for (size_t j = 0; j < R_SIZE; j++) {
            const uint8_t sum_msb = (~last_slice->raw[j]);
            e->val[i].raw[j] ^= (pos_e->val[i].raw[j] & sum_msb);
        }

        // Ensure that the padding bits (upper bits of the last byte) are zero so
        // they will not be included in the multiplication and in the hash
        // function.
        e->val[i].raw[R_SIZE - 1] &= LAST_R_BYTE_MASK;
    }
}

_INLINE_ uint8_t
get_threshold(IN const syndrome_t *s) {
    bike_static_assert(sizeof(*s) >= sizeof(r_t), syndrome_is_large_enough);

    const uint32_t syndrome_weight = r_bits_vector_weight((const r_t *)s->qw);

    // The equations below are defined in BIKE's specification:
    // https://bikesuite.org/files/round2/spec/BIKE-Spec-Round2.2019.03.30.pdf
    // Page 20 Section 2.4.2
    const uint8_t threshold =
        max32(THRESHOLD_COEFF0 + (THRESHOLD_COEFF1 * syndrome_weight), THRESHOLD_LOWER_LIMIT);

    DMSG("    Threshold: %d\n", threshold);
    return threshold;
}

// This functions is based on find_err1 from BIKE's additional implementation.
// We kept the original author's comments.
_INLINE_ ret_t
bitflip_iter(OUT split_e_t *e,
             IN syndrome_t *  syndrome,
             IN const uint8_t threshold,
             IN const ct_t *ct,
             IN const sk_t *sk) {
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
        bit_slice_full_subtract(&upc, threshold);

        // 3) Update the errors and the black errors vectors.
        //    The last slice of the UPC array holds the MSB of the accumulated
        //    values minus the threshold. Every zero bit indicates a potential
        //    error bit. The errors values are stored in the black array and xored
        //    with the errors Of the previous iteration.
        const r_t *last_slice = &(upc.slice[SLICES - 1].u.r.val);
        for (size_t j = 0; j < R_SIZE; j++) {
            const uint8_t sum_msb = (~last_slice->raw[j]);
            e->val[i].raw[j] ^= sum_msb;
        }

        // Ensure that the padding bits (upper bits of the last byte) are zero so
        // they will not be included in the multiplication and in the hash
        // function.
        e->val[i].raw[R_SIZE - 1] &= LAST_R_BYTE_MASK;

        // 4) Calculate the gray error array by adding "DELTA" to the UPC array.
        //    For that we reuse the rotated_syndrome variable setting it to all
        //    "1".
        for (size_t l = 0; l < DELTA; l++) {
            memset((uint8_t *)rotated_syndrome.qw, 0xff, R_SIZE);
            bit_sliced_adder(&upc, &rotated_syndrome, SLICES);
        }
    }
    GUARD(recompute_syndrome(syndrome, ct, sk, e));
    return SUCCESS;
}