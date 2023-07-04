#pragma once

#include "kem.h"
#include "types.h"

_INLINE_ void
split_e(OUT split_e_t *splitted_e, IN const e_t *e) {
    // Copy lower bytes (e0)
    memcpy(splitted_e->val[0].raw, e->raw, R_SIZE);

    // Now load second value
    for (uint32_t i = R_SIZE; i < N_SIZE; ++i) {
        splitted_e->val[1].raw[i - R_SIZE] =
            ((e->raw[i] << LAST_R_BYTE_TRAIL) | (e->raw[i - 1] >> LAST_R_BYTE_LEAD));
    }

    // Fix corner case
    if (N_SIZE < (2ULL * R_SIZE)) {
        splitted_e->val[1].raw[R_SIZE - 1] = (e->raw[N_SIZE - 1] >> LAST_R_BYTE_LEAD);
    }

    // Fix last value
    splitted_e->val[0].raw[R_SIZE - 1] &= LAST_R_BYTE_MASK;
    splitted_e->val[1].raw[R_SIZE - 1] &= LAST_R_BYTE_MASK;
}

_INLINE_ void
translate_hash_to_ss(OUT ss_t *ss, IN sha_hash_t *hash) {
    bike_static_assert(sizeof(*hash) >= sizeof(*ss), hash_size_lt_ss_size);
    memcpy(ss->raw, hash->u.raw, sizeof(*ss));
}

_INLINE_ void
translate_hash_to_seed(OUT seed_t *seed, IN sha_hash_t *hash) {
    bike_static_assert(sizeof(*hash) >= sizeof(*seed), hash_size_lt_seed_size);
    memcpy(seed->raw, hash->u.raw, sizeof(*seed));
}

_INLINE_ ret_t
calc_pk(OUT pk_t *pk, IN const seed_t *g_seed, IN const pad_sk_t p_sk) {
    // PK is dbl padded because modmul require some scratch space for the
    // multiplication result
    dbl_pad_pk_t p_pk = {0};

    // Intialized padding to zero
    DEFER_CLEANUP(padded_r_t g = {0}, padded_r_cleanup);

    GUARD(sample_uniform_r_bits(&g.val, g_seed, MUST_BE_ODD));

    // Calculate (g0, g1) = (g*h1, g*h0)
    GUARD(gf2x_mod_mul((uint64_t *)&p_pk[0], (const uint64_t *)&g, (const uint64_t *)&p_sk[1]));
    GUARD(gf2x_mod_mul((uint64_t *)&p_pk[1], (const uint64_t *)&g, (const uint64_t *)&p_sk[0]));

    // Copy the data to the output parameters.
    pk->val[0] = p_pk[0].val;
    pk->val[1] = p_pk[1].val;

    print("g:  ", (uint64_t *)g.val.raw, R_BITS);
    print("g0: ", (uint64_t *)&p_pk[0], R_BITS);
    print("g1: ", (uint64_t *)&p_pk[1], R_BITS);

    return SUCCESS;
}

// The function H is required by BIKE-1- Round 2 variant. It uses the
// extract-then-expand paradigm, based on SHA384 and AES256-CTR PRNG, to produce e
// from (m*f0, m*f1):
_INLINE_ ret_t
function_h(OUT split_e_t *splitted_e, IN const r_t *in0, IN const r_t *in1) {
    DEFER_CLEANUP(generic_param_n_t tmp, generic_param_n_cleanup);
    DEFER_CLEANUP(sha_hash_t hash_seed = {0}, sha_hash_cleanup);
    DEFER_CLEANUP(seed_t seed_for_hash, seed_cleanup);
    DEFER_CLEANUP(aes_ctr_prf_state_t prf_state = {0}, finalize_aes_ctr_prf);

    tmp.val[0] = *in0;
    tmp.val[1] = *in1;

    // Hash (m*f0, m*f1) to generate a seed:
    sha(&hash_seed, sizeof(tmp), (uint8_t *)&tmp);

    // Format the seed as a 32-bytes input:
    translate_hash_to_seed(&seed_for_hash, &hash_seed);

    // Use the seed to generate a sparse error vector e:
    DMSG("    Generating random error.\n");
    GUARD(init_aes_ctr_prf_state(&prf_state, MAX_AES_INVOKATION, &seed_for_hash));

    DEFER_CLEANUP(padded_e_t e, padded_e_cleanup);
    DEFER_CLEANUP(compressed_idx_t_t dummy, compressed_idx_t_cleanup);

    GUARD(generate_sparse_rep((uint64_t *)&e, dummy.val, T1_BIKE, N_BITS, sizeof(e), &prf_state));
    split_e(splitted_e, &e.val);

    return SUCCESS;
}

_INLINE_ ret_t
function_h_weighted(OUT split_e_t *splitted_e,
                    IN const r_t *in0,
                    IN const r_t *    in1,
                    IN const uint32_t weight) {
    DEFER_CLEANUP(generic_param_n_t tmp, generic_param_n_cleanup);
    DEFER_CLEANUP(sha_hash_t hash_seed = {0}, sha_hash_cleanup);
    DEFER_CLEANUP(seed_t seed_for_hash, seed_cleanup);
    DEFER_CLEANUP(aes_ctr_prf_state_t prf_state = {0}, finalize_aes_ctr_prf);

    tmp.val[0] = *in0;
    tmp.val[1] = *in1;

    // Hash (m*f0, m*f1) to generate a seed:
    sha(&hash_seed, sizeof(tmp), (uint8_t *)&tmp);

    // Format the seed as a 32-bytes input:
    translate_hash_to_seed(&seed_for_hash, &hash_seed);

    // Use the seed to generate a sparse error vector e:
    DMSG("    Generating random error.\n");
    GUARD(init_aes_ctr_prf_state(&prf_state, MAX_AES_INVOKATION, &seed_for_hash));

    DEFER_CLEANUP(padded_e_t e, padded_e_cleanup);
    DEFER_CLEANUP(compressed_idx_t_t dummy, compressed_idx_t_cleanup);

    GUARD(generate_sparse_rep((uint64_t *)&e, dummy.val, weight, N_BITS, sizeof(e), &prf_state));
    split_e(splitted_e, &e.val);

    return SUCCESS;
}

_INLINE_ void
get_ss(OUT ss_t *out, IN const r_t *in0, IN const r_t *in1, IN const ct_t *ct) {
    DMSG("    Enter get_ss.\n");

    uint8_t tmp[4 * R_SIZE];
    memcpy(tmp, in0->raw, R_SIZE);
    memcpy(tmp + R_SIZE, in1->raw, R_SIZE);
    memcpy(tmp + 2 * R_SIZE, ct, sizeof(*ct));

    // Calculate the hash digest
    DEFER_CLEANUP(sha_hash_t hash = {0}, sha_hash_cleanup);
    sha(&hash, sizeof(tmp), tmp);

    // Truncate the resulting digest, to produce the key K, by copying only the
    // desired number of LSBs.
    translate_hash_to_ss(out, &hash);

    secure_clean(tmp, sizeof(tmp));
    DMSG("    Exit get_ss.\n");
}
