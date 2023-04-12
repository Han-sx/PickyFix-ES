#pragma once

#include "defs.h"

#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MAX(a, b) ((a) > (b) ? (a) : (b))

ret_t
encrypt_and_return_e_weighted(OUT split_e_t *e,
                              OUT ct_t *ct,
                              OUT split_e_t *mf,
                              IN const pk_t *pk,
                              IN const seed_t * seed,
                              IN const uint32_t weight) {
    DEFER_CLEANUP(padded_r_t m = {0}, padded_r_cleanup);

    DMSG("    Sampling m.\n");
    GUARD(sample_uniform_r_bits(&m.val, seed, NO_RESTRICTION));

    // Pad the public key
    pad_pk_t p_pk = {0};
    p_pk[0].val   = pk->val[0];
    p_pk[1].val   = pk->val[1];

    // Pad the ciphertext
    pad_ct_t p_ct = {0};
    p_ct[0].val   = ct->val[0];
    p_ct[1].val   = ct->val[1];

    DEFER_CLEANUP(dbl_pad_ct_t mf_int = {0}, dbl_pad_ct_cleanup);

    DMSG("    Computing m*f0 and m*f1.\n");
    GUARD(gf2x_mod_mul((uint64_t *)&mf_int[0], (uint64_t *)&m, (uint64_t *)&p_pk[0]));
    GUARD(gf2x_mod_mul((uint64_t *)&mf_int[1], (uint64_t *)&m, (uint64_t *)&p_pk[1]));

    DEFER_CLEANUP(split_e_t splitted_e, split_e_cleanup);

    DMSG("    Computing the hash function e <- H(m*f0, m*f1).\n");
    GUARD(function_h_weighted(&splitted_e, &mf_int[0].val, &mf_int[1].val, weight));

    DMSG("    Addding Error to the ciphertext.\n");
    GUARD(gf2x_add(p_ct[0].val.raw, mf_int[0].val.raw, splitted_e.val[0].raw, R_SIZE));
    GUARD(gf2x_add(p_ct[1].val.raw, mf_int[1].val.raw, splitted_e.val[1].raw, R_SIZE));

    // Copy the data to the output parameters.
    ct->val[0] = p_ct[0].val;
    ct->val[1] = p_ct[1].val;

    // Copy the internal mf to the output parameters.
    mf->val[0] = mf_int[0].val;
    mf->val[1] = mf_int[1].val;

    print("e0: ", (uint64_t *)splitted_e.val[0].raw, R_BITS);
    print("e1: ", (uint64_t *)splitted_e.val[1].raw, R_BITS);
    print("c0: ", (uint64_t *)p_ct[0].val.raw, R_BITS);
    print("c1: ", (uint64_t *)p_ct[1].val.raw, R_BITS);

    memcpy(e, &splitted_e, sizeof(splitted_e));

    return SUCCESS;
}

ret_t
get_challenge(OUT split_e_t *e,
              OUT syndrome_t *        s,
              OUT unsigned char *     ct,
              OUT unsigned char *     ss,
              IN const unsigned char *sk,
              IN const unsigned char *pk,
              IN uint32_t             weight) {
    const pk_t *l_pk = (const pk_t *)pk;
    ct_t *      l_ct = (ct_t *)ct;
    ss_t *      l_ss = (ss_t *)ss;

    DEFER_CLEANUP(seeds_t seeds = {0}, seeds_cleanup);

    get_seeds(&seeds);

    DEFER_CLEANUP(split_e_t mf, split_e_cleanup);
    GUARD(encrypt_and_return_e_weighted(e, l_ct, &mf, l_pk, &seeds.seed[1], weight));

    DMSG("    Generating shared secret.\n");
    get_ss(l_ss, &mf.val[0], &mf.val[1], l_ct);

    print("ss: ", (uint64_t *)l_ss->raw, SIZEOF_BITS(*l_ss));
    DMSG("  Exit crypto_kem_enc.\n");

    const sk_t *l_sk = (const sk_t *)sk;
    // const ct_t * = (const ct_t *)ct;

    GUARD(compute_syndrome(s, l_ct, l_sk));

    return SUCCESS;
}