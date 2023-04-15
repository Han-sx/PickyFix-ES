#include "bike_defs.h"
#include "kem.h"
#include "measurements.h"
#include "utilities.h"
#include <assert.h>
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "decode.h"
#include "gf2x.h"
#include "sampling.h"
#include "sha.h"

#include "pickyfix.h"

#include "decode_internals.h"
#include "kem_internals.h"

ret_t
get_separate_counters(OUT int counters_right[],
                      OUT int counters_wrong[],
                      IN split_e_t *true_error,
                      IN const syndrome_t *original_s,
                      IN const sk_t *sk) {
    syndrome_t s;

    s = *original_s;
    dup(&s);

    fixflip_upc_t ff_upc;
    memset(&ff_upc, 0, sizeof(ff_upc));

    get_upc(&ff_upc, &s, sk->wlist);

    uint8_t decomp_e[2 * R_BITS] = {0};

    decompress_e(decomp_e, true_error);

    for (int i = 0; i < 2 * R_BITS; i++) {
        if (decomp_e[i] == 0) {
            counters_right[upc_for_index(&ff_upc, i)]++;
        } else {
            counters_wrong[upc_for_index(&ff_upc, i)]++;
        }
    }

    return SUCCESS;
}

_INLINE_ ret_t
encrypt_and_return_e(OUT split_e_t *e,
                     OUT ct_t *ct,
                     OUT split_e_t *mf,
                     IN const pk_t *pk,
                     IN const seed_t *seed) {
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
    GUARD(function_h(&splitted_e, &mf_int[0].val, &mf_int[1].val));

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

_INLINE_ ret_t
get_challenge(OUT split_e_t *e,
              OUT syndrome_t *        s,
              OUT unsigned char *     ct,
              OUT unsigned char *     ss,
              IN const unsigned char *sk,
              IN const unsigned char *pk) {
    const pk_t *l_pk = (const pk_t *)pk;
    ct_t *      l_ct = (ct_t *)ct;
    ss_t *      l_ss = (ss_t *)ss;

    DEFER_CLEANUP(seeds_t seeds = {0}, seeds_cleanup);

    get_seeds(&seeds);

    DEFER_CLEANUP(split_e_t mf, split_e_cleanup);
    GUARD(encrypt_and_return_e(e, l_ct, &mf, l_pk, &seeds.seed[1]));

    DMSG("    Generating shared secret.\n");
    get_ss(l_ss, &mf.val[0], &mf.val[1], l_ct);

    print("ss: ", (uint64_t *)l_ss->raw, SIZEOF_BITS(*l_ss));
    DMSG("  Exit crypto_kem_enc.\n");

    const sk_t *l_sk = (const sk_t *)sk;
    // const ct_t * = (const ct_t *)ct;

    GUARD(compute_syndrome(s, l_ct, l_sk));

    return SUCCESS;
}

int
main(int argc, char *argv[]) {

    if (argc != 2) {
        fprintf(stderr, "Usage: %s <n_tests>\n", argv[0]);
        exit(1);
    }

    int n_tests = atoi(argv[1]);

    printf("level,r_bits,error_weight,test,counter,n_right,n_wrong\n");
    for (int i = 0; i < n_tests; i++) {

        uint8_t sk[sizeof(sk_t)]    = {0}; // private-key: (h0, h1)
        uint8_t pk[sizeof(pk_t)]    = {0}; // public-key:  (g0, g1)
        uint8_t ct[sizeof(ct_t)]    = {0}; // ciphertext:  (c0, c1)
        uint8_t k_enc[sizeof(ss_t)] = {0}; // shared secret after encapsulate

        int res = 0;

        split_e_t e;

        res = crypto_kem_keypair(pk, sk);

        if (res != 0)
            continue;

        syndrome_t syndrome = {0};

        res = get_challenge(&e, &syndrome, ct, k_enc, sk, pk);

        const sk_t *l_sk = (const sk_t *)sk;

        int counters_right[DV + 1] = {0};
        int counters_wrong[DV + 1] = {0};

        printf("#%d,threshold=%d\n", i, get_threshold(&syndrome));
        assert(get_separate_counters(counters_right, counters_wrong, &e, &syndrome, l_sk) ==
               SUCCESS);

        for (int k = 0; k < DV + 1; k++) {
            printf("%d,%d,%d,%d,%d,%d,%d\n", LEVEL, R_BITS, T1_BIKE, i, k, counters_right[k],
                   counters_wrong[k]);
        }
    }
    return 0;
}
