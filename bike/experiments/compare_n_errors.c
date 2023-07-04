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

#include "decode_internals.h"
#include "pickyfix.h"
#include "kem_internals.h"

#include "experiments.h"

typedef struct error_pattern_s {
    double n_errors_corrected;
    double n_errors_added;
    double n_errors_left;
    double max_errors_left;
} error_pattern_t;

typedef enum {
    DEC_BGF = 0,
    DEC_PICKYFIX,
} Decoder;

int
get_diff_errors(split_e_t *e1, split_e_t *e2) {

    split_e_t d;
    memset(&d, 0, sizeof(d));

    int ret;
    ret = gf2x_add(d.val[0].raw, e1->val[0].raw, e2->val[0].raw, R_SIZE);
    assert(ret == SUCCESS);
    ret = gf2x_add(d.val[1].raw, e1->val[1].raw, e2->val[1].raw, R_SIZE);
    assert(ret == SUCCESS);

    return (r_bits_vector_weight(&d.val[0]) + r_bits_vector_weight(&d.val[1]));
}

ret_t
bgf_partial_decode(OUT split_e_t *e,
                   IN const syndrome_t *original_s,
                   IN const ct_t *ct,
                   IN const sk_t *sk) {
    split_e_t  black_e = {0};
    split_e_t  gray_e  = {0};
    syndrome_t s;

    // Reset (init) the error because it is xored in the find_err funcitons.
    memset(e, 0, sizeof(*e));
    s = *original_s;
    dup(&s);

    uint8_t threshold = get_threshold(&s);
    find_err1(e, &black_e, &gray_e, &s, sk->wlist, threshold);
    GUARD(recompute_syndrome(&s, ct, sk, e));

    find_err2(e, &black_e, &s, sk->wlist, ((DV + 1) / 2) + 1);
    GUARD(recompute_syndrome(&s, ct, sk, e));

    find_err2(e, &gray_e, &s, sk->wlist, ((DV + 1) / 2) + 1);
    GUARD(recompute_syndrome(&s, ct, sk, e));

    // 2nd and 3rd iterations below:
    // {
    // find_err1(e, &black_e, &gray_e, &s, sk->wlist, get_threshold(&s));
    // GUARD(recompute_syndrome(&s, ct, sk, e));
    // find_err1(e, &black_e, &gray_e, &s, sk->wlist, get_threshold(&s));
    // GUARD(recompute_syndrome(&s, ct, sk, e));
    // }

    return SUCCESS;
}

ret_t
pickyfix_partial_decode(OUT split_e_t *e,
                       IN const syndrome_t *original_s,
                       IN const ct_t *ct,
                       IN const sk_t *sk,
                       int            nflips) {
    syndrome_t s;

    memset(e, 0, sizeof(*e));
    s = *original_s;
    dup(&s);

    GUARD(fixflip_iter(e, &s, nflips, ct, sk));
    GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));
    GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));

    return SUCCESS;
}

void
get_errors(error_pattern_t *errors, int tgt_weight, Decoder dec, int nflips) {
    uint8_t sk[sizeof(sk_t)]    = {0}; // private-key: (h0, h1)
    uint8_t pk[sizeof(pk_t)]    = {0}; // public-key:  (g0, g1)
    uint8_t ct[sizeof(ct_t)]    = {0}; // ciphertext:  (c0, c1)
    uint8_t k_enc[sizeof(ss_t)] = {0}; // shared secret after encapsulate

    split_e_t e;

    int res = 1;
    while (res != 0) {
        res = crypto_kem_keypair(pk, sk);
    }

    syndrome_t syndrome = {0};

    res = get_challenge(&e, &syndrome, ct, k_enc, sk, pk, tgt_weight);

    const sk_t *l_sk = (const sk_t *)sk;
    const ct_t *l_ct = (const ct_t *)ct;

    split_e_t e_partial;

    if (dec == DEC_BGF)
        assert(bgf_partial_decode(&e_partial, &syndrome, l_ct, l_sk) == SUCCESS);
    else
        assert(pickyfix_partial_decode(&e_partial, &syndrome, l_ct, l_sk, nflips) == SUCCESS);

    int weight_added =
        r_bits_vector_weight(&e_partial.val[0]) + r_bits_vector_weight(&e_partial.val[1]);

    int errors_xor = get_diff_errors(&e, &e_partial);
    // fprintf(stderr, "errors_xor = %d\n", errors_xor);

    errors->n_errors_corrected = (tgt_weight + weight_added - errors_xor) / 2;
    errors->n_errors_added     = weight_added - errors->n_errors_corrected;
    errors->n_errors_left      = errors_xor;

    // fprintf(stderr, "weight_added = %ld\n", weight_added);
    // fprintf(stderr, "errors->n_errors_corrected = %lf\n",
    // errors->n_errors_corrected); fprintf(stderr, "errors->n_errors_added =
    // %lf\n", errors->n_errors_added); fprintf(stderr, "errors->n_errors_left =
    // %lf\n", errors->n_errors_left); fprintf(stderr, "tgt_weight = %d\n",
    // tgt_weight);

    assert(errors->n_errors_corrected - errors->n_errors_added + errors->n_errors_left ==
           tgt_weight);
}

void
get_average_errors(error_pattern_t *av_errors,
                   int              n_tests,
                   int              tgt_weight,
                   Decoder          dec,
                   int              nflips) {

    double sum_errors_corrected = 0;
    double sum_errors_added     = 0;
    double sum_errors_left      = 0;
    double max_errors_left      = 0;

    for (int i = 0; i < n_tests; i++) {
        error_pattern_t errors;
        get_errors(&errors, tgt_weight, dec, nflips);

        sum_errors_corrected += errors.n_errors_corrected;
        sum_errors_added += errors.n_errors_added;
        sum_errors_left += errors.n_errors_left;
        max_errors_left = MAX(errors.n_errors_left, max_errors_left);
    }

    av_errors->n_errors_corrected = sum_errors_corrected / n_tests;
    av_errors->n_errors_added     = sum_errors_added / n_tests;
    av_errors->n_errors_left      = sum_errors_left / n_tests;
    av_errors->max_errors_left    = max_errors_left;
}

void
usage_error(char *argv[]) {
    fprintf(stderr, "Usage: %s <n_tests> <seed> <quiet>\n", argv[0]);
    exit(1);
}

int
main(int argc, char *argv[]) {

    if (argc < 4)
        usage_error(argv);

    int n_tests = atoi(argv[1]);
    int seed    = atoi(argv[2]);
    int quiet   = atoi(argv[3]);
    srand(seed);

    if (quiet == 0) {
        printf("LEVEL,R_BITS,T1_BIKE,decoder,nflips,av_errors_left,max_errors_left,n_tests\n");
    }
    // BGF
    {
        error_pattern_t av_errors = {0};
        get_average_errors(&av_errors, n_tests, T1_BIKE, DEC_BGF, 0);
        printf("%d,%d,%d,BGF,NA,%lf,%lf,%d\n", LEVEL, R_BITS, T1_BIKE, av_errors.n_errors_left,
               av_errors.max_errors_left, n_tests);
    }

    error_pattern_t av_errors = {0};
    for (int nflips = 5; nflips <= MIN(T1_BIKE, 200); nflips += 5) {
        get_average_errors(&av_errors, n_tests, T1_BIKE, DEC_PICKYFIX, nflips);
        printf("%d,%d,%d,PickyFix,%d,%lf,%lf,%d\n", LEVEL, R_BITS, T1_BIKE, nflips, av_errors.n_errors_left,
               av_errors.max_errors_left, n_tests);
        fflush(stdout);
    }
    return 0;
}