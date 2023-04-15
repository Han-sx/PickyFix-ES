/*


for i in `seq 0 41`; do
  r_bits=$((9001 + i*100))
  echo $r_bits
  make clean; make CC=gcc LEVEL=1 AVX512=1 TEST_pickyfix=1 R_BITS=$r_bits threshold
  ./bin/threshold 10000 $i $i >> threshold/level1.csv
done


for i in `seq 0 21`; do
  r_bits=$((19001 + i*200))
  echo $r_bits
  make clean; make CC=gcc LEVEL=3 AVX512=1 TEST_pickyfix=1 R_BITS=$r_bits threshold
  ./bin/threshold 100 $i $i >> threshold/level3.csv
done

for i in `seq 0 31`; do
  r_bits=$((32001 + i*400))
  echo $r_bits
  make clean; make CC=gcc LEVEL=5 AVX512=1 TEST_pickyfix=1 R_BITS=$r_bits threshold
  ./bin/threshold 100 $i $i >> threshold/level5.csv
done

*/

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


#if !defined(TEST_PICKYFIX) && !defined(TEST_BGF)
#define TEST_BGF
#endif


typedef struct error_pattern_s {
    double n_errors_corrected;
    double n_errors_added;
    double n_errors_left;
} error_pattern_t;

ret_t
pickyfix_partial_decode_thresholds(OUT split_e_t *e,
                                  IN const syndrome_t *original_s,
                                  IN const ct_t *ct,
                                  IN const sk_t *sk) {
    syndrome_t s;

    memset(e, 0, sizeof(*e));
    s = *original_s;
    dup(&s);

    printf("%d,%d,%d,pickyfix,%d,", LEVEL, R_BITS, T1_BIKE, MAX_IT);
    for (int i = 0; i < MAX_IT; i++) {
        if (i == 0) {
            GUARD(fixflip_iter(e, &s, FIXFLIP_HEAD_N_FLIPS, ct, sk));

            int th = get_threshold(&s);
            printf("%d ", th);
            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));

            th = get_threshold(&s);
            printf("%d ", th);
            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));
        } else {
            int th = get_threshold(&s);
            printf("%d ", th);
            GUARD(pickyflip_iter(e, &s, get_threshold(&s), (DV + 1) / 2, ct, sk));
        }
    }
    printf("\n");

    return SUCCESS;
}

ret_t
bgf_partial_decode_thresholds(OUT split_e_t *e,
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

    printf("%d,%d,%d,BGF,%d,", LEVEL, R_BITS, T1_BIKE, MAX_IT);

    for (int i = 0; i < MAX_IT; i++) {

        int th = get_threshold(&s);
        if (i == 0) {
            find_err1(e, &black_e, &gray_e, &s, sk->wlist, th);
            GUARD(recompute_syndrome(&s, ct, sk, e));

            find_err2(e, &black_e, &s, sk->wlist, ((DV + 1) / 2) + 1);
            GUARD(recompute_syndrome(&s, ct, sk, e));

            find_err2(e, &gray_e, &s, sk->wlist, ((DV + 1) / 2) + 1);
            GUARD(recompute_syndrome(&s, ct, sk, e));
        } else {
            find_err1(e, &black_e, &gray_e, &s, sk->wlist, th);
            GUARD(recompute_syndrome(&s, ct, sk, e));
        }

        printf("%d ", th);
    }
    printf("\n");
    return SUCCESS;
}

void
usage_error(char *argv[]) {
    fprintf(stderr, "Usage: %s <n_tests> <seed> <quiet>\n", argv[0]);
    exit(1);
}

void
show_thresholds() {
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

    res = get_challenge(&e, &syndrome, ct, k_enc, sk, pk, T1_BIKE);

    const sk_t *l_sk = (const sk_t *)sk;
    const ct_t *l_ct = (const ct_t *)ct;


#ifdef TEST_PICKYFIX
    split_e_t e_partial_ff;
    assert(pickyfix_partial_decode_thresholds(&e_partial_ff, &syndrome, l_ct, l_sk) == SUCCESS);
#endif
#ifdef TEST_BGF
    split_e_t e_partial_bgf;
    assert(bgf_partial_decode_thresholds(&e_partial_bgf, &syndrome, l_ct, l_sk) == SUCCESS);
#endif

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
        printf("LEVEL,R_BITS,T1,decoder,MAX_IT,thresholds\n");
    }
    for (int i = 0; i < n_tests; i++) {
        show_thresholds();
    }
    return 0;
}
