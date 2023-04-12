#include "bike_defs.h"
#include "kem.h"
#include "measurements.h"
#include "utilities.h"
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <assert.h>

#ifdef USE_NIST_RAND
    #include "FromNIST/rng.h"
#endif

#ifdef BGF_DECODER
#    define BG_OR_BGF "BGF"
#elif defined(BG_DECODER)
#    define BG_OR_BGF "BG"
#endif

// Set to test BGF and PickyFix together
// #ifndef TEST_BGF
// #define TEST_BGF
// #endif

// #ifndef TEST_PICKYFIX
// #define TEST_PICKYFIX
// #endif

#if !defined(TEST_PICKYFIX) && !defined(TEST_BGF)
#define TEST_PICKYFIX
#endif


#ifdef AVX512
#define IMPLEMENTATION "avx512"
#elif defined(AVX2)
#define IMPLEMENTATION "avx2"
#else
#define IMPLEMENTATION "portable"
#endif

int
main(int argc, char *argv[]) {

    int hide_header = 0;
    if (argc > 1) {
        hide_header = atoi(argv[1]);
    }

    if (!hide_header)
        printf("implementation,decoder,level,n_iterations,r_bits,cycles\n");

    uint8_t sk[sizeof(sk_t)]    = {0}; // private-key: (h0, h1)
    uint8_t pk[sizeof(pk_t)]    = {0}; // public-key:  (g0, g1)
    uint8_t ct[sizeof(ct_t)]    = {0}; // ciphertext:  (c0, c1)
    uint8_t k_enc[sizeof(ss_t)] = {0}; // shared secret after encapsulate
    uint8_t k_dec[sizeof(ss_t)] = {0}; // shared secret after decapsulate

    int res = 0;
    res = crypto_kem_keypair(pk, sk);
    assert(res == SUCCESS);
    res = crypto_kem_enc(ct, k_enc, pk);
    assert(res == SUCCESS);

#ifdef TEST_PICKYFIX
    printf(IMPLEMENTATION ",PickyFix,%d,%d,%d,", LEVEL, MAX_IT, R_BITS);
    MEASURE(" ", res = crypto_kem_dec_pickyfix(k_dec, ct, sk););
    assert(res == SUCCESS);
#endif
#ifdef TEST_BGF
    printf(IMPLEMENTATION ",BGF,%d,%d,%d,", LEVEL, MAX_IT, R_BITS);
    MEASURE(" ", res = crypto_kem_dec_bgf(k_dec, ct, sk););
    assert(res == SUCCESS);
#endif

    return 0;
}
