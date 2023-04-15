#include "bike_defs.h"
#include "kem.h"
#include "measurements.h"
#include "utilities.h"
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

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

typedef enum {
    DEC_BGF = 0,
    DEC_PICKYFIX,
} Decoder;

uint32_t
get_n_errors_for_decoding_challenge(Decoder dec,
                                    uint8_t k_enc[],
                                    uint8_t k_dec[],
                                    uint8_t ct[],
                                    uint8_t sk[],
                                    int     measure_flag) {
    int dec_rc = 0;

    if (measure_flag) {
        switch (dec) {
            case DEC_BGF:
                MEASURE("  decaps bgf    ", dec_rc = crypto_kem_dec_bgf(k_dec, ct, sk););
                break;
            case DEC_PICKYFIX:
                MEASURE("  decaps pickyfix", dec_rc = crypto_kem_dec_pickyfix(k_dec, ct, sk););
                break;
        }
    } else {
        switch (dec) {
            case DEC_BGF:
                dec_rc = crypto_kem_dec_bgf(k_dec, ct, sk);
                break;
            case DEC_PICKYFIX:
                dec_rc = crypto_kem_dec_pickyfix(k_dec, ct, sk);
                break;
        }
    }

    if (dec_rc != SUCCESS || (!secure_cmp(k_enc, k_dec, sizeof(ss_t) / sizeof(uint64_t)))) {
        return 1;
    }

    return 0;
}

int
main(int argc, char *argv[]) {

    if (argc != 4 && argc != 5) {
        fprintf(stderr,
                "Usage: %s <number of tests> <seed> <number of threads> [measure "
                "time (true|False)]\n",
                argv[0]);
        exit(1);
    }

    uint32_t ntests = atoi(argv[1]);

    srand(atoi(argv[2]));

#ifdef USE_NIST_RAND
    unsigned char entropy_input[48];

    for (int i = 0; i < 48; i++)
        entropy_input[i] = rand();

    randombytes_init(entropy_input, NULL, 256);
#endif


    int nthreads = atoi(argv[3]);
    omp_set_num_threads(nthreads);

    uint32_t final_nerrors_bgf      = 0;
    uint32_t final_nerrors_pickyfix = 0;

    int measure_flag = 0;
    if (argc == 5) {
        measure_flag = ((argv[4][0] == 'T') || (argv[4][0] == 't')) ? 1 : 0;
    }
    printf("decoder,n_iterations,level,r_bits,error_weight,n_failures,n_tests\n");
#pragma omp parallel for schedule(static)
    for (int i_thread = 0; i_thread < nthreads; i_thread++) {
        uint32_t nruns = ntests / nthreads;
        if (i_thread == 0)
            nruns += ntests % nthreads;

        uint32_t nerrors_bgf      = 0;
        uint32_t nerrors_pickyfix = 0;

        for (uint32_t i = 1; i <= nruns; i++) {

            uint8_t sk[sizeof(sk_t)]    = {0}; // private-key: (h0, h1)
            uint8_t pk[sizeof(pk_t)]    = {0}; // public-key:  (g0, g1)
            uint8_t ct[sizeof(ct_t)]    = {0}; // ciphertext:  (c0, c1)
            uint8_t k_enc[sizeof(ss_t)] = {0}; // shared secret after encapsulate
            uint8_t k_dec[sizeof(ss_t)] = {0}; // shared secret after decapsulate

            int res = 0;

            // Key generation
            // MEASURE("  keypair", res = crypto_kem_keypair(pk, sk););
            res = crypto_kem_keypair(pk, sk);

            if (res != 0)
                continue;

#ifdef TEST_BGF
            res = crypto_kem_enc(ct, k_enc, pk);
            if (res != 0)
                continue;
            nerrors_bgf +=
                get_n_errors_for_decoding_challenge(DEC_BGF, k_enc, k_dec, ct, sk, measure_flag);
#endif
#ifdef TEST_PICKYFIX
            res = crypto_kem_enc(ct, k_enc, pk);
            if (res != 0)
                continue;
            nerrors_pickyfix += get_n_errors_for_decoding_challenge(DEC_PICKYFIX, k_enc, k_dec, ct,
                                                                    sk, measure_flag);
#endif

            if ((i % 1000) == 0) {
#ifdef TEST_BGF
                fprintf(stderr, BG_OR_BGF ",%d,%d,%d,%d,%d,%d,thread%d\n", MAX_IT, LEVEL, R_BITS,
                        T1_BIKE, nerrors_bgf, i, i_thread);
#endif
#ifdef TEST_PICKYFIX
                fprintf(stderr, "PickyFix,%d,%d,%d,%d,%d,%d,thread%d\n", MAX_IT, LEVEL, R_BITS, T1_BIKE,
                        nerrors_pickyfix, i, i_thread);

#endif
            }
        }
#pragma omp critical
        {
            final_nerrors_bgf += nerrors_bgf;
            final_nerrors_pickyfix += nerrors_pickyfix;
        }

    }

    // decoder,n_iterations,level,r_bits,n_failures,n_tests
#ifdef TEST_BGF
    printf(BG_OR_BGF ",%d,%d,%d,%d,%d,%d\n", MAX_IT, LEVEL, R_BITS, T1_BIKE, final_nerrors_bgf, ntests);
#endif
#ifdef TEST_PICKYFIX
    printf("PickyFix,%d,%d,%d,%d,%d,%d\n", MAX_IT, LEVEL, R_BITS, T1_BIKE, final_nerrors_pickyfix,
           ntests);
#endif

    return 0;
}
