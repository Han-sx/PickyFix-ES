/*
 * Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 * http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 * The license is detailed in the file LICENSE.md, and applies to this file.
 *
 * Written by Nir Drucker and Shay Gueron
 * AWS Cryptographic Algorithms Group.
 * (ndrucker@amazon.com, gueron@amazon.com)
 */

#pragma once

#include "defs.h"

////////////////////////////////////////////
//             BIKE Parameters
///////////////////////////////////////////
#define N0 2

#ifndef LEVEL
#    define LEVEL 1
#endif

#if (LEVEL == 5)
// 128-bits of post-quantum security parameters (BIKE paper):
#    ifndef R_BITS
#        define R_BITS 40973
#    endif

#    define DV 137

#    ifndef T1
#        define T1 264
#    endif

#    define THRESHOLD_COEFF0      17.8785
#    define THRESHOLD_COEFF1      0.00402312
#    define THRESHOLD_LOWER_LIMIT 69

// The gfm code is optimized to a block size in this case:
#    define BLOCK_SIZE (32768 * 2)
#elif (LEVEL == 3)

#    ifndef R_BITS
#        define R_BITS 24659
#    endif

#    define DV 103

#    ifndef T1
#        define T1 199
#    endif

#    define THRESHOLD_COEFF0      15.2588
#    define THRESHOLD_COEFF1      0.005265
#    define THRESHOLD_LOWER_LIMIT 52

// The gfm code is optimized to a block size in this case:
#    define BLOCK_SIZE            32768
#elif (LEVEL == 1)
// 64-bits of post-quantum security parameters (BIKE paper):

#    ifndef R_BITS
#        define R_BITS 12323
#    endif

#    define DV 71

#    ifndef T1
#        define T1 134
#    endif

#    define THRESHOLD_COEFF0      13.530
#    define THRESHOLD_COEFF1      0.0069722
#    define THRESHOLD_LOWER_LIMIT 36

// The gfm code is optimized to a block size in this case:
#    define BLOCK_SIZE            (16384)
#else
#    error "Bad level, choose one of 1/3/5"
#endif

#define NUM_OF_SEEDS 3

// Round the size to the nearest byte.
// SIZE suffix, is the number of bytes (uint8_t).
#define N_BITS (R_BITS * N0)
#define R_SIZE DIVIDE_AND_CEIL(R_BITS, 8)
#define R_QW   DIVIDE_AND_CEIL(R_BITS, 8 * QW_SIZE)
#define R_YMM  DIVIDE_AND_CEIL(R_BITS, 8 * YMM_SIZE)
#define R_ZMM  DIVIDE_AND_CEIL(R_BITS, 8 * ZMM_SIZE)

#define N_SIZE DIVIDE_AND_CEIL(N_BITS, 8)

#define R_BLOCKS      DIVIDE_AND_CEIL(R_BITS, BLOCK_SIZE)
#define R_PADDED      (R_BLOCKS * BLOCK_SIZE)
#define R_PADDED_SIZE (R_PADDED / 8)
#define R_PADDED_QW   (R_PADDED / 64)

#define N_BLOCKS      DIVIDE_AND_CEIL(N_BITS, BLOCK_SIZE)
#define N_PADDED      (N_BLOCKS * BLOCK_SIZE)
#define N_PADDED_SIZE (N_PADDED / 8)
#define N_PADDED_QW   (N_PADDED / 64)

#ifdef AVX512
#    define R_QDQWORDS_BITS (DIVIDE_AND_CEIL(R_BITS, ALL_ZMM_SIZE) * ALL_ZMM_SIZE)
bike_static_assert((R_BITS % ALL_ZMM_SIZE != 0), rbits_2048_err);

#    define N_QDQWORDS_BITS (R_QDQWORDS_BITS + R_BITS)
bike_static_assert((N_BITS % ALL_ZMM_SIZE != 0), nbits_2048_err);

#else // AVX512

#    define R_DDQWORDS_BITS (DIVIDE_AND_CEIL(R_BITS, ALL_YMM_SIZE) * ALL_YMM_SIZE)
bike_static_assert((R_BITS % ALL_YMM_SIZE != 0), rbits_512_err);

#    define N_DDQWORDS_BITS (R_DDQWORDS_BITS + R_BITS)
bike_static_assert((N_BITS % ALL_YMM_SIZE != 0), nbits_512_err);

#endif

#define LAST_R_QW_LEAD  (R_BITS & MASK(6))
#define LAST_R_QW_TRAIL (64 - LAST_R_QW_LEAD)
#define LAST_R_QW_MASK  MASK(LAST_R_QW_LEAD)

#define LAST_R_BYTE_LEAD  (R_BITS & MASK(3))
#define LAST_R_BYTE_TRAIL (8 - LAST_R_BYTE_LEAD)
#define LAST_R_BYTE_MASK  MASK(LAST_R_BYTE_LEAD)

// BIKE auxiliary functions parameters:
#define ELL_K_BITS 256
#define ELL_K_SIZE (ELL_K_BITS / 8)

////////////////////////////////
// Parameters for the BG decoder.
////////////////////////////////
// #define BG_DECODER
#define BGF_DECODER
#define DELTA  3
#define SLICES (LOG2_MSB(DV) + 1)

// Had to replace this so that the test could read parameter MAX_IT

// Decoding (bit-flipping) parameter

#ifndef MAX_IT
#    ifdef BG_DECODER
#        if (LEVEL == 1)
#            define MAX_IT 3
#        elif (LEVEL == 3)
#            define MAX_IT 4
#        elif (LEVEL == 5)
#            define MAX_IT 7
#        else
#            error "Level can only be 1/3/5"
#        endif
#    elif defined(BGF_DECODER)
#        if (LEVEL == 1)
#            define MAX_IT 5
#        elif (LEVEL == 3)
#            define MAX_IT 5
#        elif (LEVEL == 5)
#            define MAX_IT 5
#        else
#            error "Level can only be 1/3/5"
#        endif
#    endif
#endif