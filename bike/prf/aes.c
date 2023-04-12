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

#include "aes.h"
#include "utilities.h"
#include <string.h>

ret_t
aes256_enc(OUT uint8_t *ct, IN const uint8_t *pt, IN const aes256_ks_t *ks) {
    uint32_t i     = 0;
    __m128i  block = _mm_setr_epi8(pt[0], pt[1], pt[2], pt[3], pt[4], pt[5], pt[6], pt[7], pt[8],
                                  pt[9], pt[10], pt[11], pt[12], pt[13], pt[14], pt[15]);

    block = _mm_xor_si128(block, ks->keys[0]);
    for (i = 1; i < AES256_ROUNDS; i++) {
        block = _mm_aesenc_si128(block, ks->keys[i]);
    }
    block = _mm_aesenclast_si128(block, ks->keys[AES256_ROUNDS]);

    // We use memcpy to avoid align casting.
    memcpy(ct, (const void *)&block, sizeof(block));

    // Clear the secret data when done
    secure_clean((uint8_t *)&block, sizeof(block));

    return SUCCESS;
}
