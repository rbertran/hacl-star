/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#ifndef __Hacl_Hash_Base_H
#define __Hacl_Hash_Base_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"
#include "Hacl_Leftovers.h"
#include "Lib_Memzero0.h"
#include "Hacl_Impl_Blake2_Constants.h"
#include "Hacl_Spec.h"

uint64_t Hacl_Hash_Core_Blake2_update_blake2s_32(uint32_t *s, uint64_t totlen, uint8_t *block);

void Hacl_Hash_Core_Blake2_finish_blake2s_32(uint32_t *s, uint64_t ev, uint8_t *dst);

uint128_t
Hacl_Hash_Core_Blake2_update_blake2b_32(uint64_t *s, uint128_t totlen, uint8_t *block);

void Hacl_Hash_Core_Blake2_finish_blake2b_32(uint64_t *s, uint128_t ev, uint8_t *dst);

uint64_t
Hacl_Hash_Blake2_update_multi_blake2s_32(
  uint32_t *s,
  uint64_t ev,
  uint8_t *blocks,
  uint32_t n_blocks
);

uint128_t
Hacl_Hash_Blake2_update_multi_blake2b_32(
  uint64_t *s,
  uint128_t ev,
  uint8_t *blocks,
  uint32_t n_blocks
);

uint64_t
Hacl_Hash_Blake2_update_last_blake2s_32(
  uint32_t *s,
  uint64_t ev,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

uint128_t
Hacl_Hash_Blake2_update_last_blake2b_32(
  uint64_t *s,
  uint128_t ev,
  uint128_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

void Hacl_Hash_Blake2_hash_blake2s_32(uint8_t *input, uint32_t input_len, uint8_t *dst);

void Hacl_Hash_Blake2_hash_blake2b_32(uint8_t *input, uint32_t input_len, uint8_t *dst);

uint32_t Hacl_Hash_Definitions_word_len(Spec_Hash_Definitions_hash_alg a);

uint32_t Hacl_Hash_Definitions_block_len(Spec_Hash_Definitions_hash_alg a);

uint32_t Hacl_Hash_Definitions_hash_word_len(Spec_Hash_Definitions_hash_alg a);

uint32_t Hacl_Hash_Definitions_hash_len(Spec_Hash_Definitions_hash_alg a);

#if defined(__cplusplus)
}
#endif

#define __Hacl_Hash_Base_H_DEFINED
#endif
