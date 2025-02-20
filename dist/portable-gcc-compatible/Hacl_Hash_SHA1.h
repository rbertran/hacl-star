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


#ifndef __Hacl_Hash_SHA1_H
#define __Hacl_Hash_SHA1_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"

/* SNIPPET_START: Hacl_Hash_Core_SHA1_legacy_init */

void Hacl_Hash_Core_SHA1_legacy_init(uint32_t *s);

/* SNIPPET_END: Hacl_Hash_Core_SHA1_legacy_init */

/* SNIPPET_START: Hacl_Hash_Core_SHA1_legacy_update */

void Hacl_Hash_Core_SHA1_legacy_update(uint32_t *h, uint8_t *l);

/* SNIPPET_END: Hacl_Hash_Core_SHA1_legacy_update */

/* SNIPPET_START: Hacl_Hash_Core_SHA1_legacy_finish */

void Hacl_Hash_Core_SHA1_legacy_finish(uint32_t *s, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_SHA1_legacy_finish */

/* SNIPPET_START: Hacl_Hash_SHA1_legacy_update_multi */

void Hacl_Hash_SHA1_legacy_update_multi(uint32_t *s, uint8_t *blocks, uint32_t n_blocks);

/* SNIPPET_END: Hacl_Hash_SHA1_legacy_update_multi */

/* SNIPPET_START: Hacl_Hash_SHA1_legacy_update_last */

void
Hacl_Hash_SHA1_legacy_update_last(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

/* SNIPPET_END: Hacl_Hash_SHA1_legacy_update_last */

/* SNIPPET_START: Hacl_Hash_SHA1_legacy_hash */

void Hacl_Hash_SHA1_legacy_hash(uint8_t *input, uint32_t input_len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_SHA1_legacy_hash */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Hash_SHA1_H_DEFINED
#endif
