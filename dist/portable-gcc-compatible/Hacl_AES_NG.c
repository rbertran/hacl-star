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


#include "Hacl_AES_NG.h"

/* SNIPPET_START: load_block0 */

static void load_block0(uint64_t *out, uint8_t *inp)
{
  uint8_t *b1 = inp;
  uint8_t *b2 = inp + (uint32_t)8U;
  uint64_t u0 = load64_le(b1);
  uint64_t fst = u0;
  uint64_t u1 = load64_le(b2);
  uint64_t snd = u1;
  uint64_t fst1 = Hacl_Spec_AES_128_BitSlice_transpose_bits64(fst);
  uint64_t snd1 = Hacl_Spec_AES_128_BitSlice_transpose_bits64(snd);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t sh = i * (uint32_t)8U;
    uint64_t u = fst1 >> sh & (uint64_t)0xffU;
    uint64_t u10 = u ^ (snd1 >> sh & (uint64_t)0xffU) << (uint32_t)8U;
    out[i] = u10;
  }
}

/* SNIPPET_END: load_block0 */

/* SNIPPET_START: transpose_state */

static void transpose_state(uint64_t *st)
{
  uint64_t i0 = st[0U];
  uint64_t i1 = st[1U];
  uint64_t i2 = st[2U];
  uint64_t i3 = st[3U];
  uint64_t i4 = st[4U];
  uint64_t i5 = st[5U];
  uint64_t i6 = st[6U];
  uint64_t i7 = st[7U];
  uint64_t t0 = i0;
  uint64_t t1 = i1;
  uint64_t t2 = i2;
  uint64_t t3 = i3;
  uint64_t t4 = i4;
  uint64_t t5 = i5;
  uint64_t t6 = i6;
  uint64_t t7 = i7;
  st[0U] = t0;
  st[1U] = t1;
  st[2U] = t2;
  st[3U] = t3;
  st[4U] = t4;
  st[5U] = t5;
  st[6U] = t6;
  st[7U] = t7;
}

/* SNIPPET_END: transpose_state */

/* SNIPPET_START: store_block0 */

static void store_block0(uint8_t *out, uint64_t *inp)
{
  uint64_t i0 = inp[0U];
  uint64_t i1 = inp[1U];
  uint64_t t0 = i0;
  uint64_t t1 = i1;
  store64_le(out, t0);
  store64_le(out + (uint32_t)8U, t1);
}

/* SNIPPET_END: store_block0 */

/* SNIPPET_START: load_key1 */

static void load_key1(uint64_t *out, uint8_t *k)
{
  load_block0(out, k);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t u = out[i];
    uint64_t u1 = u ^ u << (uint32_t)16U;
    uint64_t u2 = u1 ^ u1 << (uint32_t)32U;
    out[i] = u2;
  }
}

/* SNIPPET_END: load_key1 */

/* SNIPPET_START: load_nonce */

static void load_nonce(uint64_t *out, uint8_t *nonce1)
{
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce1, (uint32_t)12U * sizeof (uint8_t));
  load_key1(out, nb);
}

/* SNIPPET_END: load_nonce */

/* SNIPPET_START: load_state */

static void load_state(uint64_t *out, uint64_t *nonce1, uint32_t counter)
{
  uint8_t ctr[16U] = { 0U };
  store32_be(ctr, counter);
  store32_be(ctr + (uint32_t)4U, counter + (uint32_t)1U);
  store32_be(ctr + (uint32_t)8U, counter + (uint32_t)2U);
  store32_be(ctr + (uint32_t)12U, counter + (uint32_t)3U);
  load_block0(out, ctr);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t u = out[i];
    uint64_t
    u1 = ((u << (uint32_t)12U | u << (uint32_t)24U) | u << (uint32_t)36U) | u << (uint32_t)48U;
    uint64_t u2 = u1 & (uint64_t)0xf000f000f000f000U;
    out[i] = u2 ^ nonce1[i];
  }
}

/* SNIPPET_END: load_state */

/* SNIPPET_START: xor_state_key1 */

static void xor_state_key1(uint64_t *st, uint64_t *ost)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    st[i] = st[i] ^ ost[i];
  }
}

/* SNIPPET_END: xor_state_key1 */

/* SNIPPET_START: xor_block */

static void xor_block(uint8_t *out, uint64_t *st, uint8_t *inp)
{
  transpose_state(st);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint8_t *ob = out + i * (uint32_t)8U;
    uint8_t *ib = inp + i * (uint32_t)8U;
    uint64_t u = load64_le(ib);
    uint64_t u0 = u;
    store64_le(ob, u0 ^ st[i]);
  }
}

/* SNIPPET_END: xor_block */

/* SNIPPET_START: sub_bytes_state */

static void sub_bytes_state(uint64_t *st)
{
  uint64_t st0 = st[0U];
  uint64_t st1 = st[1U];
  uint64_t st2 = st[2U];
  uint64_t st3 = st[3U];
  uint64_t st4 = st[4U];
  uint64_t st5 = st[5U];
  uint64_t st6 = st[6U];
  uint64_t st7 = st[7U];
  st[0U] = st0;
  st[1U] = st1;
  st[2U] = st2;
  st[3U] = st3;
  st[4U] = st4;
  st[5U] = st5;
  st[6U] = st6;
  st[7U] = st7;
}

/* SNIPPET_END: sub_bytes_state */

/* SNIPPET_START: shift_rows_state */

static void shift_rows_state(uint64_t *st)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t rowi = st[i];
    st[i] =
      ((((((rowi & (uint64_t)0x1111111111111111U)
      | (rowi & (uint64_t)0x2220222022202220U) >> (uint32_t)4U)
      | (rowi & (uint64_t)0x0002000200020002U) << (uint32_t)12U)
      | (rowi & (uint64_t)0x4400440044004400U) >> (uint32_t)8U)
      | (rowi & (uint64_t)0x0044004400440044U) << (uint32_t)8U)
      | (rowi & (uint64_t)0x8000800080008000U) >> (uint32_t)12U)
      | (rowi & (uint64_t)0x0888088808880888U) << (uint32_t)4U;
  }
}

/* SNIPPET_END: shift_rows_state */

/* SNIPPET_START: mix_columns_state */

static void mix_columns_state(uint64_t *st)
{
  uint64_t col[8U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t coli = st[i];
    col[i] =
      coli
      ^
        ((coli & (uint64_t)0xeeeeeeeeeeeeeeeeU)
        >> (uint32_t)1U
        | (coli & (uint64_t)0x1111111111111111U) << (uint32_t)3U);
  }
  uint64_t col0 = col[0U];
  uint64_t
  ncol0 =
    col0
    ^
      ((col0 & (uint64_t)0xccccccccccccccccU)
      >> (uint32_t)2U
      | (col0 & (uint64_t)0x3333333333333333U) << (uint32_t)2U);
  st[0U] = st[0U] ^ ncol0;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)7U; i++)
  {
    uint64_t prev = col[i];
    uint64_t next = col[i + (uint32_t)1U];
    uint64_t
    ncoli =
      next
      ^
        ((next & (uint64_t)0xccccccccccccccccU)
        >> (uint32_t)2U
        | (next & (uint64_t)0x3333333333333333U) << (uint32_t)2U);
    st[i + (uint32_t)1U] = st[i + (uint32_t)1U] ^ (ncoli ^ prev);
  }
  st[0U] = st[0U] ^ col[7U];
  st[1U] = st[1U] ^ col[7U];
  st[3U] = st[3U] ^ col[7U];
  st[4U] = st[4U] ^ col[7U];
}

/* SNIPPET_END: mix_columns_state */

/* SNIPPET_START: aes_enc */

static void aes_enc(uint64_t *st, uint64_t *key)
{
  sub_bytes_state(st);
  shift_rows_state(st);
  mix_columns_state(st);
  xor_state_key1(st, key);
}

/* SNIPPET_END: aes_enc */

/* SNIPPET_START: aes_enc_last */

static void aes_enc_last(uint64_t *st, uint64_t *key)
{
  sub_bytes_state(st);
  shift_rows_state(st);
  xor_state_key1(st, key);
}

/* SNIPPET_END: aes_enc_last */

/* SNIPPET_START: aes_keygen_assist */

static void aes_keygen_assist(uint64_t *next, uint64_t *prev, uint8_t rcon1)
{
  memcpy(next, prev, (uint32_t)8U * sizeof (uint64_t));
  sub_bytes_state(next);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t u3 = next[i] & (uint64_t)0xf000f000f000f000U;
    uint64_t n = u3 >> (uint32_t)12U;
    uint64_t n1 = (n >> (uint32_t)1U | n << (uint32_t)3U) & (uint64_t)0x000f000f000f000fU;
    uint64_t ri = (uint64_t)(rcon1 >> i & (uint8_t)1U);
    uint64_t ri1 = ri ^ ri << (uint32_t)16U;
    uint64_t ri2 = ri1 ^ ri1 << (uint32_t)32U;
    uint64_t n2 = n1 ^ ri2;
    uint64_t n3 = n2 << (uint32_t)12U;
    next[i] = n3 ^ u3 >> (uint32_t)4U;
  }
}

/* SNIPPET_END: aes_keygen_assist */

/* SNIPPET_START: key_expansion_step */

static void key_expansion_step(uint64_t *next, uint64_t *prev)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t p = prev[i];
    uint64_t n = next[i];
    uint64_t
    p1 =
      p
      ^
        ((p & (uint64_t)0x0fff0fff0fff0fffU)
        << (uint32_t)4U
        ^
          ((p & (uint64_t)0x00ff00ff00ff00ffU)
          << (uint32_t)8U
          ^ (p & (uint64_t)0x000f000f000f000fU) << (uint32_t)12U));
    next[i] = n ^ p1;
  }
}

/* SNIPPET_END: key_expansion_step */

/* SNIPPET_START: aes128_ctr_bitslice */

static void
aes128_ctr_bitslice(uint32_t len, uint8_t *out, uint8_t *inp, uint64_t *ctx, uint32_t counter)
{
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = counter + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    uint64_t st[8U] = { 0U };
    uint64_t *kex = ctx + (uint32_t)8U;
    uint64_t *n = ctx;
    load_state(st, n, ctr);
    uint32_t klen = (uint32_t)8U;
    uint64_t *k0 = kex;
    uint64_t *kr = kex + klen;
    uint64_t *kn = kex + (uint32_t)10U * klen;
    xor_state_key1(st, k0);
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)9U; i0++)
    {
      uint64_t *sub_key = kr + i0 * (uint32_t)8U;
      aes_enc(st, sub_key);
    }
    aes_enc_last(st, kn);
    xor_block(ob, st, ib);
  }
  uint32_t rem = len % (uint32_t)64U;
  uint8_t last[64U];
  if (rem > (uint32_t)0U)
  {
    uint32_t ctr = counter + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    uint8_t init = (uint8_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      last[i] = init;
    }
    memcpy(last, ib, rem * sizeof (uint8_t));
    uint64_t st[8U] = { 0U };
    uint64_t *kex = ctx + (uint32_t)8U;
    uint64_t *n = ctx;
    load_state(st, n, ctr);
    uint32_t klen = (uint32_t)8U;
    uint64_t *k0 = kex;
    uint64_t *kr = kex + klen;
    uint64_t *kn = kex + (uint32_t)10U * klen;
    xor_state_key1(st, k0);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)9U; i++)
    {
      uint64_t *sub_key = kr + i * (uint32_t)8U;
      aes_enc(st, sub_key);
    }
    aes_enc_last(st, kn);
    xor_block(last, st, last);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: aes128_ctr_bitslice */

/* SNIPPET_START: aes256_ctr_bitslice */

static void
aes256_ctr_bitslice(uint32_t len, uint8_t *out, uint8_t *inp, uint64_t *ctx, uint32_t counter)
{
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = counter + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    uint64_t st[8U] = { 0U };
    uint64_t *kex = ctx + (uint32_t)8U;
    uint64_t *n = ctx;
    load_state(st, n, ctr);
    uint32_t klen = (uint32_t)8U;
    uint64_t *k0 = kex;
    uint64_t *kr = kex + klen;
    uint64_t *kn = kex + (uint32_t)14U * klen;
    xor_state_key1(st, k0);
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)13U; i0++)
    {
      uint64_t *sub_key = kr + i0 * (uint32_t)8U;
      aes_enc(st, sub_key);
    }
    aes_enc_last(st, kn);
    xor_block(ob, st, ib);
  }
  uint32_t rem = len % (uint32_t)64U;
  uint8_t last[64U];
  if (rem > (uint32_t)0U)
  {
    uint32_t ctr = counter + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    uint8_t init = (uint8_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      last[i] = init;
    }
    memcpy(last, ib, rem * sizeof (uint8_t));
    uint64_t st[8U] = { 0U };
    uint64_t *kex = ctx + (uint32_t)8U;
    uint64_t *n = ctx;
    load_state(st, n, ctr);
    uint32_t klen = (uint32_t)8U;
    uint64_t *k0 = kex;
    uint64_t *kr = kex + klen;
    uint64_t *kn = kex + (uint32_t)14U * klen;
    xor_state_key1(st, k0);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)13U; i++)
    {
      uint64_t *sub_key = kr + i * (uint32_t)8U;
      aes_enc(st, sub_key);
    }
    aes_enc_last(st, kn);
    xor_block(last, st, last);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: aes256_ctr_bitslice */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_init */

inline void Hacl_AES_128_BitSlice_aes128_init(uint64_t *ctx, uint8_t *key, uint8_t *nonce)
{
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n = ctx;
  uint32_t klen = (uint32_t)8U;
  load_key1(kex, key);
  uint64_t *prev = kex;
  uint64_t *next = kex + klen;
  aes_keygen_assist(next, prev, (uint8_t)0x01U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next[i] = n4;
  }
  key_expansion_step(next, prev);
  uint64_t *prev1 = kex + klen;
  uint64_t *next1 = kex + (uint32_t)2U * klen;
  aes_keygen_assist(next1, prev1, (uint8_t)0x02U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next1[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next1[i] = n4;
  }
  key_expansion_step(next1, prev1);
  uint64_t *prev2 = kex + klen * (uint32_t)2U;
  uint64_t *next2 = kex + klen * (uint32_t)3U;
  aes_keygen_assist(next2, prev2, (uint8_t)0x04U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next2[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next2[i] = n4;
  }
  key_expansion_step(next2, prev2);
  uint64_t *prev3 = kex + klen * (uint32_t)3U;
  uint64_t *next3 = kex + klen * (uint32_t)4U;
  aes_keygen_assist(next3, prev3, (uint8_t)0x08U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next3[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next3[i] = n4;
  }
  key_expansion_step(next3, prev3);
  uint64_t *prev4 = kex + klen * (uint32_t)4U;
  uint64_t *next4 = kex + klen * (uint32_t)5U;
  aes_keygen_assist(next4, prev4, (uint8_t)0x10U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next4[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next4[i] = n4;
  }
  key_expansion_step(next4, prev4);
  uint64_t *prev5 = kex + klen * (uint32_t)5U;
  uint64_t *next5 = kex + klen * (uint32_t)6U;
  aes_keygen_assist(next5, prev5, (uint8_t)0x20U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next5[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next5[i] = n4;
  }
  key_expansion_step(next5, prev5);
  uint64_t *prev6 = kex + klen * (uint32_t)6U;
  uint64_t *next6 = kex + klen * (uint32_t)7U;
  aes_keygen_assist(next6, prev6, (uint8_t)0x40U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next6[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next6[i] = n4;
  }
  key_expansion_step(next6, prev6);
  uint64_t *prev7 = kex + klen * (uint32_t)7U;
  uint64_t *next7 = kex + klen * (uint32_t)8U;
  aes_keygen_assist(next7, prev7, (uint8_t)0x80U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next7[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next7[i] = n4;
  }
  key_expansion_step(next7, prev7);
  uint64_t *prev8 = kex + klen * (uint32_t)8U;
  uint64_t *next8 = kex + klen * (uint32_t)9U;
  aes_keygen_assist(next8, prev8, (uint8_t)0x1bU);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next8[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next8[i] = n4;
  }
  key_expansion_step(next8, prev8);
  uint64_t *prev9 = kex + klen * (uint32_t)9U;
  uint64_t *next9 = kex + klen * (uint32_t)10U;
  aes_keygen_assist(next9, prev9, (uint8_t)0x36U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next9[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next9[i] = n4;
  }
  key_expansion_step(next9, prev9);
  load_nonce(n, nonce);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_init */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_set_nonce */

inline void Hacl_AES_128_BitSlice_aes128_set_nonce(uint64_t *ctx, uint8_t *nonce)
{
  uint64_t *n = ctx;
  load_nonce(n, nonce);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_set_nonce */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_key_block */

inline void
Hacl_AES_128_BitSlice_aes128_key_block(uint8_t *kb, uint64_t *ctx, uint32_t counter)
{
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n = ctx;
  uint64_t st[8U] = { 0U };
  load_state(st, n, counter);
  uint32_t klen = (uint32_t)8U;
  uint64_t *k0 = kex;
  uint64_t *kr = kex + klen;
  uint64_t *kn = kex + (uint32_t)10U * klen;
  xor_state_key1(st, k0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)9U; i++)
  {
    uint64_t *sub_key = kr + i * (uint32_t)8U;
    aes_enc(st, sub_key);
  }
  aes_enc_last(st, kn);
  store_block0(kb, st);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_key_block */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_update4 */

void
Hacl_AES_128_BitSlice_aes128_update4(uint8_t *out, uint8_t *inp, uint64_t *ctx, uint32_t ctr)
{
  uint64_t st[8U] = { 0U };
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n = ctx;
  load_state(st, n, ctr);
  uint32_t klen = (uint32_t)8U;
  uint64_t *k0 = kex;
  uint64_t *kr = kex + klen;
  uint64_t *kn = kex + (uint32_t)10U * klen;
  xor_state_key1(st, k0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)9U; i++)
  {
    uint64_t *sub_key = kr + i * (uint32_t)8U;
    aes_enc(st, sub_key);
  }
  aes_enc_last(st, kn);
  xor_block(out, st, inp);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_update4 */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_ctr */

void
Hacl_AES_128_BitSlice_aes128_ctr(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint64_t *ctx,
  uint32_t c
)
{
  aes128_ctr_bitslice(len, out, inp, ctx, c);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_ctr */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_ctr_encrypt */

inline void
Hacl_AES_128_BitSlice_aes128_ctr_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)8U + (uint32_t)11U * (uint32_t)8U);
  uint64_t ctx[(uint32_t)8U + (uint32_t)11U * (uint32_t)8U];
  memset(ctx, 0U, ((uint32_t)8U + (uint32_t)11U * (uint32_t)8U) * sizeof (uint64_t));
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n1 = ctx;
  uint32_t klen = (uint32_t)8U;
  load_key1(kex, k);
  uint64_t *prev = kex;
  uint64_t *next = kex + klen;
  aes_keygen_assist(next, prev, (uint8_t)0x01U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next[i] = n5;
  }
  key_expansion_step(next, prev);
  uint64_t *prev1 = kex + klen;
  uint64_t *next1 = kex + (uint32_t)2U * klen;
  aes_keygen_assist(next1, prev1, (uint8_t)0x02U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next1[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next1[i] = n5;
  }
  key_expansion_step(next1, prev1);
  uint64_t *prev2 = kex + klen * (uint32_t)2U;
  uint64_t *next2 = kex + klen * (uint32_t)3U;
  aes_keygen_assist(next2, prev2, (uint8_t)0x04U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next2[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next2[i] = n5;
  }
  key_expansion_step(next2, prev2);
  uint64_t *prev3 = kex + klen * (uint32_t)3U;
  uint64_t *next3 = kex + klen * (uint32_t)4U;
  aes_keygen_assist(next3, prev3, (uint8_t)0x08U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next3[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next3[i] = n5;
  }
  key_expansion_step(next3, prev3);
  uint64_t *prev4 = kex + klen * (uint32_t)4U;
  uint64_t *next4 = kex + klen * (uint32_t)5U;
  aes_keygen_assist(next4, prev4, (uint8_t)0x10U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next4[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next4[i] = n5;
  }
  key_expansion_step(next4, prev4);
  uint64_t *prev5 = kex + klen * (uint32_t)5U;
  uint64_t *next5 = kex + klen * (uint32_t)6U;
  aes_keygen_assist(next5, prev5, (uint8_t)0x20U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next5[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next5[i] = n5;
  }
  key_expansion_step(next5, prev5);
  uint64_t *prev6 = kex + klen * (uint32_t)6U;
  uint64_t *next6 = kex + klen * (uint32_t)7U;
  aes_keygen_assist(next6, prev6, (uint8_t)0x40U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next6[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next6[i] = n5;
  }
  key_expansion_step(next6, prev6);
  uint64_t *prev7 = kex + klen * (uint32_t)7U;
  uint64_t *next7 = kex + klen * (uint32_t)8U;
  aes_keygen_assist(next7, prev7, (uint8_t)0x80U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next7[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next7[i] = n5;
  }
  key_expansion_step(next7, prev7);
  uint64_t *prev8 = kex + klen * (uint32_t)8U;
  uint64_t *next8 = kex + klen * (uint32_t)9U;
  aes_keygen_assist(next8, prev8, (uint8_t)0x1bU);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next8[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next8[i] = n5;
  }
  key_expansion_step(next8, prev8);
  uint64_t *prev9 = kex + klen * (uint32_t)9U;
  uint64_t *next9 = kex + klen * (uint32_t)10U;
  aes_keygen_assist(next9, prev9, (uint8_t)0x36U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next9[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next9[i] = n5;
  }
  key_expansion_step(next9, prev9);
  load_nonce(n1, n);
  aes128_ctr_bitslice(len, out, inp, ctx, c);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_ctr_encrypt */

/* SNIPPET_START: Hacl_AES_128_BitSlice_aes128_ctr_decrypt */

inline void
Hacl_AES_128_BitSlice_aes128_ctr_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)8U + (uint32_t)11U * (uint32_t)8U);
  uint64_t ctx[(uint32_t)8U + (uint32_t)11U * (uint32_t)8U];
  memset(ctx, 0U, ((uint32_t)8U + (uint32_t)11U * (uint32_t)8U) * sizeof (uint64_t));
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n1 = ctx;
  uint32_t klen = (uint32_t)8U;
  load_key1(kex, k);
  uint64_t *prev = kex;
  uint64_t *next = kex + klen;
  aes_keygen_assist(next, prev, (uint8_t)0x01U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next[i] = n5;
  }
  key_expansion_step(next, prev);
  uint64_t *prev1 = kex + klen;
  uint64_t *next1 = kex + (uint32_t)2U * klen;
  aes_keygen_assist(next1, prev1, (uint8_t)0x02U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next1[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next1[i] = n5;
  }
  key_expansion_step(next1, prev1);
  uint64_t *prev2 = kex + klen * (uint32_t)2U;
  uint64_t *next2 = kex + klen * (uint32_t)3U;
  aes_keygen_assist(next2, prev2, (uint8_t)0x04U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next2[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next2[i] = n5;
  }
  key_expansion_step(next2, prev2);
  uint64_t *prev3 = kex + klen * (uint32_t)3U;
  uint64_t *next3 = kex + klen * (uint32_t)4U;
  aes_keygen_assist(next3, prev3, (uint8_t)0x08U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next3[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next3[i] = n5;
  }
  key_expansion_step(next3, prev3);
  uint64_t *prev4 = kex + klen * (uint32_t)4U;
  uint64_t *next4 = kex + klen * (uint32_t)5U;
  aes_keygen_assist(next4, prev4, (uint8_t)0x10U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next4[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next4[i] = n5;
  }
  key_expansion_step(next4, prev4);
  uint64_t *prev5 = kex + klen * (uint32_t)5U;
  uint64_t *next5 = kex + klen * (uint32_t)6U;
  aes_keygen_assist(next5, prev5, (uint8_t)0x20U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next5[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next5[i] = n5;
  }
  key_expansion_step(next5, prev5);
  uint64_t *prev6 = kex + klen * (uint32_t)6U;
  uint64_t *next6 = kex + klen * (uint32_t)7U;
  aes_keygen_assist(next6, prev6, (uint8_t)0x40U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next6[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next6[i] = n5;
  }
  key_expansion_step(next6, prev6);
  uint64_t *prev7 = kex + klen * (uint32_t)7U;
  uint64_t *next7 = kex + klen * (uint32_t)8U;
  aes_keygen_assist(next7, prev7, (uint8_t)0x80U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next7[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next7[i] = n5;
  }
  key_expansion_step(next7, prev7);
  uint64_t *prev8 = kex + klen * (uint32_t)8U;
  uint64_t *next8 = kex + klen * (uint32_t)9U;
  aes_keygen_assist(next8, prev8, (uint8_t)0x1bU);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next8[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next8[i] = n5;
  }
  key_expansion_step(next8, prev8);
  uint64_t *prev9 = kex + klen * (uint32_t)9U;
  uint64_t *next9 = kex + klen * (uint32_t)10U;
  aes_keygen_assist(next9, prev9, (uint8_t)0x36U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next9[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next9[i] = n5;
  }
  key_expansion_step(next9, prev9);
  load_nonce(n1, n);
  aes128_ctr_bitslice(len, out, inp, ctx, c);
}

/* SNIPPET_END: Hacl_AES_128_BitSlice_aes128_ctr_decrypt */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_init */

inline void Hacl_AES_256_BitSlice_aes256_init(uint64_t *ctx, uint8_t *key, uint8_t *nonce)
{
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n = ctx;
  uint32_t klen = (uint32_t)8U;
  uint64_t *next0 = kex;
  uint64_t *next1 = kex + klen;
  load_key1(next0, key);
  load_key1(next1, key + (uint32_t)16U);
  uint64_t *prev0 = next0;
  uint64_t *prev1 = next1;
  uint64_t *next01 = kex + klen * (uint32_t)2U;
  uint64_t *next11 = kex + klen * (uint32_t)3U;
  aes_keygen_assist(next01, prev1, (uint8_t)0x01U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next01[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next01[i] = n4;
  }
  key_expansion_step(next01, prev0);
  aes_keygen_assist(next11, next01, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next11[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next11[i] = n4;
  }
  key_expansion_step(next11, prev1);
  uint64_t *prev01 = next01;
  uint64_t *prev11 = next11;
  uint64_t *next02 = kex + klen * (uint32_t)4U;
  uint64_t *next12 = kex + klen * (uint32_t)5U;
  aes_keygen_assist(next02, prev11, (uint8_t)0x02U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next02[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next02[i] = n4;
  }
  key_expansion_step(next02, prev01);
  aes_keygen_assist(next12, next02, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next12[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next12[i] = n4;
  }
  key_expansion_step(next12, prev11);
  uint64_t *prev02 = next02;
  uint64_t *prev12 = next12;
  uint64_t *next03 = kex + klen * (uint32_t)6U;
  uint64_t *next13 = kex + klen * (uint32_t)7U;
  aes_keygen_assist(next03, prev12, (uint8_t)0x04U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next03[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next03[i] = n4;
  }
  key_expansion_step(next03, prev02);
  aes_keygen_assist(next13, next03, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next13[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next13[i] = n4;
  }
  key_expansion_step(next13, prev12);
  uint64_t *prev03 = next03;
  uint64_t *prev13 = next13;
  uint64_t *next04 = kex + klen * (uint32_t)8U;
  uint64_t *next14 = kex + klen * (uint32_t)9U;
  aes_keygen_assist(next04, prev13, (uint8_t)0x08U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next04[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next04[i] = n4;
  }
  key_expansion_step(next04, prev03);
  aes_keygen_assist(next14, next04, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next14[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next14[i] = n4;
  }
  key_expansion_step(next14, prev13);
  uint64_t *prev04 = next04;
  uint64_t *prev14 = next14;
  uint64_t *next05 = kex + klen * (uint32_t)10U;
  uint64_t *next15 = kex + klen * (uint32_t)11U;
  aes_keygen_assist(next05, prev14, (uint8_t)0x10U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next05[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next05[i] = n4;
  }
  key_expansion_step(next05, prev04);
  aes_keygen_assist(next15, next05, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next15[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next15[i] = n4;
  }
  key_expansion_step(next15, prev14);
  uint64_t *prev05 = next05;
  uint64_t *prev15 = next15;
  uint64_t *next06 = kex + klen * (uint32_t)12U;
  uint64_t *next16 = kex + klen * (uint32_t)13U;
  aes_keygen_assist(next06, prev15, (uint8_t)0x20U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next06[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next06[i] = n4;
  }
  key_expansion_step(next06, prev05);
  aes_keygen_assist(next16, next06, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next16[i];
    uint64_t n2 = n1 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n3 = n2 ^ n2 << (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next16[i] = n4;
  }
  key_expansion_step(next16, prev15);
  uint64_t *prev06 = next06;
  uint64_t *prev16 = next16;
  uint64_t *next07 = kex + klen * (uint32_t)14U;
  aes_keygen_assist(next07, prev16, (uint8_t)0x40U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n1 = next07[i];
    uint64_t n2 = n1 & (uint64_t)0xf000f000f000f000U;
    uint64_t n3 = n2 ^ n2 >> (uint32_t)4U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)8U;
    next07[i] = n4;
  }
  key_expansion_step(next07, prev06);
  load_nonce(n, nonce);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_init */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_encrypt_block */

inline void Hacl_AES_256_BitSlice_aes256_encrypt_block(uint8_t *ob, uint64_t *ctx, uint8_t *ib)
{
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t st[8U] = { 0U };
  load_block0(st, ib);
  uint32_t klen = (uint32_t)8U;
  uint64_t *k0 = kex;
  uint64_t *kr = kex + klen;
  uint64_t *kn = kex + (uint32_t)14U * klen;
  xor_state_key1(st, k0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)13U; i++)
  {
    uint64_t *sub_key = kr + i * (uint32_t)8U;
    aes_enc(st, sub_key);
  }
  aes_enc_last(st, kn);
  store_block0(ob, st);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_encrypt_block */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_set_nonce */

inline void Hacl_AES_256_BitSlice_aes256_set_nonce(uint64_t *ctx, uint8_t *nonce)
{
  uint64_t *n = ctx;
  load_nonce(n, nonce);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_set_nonce */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_key_block */

inline void
Hacl_AES_256_BitSlice_aes256_key_block(uint8_t *kb, uint64_t *ctx, uint32_t counter)
{
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n = ctx;
  uint64_t st[8U] = { 0U };
  load_state(st, n, counter);
  uint32_t klen = (uint32_t)8U;
  uint64_t *k0 = kex;
  uint64_t *kr = kex + klen;
  uint64_t *kn = kex + (uint32_t)14U * klen;
  xor_state_key1(st, k0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)13U; i++)
  {
    uint64_t *sub_key = kr + i * (uint32_t)8U;
    aes_enc(st, sub_key);
  }
  aes_enc_last(st, kn);
  store_block0(kb, st);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_key_block */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_update4 */

void
Hacl_AES_256_BitSlice_aes256_update4(uint8_t *out, uint8_t *inp, uint64_t *ctx, uint32_t ctr)
{
  uint64_t st[8U] = { 0U };
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n = ctx;
  load_state(st, n, ctr);
  uint32_t klen = (uint32_t)8U;
  uint64_t *k0 = kex;
  uint64_t *kr = kex + klen;
  uint64_t *kn = kex + (uint32_t)14U * klen;
  xor_state_key1(st, k0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)13U; i++)
  {
    uint64_t *sub_key = kr + i * (uint32_t)8U;
    aes_enc(st, sub_key);
  }
  aes_enc_last(st, kn);
  xor_block(out, st, inp);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_update4 */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_ctr */

inline void
Hacl_AES_256_BitSlice_aes256_ctr(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint64_t *ctx,
  uint32_t c
)
{
  aes256_ctr_bitslice(len, out, inp, ctx, c);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_ctr */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_ctr_encrypt */

inline void
Hacl_AES_256_BitSlice_aes256_ctr_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)8U + (uint32_t)15U * (uint32_t)8U);
  uint64_t ctx[(uint32_t)8U + (uint32_t)15U * (uint32_t)8U];
  memset(ctx, 0U, ((uint32_t)8U + (uint32_t)15U * (uint32_t)8U) * sizeof (uint64_t));
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n1 = ctx;
  uint32_t klen = (uint32_t)8U;
  uint64_t *next0 = kex;
  uint64_t *next1 = kex + klen;
  load_key1(next0, k);
  load_key1(next1, k + (uint32_t)16U);
  uint64_t *prev0 = next0;
  uint64_t *prev1 = next1;
  uint64_t *next01 = kex + klen * (uint32_t)2U;
  uint64_t *next11 = kex + klen * (uint32_t)3U;
  aes_keygen_assist(next01, prev1, (uint8_t)0x01U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next01[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next01[i] = n5;
  }
  key_expansion_step(next01, prev0);
  aes_keygen_assist(next11, next01, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next11[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next11[i] = n5;
  }
  key_expansion_step(next11, prev1);
  uint64_t *prev01 = next01;
  uint64_t *prev11 = next11;
  uint64_t *next02 = kex + klen * (uint32_t)4U;
  uint64_t *next12 = kex + klen * (uint32_t)5U;
  aes_keygen_assist(next02, prev11, (uint8_t)0x02U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next02[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next02[i] = n5;
  }
  key_expansion_step(next02, prev01);
  aes_keygen_assist(next12, next02, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next12[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next12[i] = n5;
  }
  key_expansion_step(next12, prev11);
  uint64_t *prev02 = next02;
  uint64_t *prev12 = next12;
  uint64_t *next03 = kex + klen * (uint32_t)6U;
  uint64_t *next13 = kex + klen * (uint32_t)7U;
  aes_keygen_assist(next03, prev12, (uint8_t)0x04U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next03[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next03[i] = n5;
  }
  key_expansion_step(next03, prev02);
  aes_keygen_assist(next13, next03, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next13[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next13[i] = n5;
  }
  key_expansion_step(next13, prev12);
  uint64_t *prev03 = next03;
  uint64_t *prev13 = next13;
  uint64_t *next04 = kex + klen * (uint32_t)8U;
  uint64_t *next14 = kex + klen * (uint32_t)9U;
  aes_keygen_assist(next04, prev13, (uint8_t)0x08U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next04[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next04[i] = n5;
  }
  key_expansion_step(next04, prev03);
  aes_keygen_assist(next14, next04, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next14[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next14[i] = n5;
  }
  key_expansion_step(next14, prev13);
  uint64_t *prev04 = next04;
  uint64_t *prev14 = next14;
  uint64_t *next05 = kex + klen * (uint32_t)10U;
  uint64_t *next15 = kex + klen * (uint32_t)11U;
  aes_keygen_assist(next05, prev14, (uint8_t)0x10U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next05[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next05[i] = n5;
  }
  key_expansion_step(next05, prev04);
  aes_keygen_assist(next15, next05, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next15[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next15[i] = n5;
  }
  key_expansion_step(next15, prev14);
  uint64_t *prev05 = next05;
  uint64_t *prev15 = next15;
  uint64_t *next06 = kex + klen * (uint32_t)12U;
  uint64_t *next16 = kex + klen * (uint32_t)13U;
  aes_keygen_assist(next06, prev15, (uint8_t)0x20U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next06[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next06[i] = n5;
  }
  key_expansion_step(next06, prev05);
  aes_keygen_assist(next16, next06, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next16[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next16[i] = n5;
  }
  key_expansion_step(next16, prev15);
  uint64_t *prev06 = next06;
  uint64_t *prev16 = next16;
  uint64_t *next07 = kex + klen * (uint32_t)14U;
  aes_keygen_assist(next07, prev16, (uint8_t)0x40U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next07[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next07[i] = n5;
  }
  key_expansion_step(next07, prev06);
  load_nonce(n1, n);
  aes256_ctr_bitslice(len, out, inp, ctx, c);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_ctr_encrypt */

/* SNIPPET_START: Hacl_AES_256_BitSlice_aes256_ctr_decrypt */

inline void
Hacl_AES_256_BitSlice_aes256_ctr_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)8U + (uint32_t)15U * (uint32_t)8U);
  uint64_t ctx[(uint32_t)8U + (uint32_t)15U * (uint32_t)8U];
  memset(ctx, 0U, ((uint32_t)8U + (uint32_t)15U * (uint32_t)8U) * sizeof (uint64_t));
  uint64_t *kex = ctx + (uint32_t)8U;
  uint64_t *n1 = ctx;
  uint32_t klen = (uint32_t)8U;
  uint64_t *next0 = kex;
  uint64_t *next1 = kex + klen;
  load_key1(next0, k);
  load_key1(next1, k + (uint32_t)16U);
  uint64_t *prev0 = next0;
  uint64_t *prev1 = next1;
  uint64_t *next01 = kex + klen * (uint32_t)2U;
  uint64_t *next11 = kex + klen * (uint32_t)3U;
  aes_keygen_assist(next01, prev1, (uint8_t)0x01U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next01[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next01[i] = n5;
  }
  key_expansion_step(next01, prev0);
  aes_keygen_assist(next11, next01, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next11[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next11[i] = n5;
  }
  key_expansion_step(next11, prev1);
  uint64_t *prev01 = next01;
  uint64_t *prev11 = next11;
  uint64_t *next02 = kex + klen * (uint32_t)4U;
  uint64_t *next12 = kex + klen * (uint32_t)5U;
  aes_keygen_assist(next02, prev11, (uint8_t)0x02U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next02[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next02[i] = n5;
  }
  key_expansion_step(next02, prev01);
  aes_keygen_assist(next12, next02, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next12[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next12[i] = n5;
  }
  key_expansion_step(next12, prev11);
  uint64_t *prev02 = next02;
  uint64_t *prev12 = next12;
  uint64_t *next03 = kex + klen * (uint32_t)6U;
  uint64_t *next13 = kex + klen * (uint32_t)7U;
  aes_keygen_assist(next03, prev12, (uint8_t)0x04U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next03[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next03[i] = n5;
  }
  key_expansion_step(next03, prev02);
  aes_keygen_assist(next13, next03, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next13[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next13[i] = n5;
  }
  key_expansion_step(next13, prev12);
  uint64_t *prev03 = next03;
  uint64_t *prev13 = next13;
  uint64_t *next04 = kex + klen * (uint32_t)8U;
  uint64_t *next14 = kex + klen * (uint32_t)9U;
  aes_keygen_assist(next04, prev13, (uint8_t)0x08U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next04[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next04[i] = n5;
  }
  key_expansion_step(next04, prev03);
  aes_keygen_assist(next14, next04, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next14[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next14[i] = n5;
  }
  key_expansion_step(next14, prev13);
  uint64_t *prev04 = next04;
  uint64_t *prev14 = next14;
  uint64_t *next05 = kex + klen * (uint32_t)10U;
  uint64_t *next15 = kex + klen * (uint32_t)11U;
  aes_keygen_assist(next05, prev14, (uint8_t)0x10U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next05[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next05[i] = n5;
  }
  key_expansion_step(next05, prev04);
  aes_keygen_assist(next15, next05, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next15[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next15[i] = n5;
  }
  key_expansion_step(next15, prev14);
  uint64_t *prev05 = next05;
  uint64_t *prev15 = next15;
  uint64_t *next06 = kex + klen * (uint32_t)12U;
  uint64_t *next16 = kex + klen * (uint32_t)13U;
  aes_keygen_assist(next06, prev15, (uint8_t)0x20U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next06[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next06[i] = n5;
  }
  key_expansion_step(next06, prev05);
  aes_keygen_assist(next16, next06, (uint8_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next16[i];
    uint64_t n3 = n2 & (uint64_t)0x0f000f000f000f00U;
    uint64_t n4 = n3 ^ n3 << (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next16[i] = n5;
  }
  key_expansion_step(next16, prev15);
  uint64_t *prev06 = next06;
  uint64_t *prev16 = next16;
  uint64_t *next07 = kex + klen * (uint32_t)14U;
  aes_keygen_assist(next07, prev16, (uint8_t)0x40U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t n2 = next07[i];
    uint64_t n3 = n2 & (uint64_t)0xf000f000f000f000U;
    uint64_t n4 = n3 ^ n3 >> (uint32_t)4U;
    uint64_t n5 = n4 ^ n4 >> (uint32_t)8U;
    next07[i] = n5;
  }
  key_expansion_step(next07, prev06);
  load_nonce(n1, n);
  aes256_ctr_bitslice(len, out, inp, ctx, c);
}

/* SNIPPET_END: Hacl_AES_256_BitSlice_aes256_ctr_decrypt */

/* SNIPPET_START: Hacl_AES_128_NI_aes128_init */

inline void
Hacl_AES_128_NI_aes128_init(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *key, uint8_t *nonce)
{
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *uu____0 = kex;
  uu____0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(key);
  Lib_IntVector_Intrinsics_vec128 *prev = kex;
  Lib_IntVector_Intrinsics_vec128 *next = kex + klen;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev[0U], (uint8_t)0x01U);
  next[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key1 = prev[0U];
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key4 =
    Lib_IntVector_Intrinsics_vec128_xor(key3,
      Lib_IntVector_Intrinsics_vec128_shift_left(key3, (uint32_t)32U));
  next[0U] = Lib_IntVector_Intrinsics_vec128_xor(next[0U], key4);
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex + klen;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex + (uint32_t)2U * klen;
  Lib_IntVector_Intrinsics_vec128
  v1 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x02U);
  next1[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v1,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key10 = prev1[0U];
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key40 =
    Lib_IntVector_Intrinsics_vec128_xor(key30,
      Lib_IntVector_Intrinsics_vec128_shift_left(key30, (uint32_t)32U));
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(next1[0U], key40);
  Lib_IntVector_Intrinsics_vec128 *prev2 = kex + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next2 = kex + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v2 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev2[0U], (uint8_t)0x04U);
  next2[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v2,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key11 = prev2[0U];
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key41 =
    Lib_IntVector_Intrinsics_vec128_xor(key31,
      Lib_IntVector_Intrinsics_vec128_shift_left(key31, (uint32_t)32U));
  next2[0U] = Lib_IntVector_Intrinsics_vec128_xor(next2[0U], key41);
  Lib_IntVector_Intrinsics_vec128 *prev3 = kex + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128 *next3 = kex + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128
  v3 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev3[0U], (uint8_t)0x08U);
  next3[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v3,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key12 = prev3[0U];
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key42 =
    Lib_IntVector_Intrinsics_vec128_xor(key32,
      Lib_IntVector_Intrinsics_vec128_shift_left(key32, (uint32_t)32U));
  next3[0U] = Lib_IntVector_Intrinsics_vec128_xor(next3[0U], key42);
  Lib_IntVector_Intrinsics_vec128 *prev4 = kex + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next4 = kex + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev4[0U], (uint8_t)0x10U);
  next4[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key13 = prev4[0U];
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key43 =
    Lib_IntVector_Intrinsics_vec128_xor(key33,
      Lib_IntVector_Intrinsics_vec128_shift_left(key33, (uint32_t)32U));
  next4[0U] = Lib_IntVector_Intrinsics_vec128_xor(next4[0U], key43);
  Lib_IntVector_Intrinsics_vec128 *prev5 = kex + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128 *next5 = kex + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev5[0U], (uint8_t)0x20U);
  next5[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key14 = prev5[0U];
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key44 =
    Lib_IntVector_Intrinsics_vec128_xor(key34,
      Lib_IntVector_Intrinsics_vec128_shift_left(key34, (uint32_t)32U));
  next5[0U] = Lib_IntVector_Intrinsics_vec128_xor(next5[0U], key44);
  Lib_IntVector_Intrinsics_vec128 *prev6 = kex + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next6 = kex + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev6[0U], (uint8_t)0x40U);
  next6[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key15 = prev6[0U];
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key45 =
    Lib_IntVector_Intrinsics_vec128_xor(key35,
      Lib_IntVector_Intrinsics_vec128_shift_left(key35, (uint32_t)32U));
  next6[0U] = Lib_IntVector_Intrinsics_vec128_xor(next6[0U], key45);
  Lib_IntVector_Intrinsics_vec128 *prev7 = kex + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128 *next7 = kex + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev7[0U], (uint8_t)0x80U);
  next7[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key16 = prev7[0U];
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key46 =
    Lib_IntVector_Intrinsics_vec128_xor(key36,
      Lib_IntVector_Intrinsics_vec128_shift_left(key36, (uint32_t)32U));
  next7[0U] = Lib_IntVector_Intrinsics_vec128_xor(next7[0U], key46);
  Lib_IntVector_Intrinsics_vec128 *prev8 = kex + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next8 = kex + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev8[0U], (uint8_t)0x1bU);
  next8[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev8[0U];
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key47 =
    Lib_IntVector_Intrinsics_vec128_xor(key37,
      Lib_IntVector_Intrinsics_vec128_shift_left(key37, (uint32_t)32U));
  next8[0U] = Lib_IntVector_Intrinsics_vec128_xor(next8[0U], key47);
  Lib_IntVector_Intrinsics_vec128 *prev9 = kex + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128 *next9 = kex + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev9[0U], (uint8_t)0x36U);
  next9[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key18 = prev9[0U];
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key48 =
    Lib_IntVector_Intrinsics_vec128_xor(key38,
      Lib_IntVector_Intrinsics_vec128_shift_left(key38, (uint32_t)32U));
  next9[0U] = Lib_IntVector_Intrinsics_vec128_xor(next9[0U], key48);
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, (uint32_t)12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
}

/* SNIPPET_END: Hacl_AES_128_NI_aes128_init */

/* SNIPPET_START: Hacl_AES_128_NI_aes128_set_nonce */

inline void
Hacl_AES_128_NI_aes128_set_nonce(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *nonce)
{
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, (uint32_t)12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
}

/* SNIPPET_END: Hacl_AES_128_NI_aes128_set_nonce */

/* SNIPPET_START: Hacl_AES_128_NI_aes128_key_block */

inline void
Hacl_AES_128_NI_aes128_key_block(
  uint8_t *kb,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t counter
)
{
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  Lib_IntVector_Intrinsics_vec128 st[4U];
  for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
    st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  uint32_t counter1 = counter;
  uint32_t counter0 = htobe32(counter1);
  uint32_t counter11 = htobe32(counter1 + (uint32_t)1U);
  uint32_t counter2 = htobe32(counter1 + (uint32_t)2U);
  uint32_t counter3 = htobe32(counter1 + (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
  st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
  st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter11, (uint32_t)3U);
  st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
  st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *k0 = kex;
  Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
  Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen;
  st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
  st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
  st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
  st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)9U; i++)
  {
    Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
  }
  st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
  st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
  st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
  st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
  Lib_IntVector_Intrinsics_vec128_store128_le(kb, st[0U]);
}

/* SNIPPET_END: Hacl_AES_128_NI_aes128_key_block */

/* SNIPPET_START: Hacl_AES_128_NI_aes128_update4 */

void
Hacl_AES_128_NI_aes128_update4(
  uint8_t *out,
  uint8_t *inp,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t ctr
)
{
  Lib_IntVector_Intrinsics_vec128 st[4U];
  for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
    st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint32_t counter = ctr;
  uint32_t counter0 = htobe32(counter);
  uint32_t counter1 = htobe32(counter + (uint32_t)1U);
  uint32_t counter2 = htobe32(counter + (uint32_t)2U);
  uint32_t counter3 = htobe32(counter + (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
  st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
  st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
  st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
  st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *k0 = kex;
  Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
  Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen;
  st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
  st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
  st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
  st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)9U; i++)
  {
    Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
  }
  st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
  st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
  st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
  st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
  Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(inp);
  Lib_IntVector_Intrinsics_vec128
  v1 = Lib_IntVector_Intrinsics_vec128_load128_le(inp + (uint32_t)16U);
  Lib_IntVector_Intrinsics_vec128
  v2 = Lib_IntVector_Intrinsics_vec128_load128_le(inp + (uint32_t)32U);
  Lib_IntVector_Intrinsics_vec128
  v3 = Lib_IntVector_Intrinsics_vec128_load128_le(inp + (uint32_t)48U);
  Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
  Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
  Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
  Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
  Lib_IntVector_Intrinsics_vec128_store128_le(out, v01);
  Lib_IntVector_Intrinsics_vec128_store128_le(out + (uint32_t)16U, v11);
  Lib_IntVector_Intrinsics_vec128_store128_le(out + (uint32_t)32U, v21);
  Lib_IntVector_Intrinsics_vec128_store128_le(out + (uint32_t)48U, v31);
}

/* SNIPPET_END: Hacl_AES_128_NI_aes128_update4 */

/* SNIPPET_START: Hacl_AES_128_NI_aes128_ctr */

void
Hacl_AES_128_NI_aes128_ctr(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t c
)
{
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = c + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)9U; i0++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i0 * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(ib);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)48U, v31);
  }
  uint32_t rem = len % (uint32_t)64U;
  uint8_t last[64U];
  if (rem > (uint32_t)0U)
  {
    uint32_t ctr = c + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    uint8_t init = (uint8_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      last[i] = init;
    }
    memcpy(last, ib, rem * sizeof (uint8_t));
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)9U; i++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)48U, v31);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: Hacl_AES_128_NI_aes128_ctr */

/* SNIPPET_START: Hacl_AES_128_NI_aes128_ctr_encrypt */

inline void
Hacl_AES_128_NI_aes128_ctr_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
    (uint32_t)1U + (uint32_t)11U * (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec128 ctx[(uint32_t)1U + (uint32_t)11U * (uint32_t)1U];
  for (uint32_t _i = 0U; _i < (uint32_t)1U + (uint32_t)11U * (uint32_t)1U; ++_i)
    ctx[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *uu____0 = kex0;
  uu____0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  Lib_IntVector_Intrinsics_vec128 *prev = kex0;
  Lib_IntVector_Intrinsics_vec128 *next = kex0 + klen;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev[0U], (uint8_t)0x01U);
  next[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key = prev[0U];
  Lib_IntVector_Intrinsics_vec128
  key1 =
    Lib_IntVector_Intrinsics_vec128_xor(key,
      Lib_IntVector_Intrinsics_vec128_shift_left(key, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, (uint32_t)32U));
  next[0U] = Lib_IntVector_Intrinsics_vec128_xor(next[0U], key3);
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex0 + klen;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + (uint32_t)2U * klen;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x02U);
  next1[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key0 = prev1[0U];
  Lib_IntVector_Intrinsics_vec128
  key10 =
    Lib_IntVector_Intrinsics_vec128_xor(key0,
      Lib_IntVector_Intrinsics_vec128_shift_left(key0, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, (uint32_t)32U));
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(next1[0U], key30);
  Lib_IntVector_Intrinsics_vec128 *prev2 = kex0 + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next2 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev2[0U], (uint8_t)0x04U);
  next2[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev2[0U];
  Lib_IntVector_Intrinsics_vec128
  key11 =
    Lib_IntVector_Intrinsics_vec128_xor(key4,
      Lib_IntVector_Intrinsics_vec128_shift_left(key4, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, (uint32_t)32U));
  next2[0U] = Lib_IntVector_Intrinsics_vec128_xor(next2[0U], key31);
  Lib_IntVector_Intrinsics_vec128 *prev3 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128 *next3 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev3[0U], (uint8_t)0x08U);
  next3[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev3[0U];
  Lib_IntVector_Intrinsics_vec128
  key12 =
    Lib_IntVector_Intrinsics_vec128_xor(key5,
      Lib_IntVector_Intrinsics_vec128_shift_left(key5, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, (uint32_t)32U));
  next3[0U] = Lib_IntVector_Intrinsics_vec128_xor(next3[0U], key32);
  Lib_IntVector_Intrinsics_vec128 *prev4 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next4 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev4[0U], (uint8_t)0x10U);
  next4[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev4[0U];
  Lib_IntVector_Intrinsics_vec128
  key13 =
    Lib_IntVector_Intrinsics_vec128_xor(key6,
      Lib_IntVector_Intrinsics_vec128_shift_left(key6, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, (uint32_t)32U));
  next4[0U] = Lib_IntVector_Intrinsics_vec128_xor(next4[0U], key33);
  Lib_IntVector_Intrinsics_vec128 *prev5 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128 *next5 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev5[0U], (uint8_t)0x20U);
  next5[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev5[0U];
  Lib_IntVector_Intrinsics_vec128
  key14 =
    Lib_IntVector_Intrinsics_vec128_xor(key7,
      Lib_IntVector_Intrinsics_vec128_shift_left(key7, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, (uint32_t)32U));
  next5[0U] = Lib_IntVector_Intrinsics_vec128_xor(next5[0U], key34);
  Lib_IntVector_Intrinsics_vec128 *prev6 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next6 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev6[0U], (uint8_t)0x40U);
  next6[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v9,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev6[0U];
  Lib_IntVector_Intrinsics_vec128
  key15 =
    Lib_IntVector_Intrinsics_vec128_xor(key8,
      Lib_IntVector_Intrinsics_vec128_shift_left(key8, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, (uint32_t)32U));
  next6[0U] = Lib_IntVector_Intrinsics_vec128_xor(next6[0U], key35);
  Lib_IntVector_Intrinsics_vec128 *prev7 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128 *next7 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev7[0U], (uint8_t)0x80U);
  next7[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v10,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev7[0U];
  Lib_IntVector_Intrinsics_vec128
  key16 =
    Lib_IntVector_Intrinsics_vec128_xor(key9,
      Lib_IntVector_Intrinsics_vec128_shift_left(key9, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, (uint32_t)32U));
  next7[0U] = Lib_IntVector_Intrinsics_vec128_xor(next7[0U], key36);
  Lib_IntVector_Intrinsics_vec128 *prev8 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next8 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev8[0U], (uint8_t)0x1bU);
  next8[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v12,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev8[0U];
  Lib_IntVector_Intrinsics_vec128
  key18 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, (uint32_t)32U));
  next8[0U] = Lib_IntVector_Intrinsics_vec128_xor(next8[0U], key37);
  Lib_IntVector_Intrinsics_vec128 *prev9 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128 *next9 = kex0 + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev9[0U], (uint8_t)0x36U);
  next9[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev9[0U];
  Lib_IntVector_Intrinsics_vec128
  key110 =
    Lib_IntVector_Intrinsics_vec128_xor(key19,
      Lib_IntVector_Intrinsics_vec128_shift_left(key19, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key110,
      Lib_IntVector_Intrinsics_vec128_shift_left(key110, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, (uint32_t)32U));
  next9[0U] = Lib_IntVector_Intrinsics_vec128_xor(next9[0U], key38);
  uint8_t nb[16U] = { 0U };
  memcpy(nb, n, (uint32_t)12U * sizeof (uint8_t));
  n10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = c + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)9U; i0++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i0 * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(ib);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)48U, v31);
  }
  uint32_t rem = len % (uint32_t)64U;
  uint8_t last[64U];
  if (rem > (uint32_t)0U)
  {
    uint32_t ctr = c + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    uint8_t init = (uint8_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      last[i] = init;
    }
    memcpy(last, ib, rem * sizeof (uint8_t));
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)9U; i++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)48U, v31);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: Hacl_AES_128_NI_aes128_ctr_encrypt */

/* SNIPPET_START: Hacl_AES_128_NI_aes128_ctr_decrypt */

inline void
Hacl_AES_128_NI_aes128_ctr_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
    (uint32_t)1U + (uint32_t)11U * (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec128 ctx[(uint32_t)1U + (uint32_t)11U * (uint32_t)1U];
  for (uint32_t _i = 0U; _i < (uint32_t)1U + (uint32_t)11U * (uint32_t)1U; ++_i)
    ctx[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *uu____0 = kex0;
  uu____0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  Lib_IntVector_Intrinsics_vec128 *prev = kex0;
  Lib_IntVector_Intrinsics_vec128 *next = kex0 + klen;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev[0U], (uint8_t)0x01U);
  next[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key = prev[0U];
  Lib_IntVector_Intrinsics_vec128
  key1 =
    Lib_IntVector_Intrinsics_vec128_xor(key,
      Lib_IntVector_Intrinsics_vec128_shift_left(key, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, (uint32_t)32U));
  next[0U] = Lib_IntVector_Intrinsics_vec128_xor(next[0U], key3);
  Lib_IntVector_Intrinsics_vec128 *prev1 = kex0 + klen;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + (uint32_t)2U * klen;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x02U);
  next1[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key0 = prev1[0U];
  Lib_IntVector_Intrinsics_vec128
  key10 =
    Lib_IntVector_Intrinsics_vec128_xor(key0,
      Lib_IntVector_Intrinsics_vec128_shift_left(key0, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, (uint32_t)32U));
  next1[0U] = Lib_IntVector_Intrinsics_vec128_xor(next1[0U], key30);
  Lib_IntVector_Intrinsics_vec128 *prev2 = kex0 + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next2 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev2[0U], (uint8_t)0x04U);
  next2[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev2[0U];
  Lib_IntVector_Intrinsics_vec128
  key11 =
    Lib_IntVector_Intrinsics_vec128_xor(key4,
      Lib_IntVector_Intrinsics_vec128_shift_left(key4, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, (uint32_t)32U));
  next2[0U] = Lib_IntVector_Intrinsics_vec128_xor(next2[0U], key31);
  Lib_IntVector_Intrinsics_vec128 *prev3 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128 *next3 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev3[0U], (uint8_t)0x08U);
  next3[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev3[0U];
  Lib_IntVector_Intrinsics_vec128
  key12 =
    Lib_IntVector_Intrinsics_vec128_xor(key5,
      Lib_IntVector_Intrinsics_vec128_shift_left(key5, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, (uint32_t)32U));
  next3[0U] = Lib_IntVector_Intrinsics_vec128_xor(next3[0U], key32);
  Lib_IntVector_Intrinsics_vec128 *prev4 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next4 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev4[0U], (uint8_t)0x10U);
  next4[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev4[0U];
  Lib_IntVector_Intrinsics_vec128
  key13 =
    Lib_IntVector_Intrinsics_vec128_xor(key6,
      Lib_IntVector_Intrinsics_vec128_shift_left(key6, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, (uint32_t)32U));
  next4[0U] = Lib_IntVector_Intrinsics_vec128_xor(next4[0U], key33);
  Lib_IntVector_Intrinsics_vec128 *prev5 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128 *next5 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev5[0U], (uint8_t)0x20U);
  next5[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev5[0U];
  Lib_IntVector_Intrinsics_vec128
  key14 =
    Lib_IntVector_Intrinsics_vec128_xor(key7,
      Lib_IntVector_Intrinsics_vec128_shift_left(key7, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, (uint32_t)32U));
  next5[0U] = Lib_IntVector_Intrinsics_vec128_xor(next5[0U], key34);
  Lib_IntVector_Intrinsics_vec128 *prev6 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next6 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev6[0U], (uint8_t)0x40U);
  next6[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v9,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev6[0U];
  Lib_IntVector_Intrinsics_vec128
  key15 =
    Lib_IntVector_Intrinsics_vec128_xor(key8,
      Lib_IntVector_Intrinsics_vec128_shift_left(key8, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, (uint32_t)32U));
  next6[0U] = Lib_IntVector_Intrinsics_vec128_xor(next6[0U], key35);
  Lib_IntVector_Intrinsics_vec128 *prev7 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128 *next7 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev7[0U], (uint8_t)0x80U);
  next7[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v10,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev7[0U];
  Lib_IntVector_Intrinsics_vec128
  key16 =
    Lib_IntVector_Intrinsics_vec128_xor(key9,
      Lib_IntVector_Intrinsics_vec128_shift_left(key9, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, (uint32_t)32U));
  next7[0U] = Lib_IntVector_Intrinsics_vec128_xor(next7[0U], key36);
  Lib_IntVector_Intrinsics_vec128 *prev8 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next8 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev8[0U], (uint8_t)0x1bU);
  next8[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v12,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev8[0U];
  Lib_IntVector_Intrinsics_vec128
  key18 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, (uint32_t)32U));
  next8[0U] = Lib_IntVector_Intrinsics_vec128_xor(next8[0U], key37);
  Lib_IntVector_Intrinsics_vec128 *prev9 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128 *next9 = kex0 + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev9[0U], (uint8_t)0x36U);
  next9[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev9[0U];
  Lib_IntVector_Intrinsics_vec128
  key110 =
    Lib_IntVector_Intrinsics_vec128_xor(key19,
      Lib_IntVector_Intrinsics_vec128_shift_left(key19, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key110,
      Lib_IntVector_Intrinsics_vec128_shift_left(key110, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, (uint32_t)32U));
  next9[0U] = Lib_IntVector_Intrinsics_vec128_xor(next9[0U], key38);
  uint8_t nb[16U] = { 0U };
  memcpy(nb, n, (uint32_t)12U * sizeof (uint8_t));
  n10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = c + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)9U; i0++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i0 * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(ib);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)48U, v31);
  }
  uint32_t rem = len % (uint32_t)64U;
  uint8_t last[64U];
  if (rem > (uint32_t)0U)
  {
    uint32_t ctr = c + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    uint8_t init = (uint8_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      last[i] = init;
    }
    memcpy(last, ib, rem * sizeof (uint8_t));
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)10U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)9U; i++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)48U, v31);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: Hacl_AES_128_NI_aes128_ctr_decrypt */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_init */

inline void
Hacl_AES_256_NI_aes256_init(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *key, uint8_t *nonce)
{
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex + klen;
  next0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(key);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(key + (uint32_t)16U);
  Lib_IntVector_Intrinsics_vec128 *prev0 = next0;
  Lib_IntVector_Intrinsics_vec128 *prev1 = next1;
  Lib_IntVector_Intrinsics_vec128 *next01 = kex + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next11 = kex + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x01U);
  next01[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key1 = prev0[0U];
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key4 =
    Lib_IntVector_Intrinsics_vec128_xor(key3,
      Lib_IntVector_Intrinsics_vec128_shift_left(key3, (uint32_t)32U));
  next01[0U] = Lib_IntVector_Intrinsics_vec128_xor(next01[0U], key4);
  Lib_IntVector_Intrinsics_vec128
  v1 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next01[0U], (uint8_t)0U);
  next11[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v1,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key10 = prev1[0U];
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key40 =
    Lib_IntVector_Intrinsics_vec128_xor(key30,
      Lib_IntVector_Intrinsics_vec128_shift_left(key30, (uint32_t)32U));
  next11[0U] = Lib_IntVector_Intrinsics_vec128_xor(next11[0U], key40);
  Lib_IntVector_Intrinsics_vec128 *prev01 = next01;
  Lib_IntVector_Intrinsics_vec128 *prev11 = next11;
  Lib_IntVector_Intrinsics_vec128 *next02 = kex + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next12 = kex + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v2 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev11[0U], (uint8_t)0x02U);
  next02[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v2,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key11 = prev01[0U];
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key41 =
    Lib_IntVector_Intrinsics_vec128_xor(key31,
      Lib_IntVector_Intrinsics_vec128_shift_left(key31, (uint32_t)32U));
  next02[0U] = Lib_IntVector_Intrinsics_vec128_xor(next02[0U], key41);
  Lib_IntVector_Intrinsics_vec128
  v3 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next02[0U], (uint8_t)0U);
  next12[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v3,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key12 = prev11[0U];
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key42 =
    Lib_IntVector_Intrinsics_vec128_xor(key32,
      Lib_IntVector_Intrinsics_vec128_shift_left(key32, (uint32_t)32U));
  next12[0U] = Lib_IntVector_Intrinsics_vec128_xor(next12[0U], key42);
  Lib_IntVector_Intrinsics_vec128 *prev02 = next02;
  Lib_IntVector_Intrinsics_vec128 *prev12 = next12;
  Lib_IntVector_Intrinsics_vec128 *next03 = kex + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next13 = kex + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev12[0U], (uint8_t)0x04U);
  next03[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key13 = prev02[0U];
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key43 =
    Lib_IntVector_Intrinsics_vec128_xor(key33,
      Lib_IntVector_Intrinsics_vec128_shift_left(key33, (uint32_t)32U));
  next03[0U] = Lib_IntVector_Intrinsics_vec128_xor(next03[0U], key43);
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next03[0U], (uint8_t)0U);
  next13[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key14 = prev12[0U];
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key44 =
    Lib_IntVector_Intrinsics_vec128_xor(key34,
      Lib_IntVector_Intrinsics_vec128_shift_left(key34, (uint32_t)32U));
  next13[0U] = Lib_IntVector_Intrinsics_vec128_xor(next13[0U], key44);
  Lib_IntVector_Intrinsics_vec128 *prev03 = next03;
  Lib_IntVector_Intrinsics_vec128 *prev13 = next13;
  Lib_IntVector_Intrinsics_vec128 *next04 = kex + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next14 = kex + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev13[0U], (uint8_t)0x08U);
  next04[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key15 = prev03[0U];
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key45 =
    Lib_IntVector_Intrinsics_vec128_xor(key35,
      Lib_IntVector_Intrinsics_vec128_shift_left(key35, (uint32_t)32U));
  next04[0U] = Lib_IntVector_Intrinsics_vec128_xor(next04[0U], key45);
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next04[0U], (uint8_t)0U);
  next14[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key16 = prev13[0U];
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key46 =
    Lib_IntVector_Intrinsics_vec128_xor(key36,
      Lib_IntVector_Intrinsics_vec128_shift_left(key36, (uint32_t)32U));
  next14[0U] = Lib_IntVector_Intrinsics_vec128_xor(next14[0U], key46);
  Lib_IntVector_Intrinsics_vec128 *prev04 = next04;
  Lib_IntVector_Intrinsics_vec128 *prev14 = next14;
  Lib_IntVector_Intrinsics_vec128 *next05 = kex + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128 *next15 = kex + klen * (uint32_t)11U;
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev14[0U], (uint8_t)0x10U);
  next05[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev04[0U];
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key47 =
    Lib_IntVector_Intrinsics_vec128_xor(key37,
      Lib_IntVector_Intrinsics_vec128_shift_left(key37, (uint32_t)32U));
  next05[0U] = Lib_IntVector_Intrinsics_vec128_xor(next05[0U], key47);
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next05[0U], (uint8_t)0U);
  next15[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v9,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key18 = prev14[0U];
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key48 =
    Lib_IntVector_Intrinsics_vec128_xor(key38,
      Lib_IntVector_Intrinsics_vec128_shift_left(key38, (uint32_t)32U));
  next15[0U] = Lib_IntVector_Intrinsics_vec128_xor(next15[0U], key48);
  Lib_IntVector_Intrinsics_vec128 *prev05 = next05;
  Lib_IntVector_Intrinsics_vec128 *prev15 = next15;
  Lib_IntVector_Intrinsics_vec128 *next06 = kex + klen * (uint32_t)12U;
  Lib_IntVector_Intrinsics_vec128 *next16 = kex + klen * (uint32_t)13U;
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev15[0U], (uint8_t)0x20U);
  next06[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v10,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev05[0U];
  Lib_IntVector_Intrinsics_vec128
  key29 =
    Lib_IntVector_Intrinsics_vec128_xor(key19,
      Lib_IntVector_Intrinsics_vec128_shift_left(key19, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key39 =
    Lib_IntVector_Intrinsics_vec128_xor(key29,
      Lib_IntVector_Intrinsics_vec128_shift_left(key29, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key49 =
    Lib_IntVector_Intrinsics_vec128_xor(key39,
      Lib_IntVector_Intrinsics_vec128_shift_left(key39, (uint32_t)32U));
  next06[0U] = Lib_IntVector_Intrinsics_vec128_xor(next06[0U], key49);
  Lib_IntVector_Intrinsics_vec128
  v11 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next06[0U], (uint8_t)0U);
  next16[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v11,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key110 = prev15[0U];
  Lib_IntVector_Intrinsics_vec128
  key210 =
    Lib_IntVector_Intrinsics_vec128_xor(key110,
      Lib_IntVector_Intrinsics_vec128_shift_left(key110, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key310 =
    Lib_IntVector_Intrinsics_vec128_xor(key210,
      Lib_IntVector_Intrinsics_vec128_shift_left(key210, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key410 =
    Lib_IntVector_Intrinsics_vec128_xor(key310,
      Lib_IntVector_Intrinsics_vec128_shift_left(key310, (uint32_t)32U));
  next16[0U] = Lib_IntVector_Intrinsics_vec128_xor(next16[0U], key410);
  Lib_IntVector_Intrinsics_vec128 *prev06 = next06;
  Lib_IntVector_Intrinsics_vec128 *prev16 = next16;
  Lib_IntVector_Intrinsics_vec128 *next07 = kex + klen * (uint32_t)14U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev16[0U], (uint8_t)0x40U);
  next07[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key111 = prev06[0U];
  Lib_IntVector_Intrinsics_vec128
  key211 =
    Lib_IntVector_Intrinsics_vec128_xor(key111,
      Lib_IntVector_Intrinsics_vec128_shift_left(key111, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key311 =
    Lib_IntVector_Intrinsics_vec128_xor(key211,
      Lib_IntVector_Intrinsics_vec128_shift_left(key211, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key411 =
    Lib_IntVector_Intrinsics_vec128_xor(key311,
      Lib_IntVector_Intrinsics_vec128_shift_left(key311, (uint32_t)32U));
  next07[0U] = Lib_IntVector_Intrinsics_vec128_xor(next07[0U], key411);
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, (uint32_t)12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_init */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_encrypt_block */

inline void
Hacl_AES_256_NI_aes256_encrypt_block(
  uint8_t *ob,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint8_t *ib
)
{
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 st[4U];
  for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
    st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  st[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(ib);
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *k0 = kex;
  Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
  Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen;
  st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
  st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
  st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
  st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)13U; i++)
  {
    Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
  }
  st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
  st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
  st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
  st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
  Lib_IntVector_Intrinsics_vec128_store128_le(ob, st[0U]);
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_encrypt_block */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_set_nonce */

inline void
Hacl_AES_256_NI_aes256_set_nonce(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *nonce)
{
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint8_t nb[16U] = { 0U };
  memcpy(nb, nonce, (uint32_t)12U * sizeof (uint8_t));
  n[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_set_nonce */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_key_block */

inline void
Hacl_AES_256_NI_aes256_key_block(
  uint8_t *kb,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t counter
)
{
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  Lib_IntVector_Intrinsics_vec128 st[4U];
  for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
    st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  uint32_t counter1 = counter;
  uint32_t counter0 = htobe32(counter1);
  uint32_t counter11 = htobe32(counter1 + (uint32_t)1U);
  uint32_t counter2 = htobe32(counter1 + (uint32_t)2U);
  uint32_t counter3 = htobe32(counter1 + (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
  st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
  st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter11, (uint32_t)3U);
  st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
  st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *k0 = kex;
  Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
  Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen;
  st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
  st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
  st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
  st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)13U; i++)
  {
    Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
  }
  st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
  st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
  st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
  st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
  Lib_IntVector_Intrinsics_vec128_store128_le(kb, st[0U]);
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_key_block */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_update4 */

void
Hacl_AES_256_NI_aes256_update4(
  uint8_t *out,
  uint8_t *inp,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t ctr
)
{
  Lib_IntVector_Intrinsics_vec128 st[4U];
  for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
    st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n = ctx;
  uint32_t counter = ctr;
  uint32_t counter0 = htobe32(counter);
  uint32_t counter1 = htobe32(counter + (uint32_t)1U);
  uint32_t counter2 = htobe32(counter + (uint32_t)2U);
  uint32_t counter3 = htobe32(counter + (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
  st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
  st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
  st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
  st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *k0 = kex;
  Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
  Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen;
  st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
  st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
  st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
  st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)13U; i++)
  {
    Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
  }
  st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
  st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
  st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
  st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
  Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(inp);
  Lib_IntVector_Intrinsics_vec128
  v1 = Lib_IntVector_Intrinsics_vec128_load128_le(inp + (uint32_t)16U);
  Lib_IntVector_Intrinsics_vec128
  v2 = Lib_IntVector_Intrinsics_vec128_load128_le(inp + (uint32_t)32U);
  Lib_IntVector_Intrinsics_vec128
  v3 = Lib_IntVector_Intrinsics_vec128_load128_le(inp + (uint32_t)48U);
  Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
  Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
  Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
  Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
  Lib_IntVector_Intrinsics_vec128_store128_le(out, v01);
  Lib_IntVector_Intrinsics_vec128_store128_le(out + (uint32_t)16U, v11);
  Lib_IntVector_Intrinsics_vec128_store128_le(out + (uint32_t)32U, v21);
  Lib_IntVector_Intrinsics_vec128_store128_le(out + (uint32_t)48U, v31);
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_update4 */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_ctr */

inline void
Hacl_AES_256_NI_aes256_ctr(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t c
)
{
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = c + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)13U; i0++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i0 * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(ib);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)48U, v31);
  }
  uint32_t rem = len % (uint32_t)64U;
  uint8_t last[64U];
  if (rem > (uint32_t)0U)
  {
    uint32_t ctr = c + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    uint8_t init = (uint8_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      last[i] = init;
    }
    memcpy(last, ib, rem * sizeof (uint8_t));
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)13U; i++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v0 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v0, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)48U, v31);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_ctr */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_ctr_encrypt */

inline void
Hacl_AES_256_NI_aes256_ctr_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
    (uint32_t)1U + (uint32_t)15U * (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec128 ctx[(uint32_t)1U + (uint32_t)15U * (uint32_t)1U];
  for (uint32_t _i = 0U; _i < (uint32_t)1U + (uint32_t)15U * (uint32_t)1U; ++_i)
    ctx[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex0;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + klen;
  next0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k + (uint32_t)16U);
  Lib_IntVector_Intrinsics_vec128 *prev0 = next0;
  Lib_IntVector_Intrinsics_vec128 *prev1 = next1;
  Lib_IntVector_Intrinsics_vec128 *next01 = kex0 + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next11 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x01U);
  next01[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key = prev0[0U];
  Lib_IntVector_Intrinsics_vec128
  key1 =
    Lib_IntVector_Intrinsics_vec128_xor(key,
      Lib_IntVector_Intrinsics_vec128_shift_left(key, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, (uint32_t)32U));
  next01[0U] = Lib_IntVector_Intrinsics_vec128_xor(next01[0U], key3);
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next01[0U], (uint8_t)0U);
  next11[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key0 = prev1[0U];
  Lib_IntVector_Intrinsics_vec128
  key10 =
    Lib_IntVector_Intrinsics_vec128_xor(key0,
      Lib_IntVector_Intrinsics_vec128_shift_left(key0, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, (uint32_t)32U));
  next11[0U] = Lib_IntVector_Intrinsics_vec128_xor(next11[0U], key30);
  Lib_IntVector_Intrinsics_vec128 *prev01 = next01;
  Lib_IntVector_Intrinsics_vec128 *prev11 = next11;
  Lib_IntVector_Intrinsics_vec128 *next02 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next12 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev11[0U], (uint8_t)0x02U);
  next02[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev01[0U];
  Lib_IntVector_Intrinsics_vec128
  key11 =
    Lib_IntVector_Intrinsics_vec128_xor(key4,
      Lib_IntVector_Intrinsics_vec128_shift_left(key4, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, (uint32_t)32U));
  next02[0U] = Lib_IntVector_Intrinsics_vec128_xor(next02[0U], key31);
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next02[0U], (uint8_t)0U);
  next12[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev11[0U];
  Lib_IntVector_Intrinsics_vec128
  key12 =
    Lib_IntVector_Intrinsics_vec128_xor(key5,
      Lib_IntVector_Intrinsics_vec128_shift_left(key5, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, (uint32_t)32U));
  next12[0U] = Lib_IntVector_Intrinsics_vec128_xor(next12[0U], key32);
  Lib_IntVector_Intrinsics_vec128 *prev02 = next02;
  Lib_IntVector_Intrinsics_vec128 *prev12 = next12;
  Lib_IntVector_Intrinsics_vec128 *next03 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next13 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev12[0U], (uint8_t)0x04U);
  next03[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev02[0U];
  Lib_IntVector_Intrinsics_vec128
  key13 =
    Lib_IntVector_Intrinsics_vec128_xor(key6,
      Lib_IntVector_Intrinsics_vec128_shift_left(key6, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, (uint32_t)32U));
  next03[0U] = Lib_IntVector_Intrinsics_vec128_xor(next03[0U], key33);
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next03[0U], (uint8_t)0U);
  next13[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev12[0U];
  Lib_IntVector_Intrinsics_vec128
  key14 =
    Lib_IntVector_Intrinsics_vec128_xor(key7,
      Lib_IntVector_Intrinsics_vec128_shift_left(key7, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, (uint32_t)32U));
  next13[0U] = Lib_IntVector_Intrinsics_vec128_xor(next13[0U], key34);
  Lib_IntVector_Intrinsics_vec128 *prev03 = next03;
  Lib_IntVector_Intrinsics_vec128 *prev13 = next13;
  Lib_IntVector_Intrinsics_vec128 *next04 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next14 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev13[0U], (uint8_t)0x08U);
  next04[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v9,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev03[0U];
  Lib_IntVector_Intrinsics_vec128
  key15 =
    Lib_IntVector_Intrinsics_vec128_xor(key8,
      Lib_IntVector_Intrinsics_vec128_shift_left(key8, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, (uint32_t)32U));
  next04[0U] = Lib_IntVector_Intrinsics_vec128_xor(next04[0U], key35);
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next04[0U], (uint8_t)0U);
  next14[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v10,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev13[0U];
  Lib_IntVector_Intrinsics_vec128
  key16 =
    Lib_IntVector_Intrinsics_vec128_xor(key9,
      Lib_IntVector_Intrinsics_vec128_shift_left(key9, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, (uint32_t)32U));
  next14[0U] = Lib_IntVector_Intrinsics_vec128_xor(next14[0U], key36);
  Lib_IntVector_Intrinsics_vec128 *prev04 = next04;
  Lib_IntVector_Intrinsics_vec128 *prev14 = next14;
  Lib_IntVector_Intrinsics_vec128 *next05 = kex0 + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128 *next15 = kex0 + klen * (uint32_t)11U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev14[0U], (uint8_t)0x10U);
  next05[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v12,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev04[0U];
  Lib_IntVector_Intrinsics_vec128
  key18 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, (uint32_t)32U));
  next05[0U] = Lib_IntVector_Intrinsics_vec128_xor(next05[0U], key37);
  Lib_IntVector_Intrinsics_vec128
  v13 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next05[0U], (uint8_t)0U);
  next15[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v13,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev14[0U];
  Lib_IntVector_Intrinsics_vec128
  key110 =
    Lib_IntVector_Intrinsics_vec128_xor(key19,
      Lib_IntVector_Intrinsics_vec128_shift_left(key19, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key110,
      Lib_IntVector_Intrinsics_vec128_shift_left(key110, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, (uint32_t)32U));
  next15[0U] = Lib_IntVector_Intrinsics_vec128_xor(next15[0U], key38);
  Lib_IntVector_Intrinsics_vec128 *prev05 = next05;
  Lib_IntVector_Intrinsics_vec128 *prev15 = next15;
  Lib_IntVector_Intrinsics_vec128 *next06 = kex0 + klen * (uint32_t)12U;
  Lib_IntVector_Intrinsics_vec128 *next16 = kex0 + klen * (uint32_t)13U;
  Lib_IntVector_Intrinsics_vec128
  v14 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev15[0U], (uint8_t)0x20U);
  next06[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v14,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key29 = prev05[0U];
  Lib_IntVector_Intrinsics_vec128
  key111 =
    Lib_IntVector_Intrinsics_vec128_xor(key29,
      Lib_IntVector_Intrinsics_vec128_shift_left(key29, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key210 =
    Lib_IntVector_Intrinsics_vec128_xor(key111,
      Lib_IntVector_Intrinsics_vec128_shift_left(key111, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key39 =
    Lib_IntVector_Intrinsics_vec128_xor(key210,
      Lib_IntVector_Intrinsics_vec128_shift_left(key210, (uint32_t)32U));
  next06[0U] = Lib_IntVector_Intrinsics_vec128_xor(next06[0U], key39);
  Lib_IntVector_Intrinsics_vec128
  v15 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next06[0U], (uint8_t)0U);
  next16[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v15,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key40 = prev15[0U];
  Lib_IntVector_Intrinsics_vec128
  key112 =
    Lib_IntVector_Intrinsics_vec128_xor(key40,
      Lib_IntVector_Intrinsics_vec128_shift_left(key40, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key211 =
    Lib_IntVector_Intrinsics_vec128_xor(key112,
      Lib_IntVector_Intrinsics_vec128_shift_left(key112, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key310 =
    Lib_IntVector_Intrinsics_vec128_xor(key211,
      Lib_IntVector_Intrinsics_vec128_shift_left(key211, (uint32_t)32U));
  next16[0U] = Lib_IntVector_Intrinsics_vec128_xor(next16[0U], key310);
  Lib_IntVector_Intrinsics_vec128 *prev06 = next06;
  Lib_IntVector_Intrinsics_vec128 *prev16 = next16;
  Lib_IntVector_Intrinsics_vec128 *next07 = kex0 + klen * (uint32_t)14U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev16[0U], (uint8_t)0x40U);
  next07[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key41 = prev06[0U];
  Lib_IntVector_Intrinsics_vec128
  key113 =
    Lib_IntVector_Intrinsics_vec128_xor(key41,
      Lib_IntVector_Intrinsics_vec128_shift_left(key41, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key212 =
    Lib_IntVector_Intrinsics_vec128_xor(key113,
      Lib_IntVector_Intrinsics_vec128_shift_left(key113, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key311 =
    Lib_IntVector_Intrinsics_vec128_xor(key212,
      Lib_IntVector_Intrinsics_vec128_shift_left(key212, (uint32_t)32U));
  next07[0U] = Lib_IntVector_Intrinsics_vec128_xor(next07[0U], key311);
  uint8_t nb[16U] = { 0U };
  memcpy(nb, n, (uint32_t)12U * sizeof (uint8_t));
  n10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = c + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)13U; i0++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i0 * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(ib);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)48U, v31);
  }
  uint32_t rem = len % (uint32_t)64U;
  uint8_t last[64U];
  if (rem > (uint32_t)0U)
  {
    uint32_t ctr = c + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    uint8_t init = (uint8_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      last[i] = init;
    }
    memcpy(last, ib, rem * sizeof (uint8_t));
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)13U; i++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)48U, v31);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_ctr_encrypt */

/* SNIPPET_START: Hacl_AES_256_NI_aes256_ctr_decrypt */

inline void
Hacl_AES_256_NI_aes256_ctr_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint8_t *k,
  uint8_t *n,
  uint32_t c
)
{
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
    (uint32_t)1U + (uint32_t)15U * (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec128 ctx[(uint32_t)1U + (uint32_t)15U * (uint32_t)1U];
  for (uint32_t _i = 0U; _i < (uint32_t)1U + (uint32_t)15U * (uint32_t)1U; ++_i)
    ctx[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  Lib_IntVector_Intrinsics_vec128 *kex0 = ctx + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *n10 = ctx;
  uint32_t klen = (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *next0 = kex0;
  Lib_IntVector_Intrinsics_vec128 *next1 = kex0 + klen;
  next0[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k);
  next1[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(k + (uint32_t)16U);
  Lib_IntVector_Intrinsics_vec128 *prev0 = next0;
  Lib_IntVector_Intrinsics_vec128 *prev1 = next1;
  Lib_IntVector_Intrinsics_vec128 *next01 = kex0 + klen * (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *next11 = kex0 + klen * (uint32_t)3U;
  Lib_IntVector_Intrinsics_vec128
  v0 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev1[0U], (uint8_t)0x01U);
  next01[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key = prev0[0U];
  Lib_IntVector_Intrinsics_vec128
  key1 =
    Lib_IntVector_Intrinsics_vec128_xor(key,
      Lib_IntVector_Intrinsics_vec128_shift_left(key, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key2 =
    Lib_IntVector_Intrinsics_vec128_xor(key1,
      Lib_IntVector_Intrinsics_vec128_shift_left(key1, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key3 =
    Lib_IntVector_Intrinsics_vec128_xor(key2,
      Lib_IntVector_Intrinsics_vec128_shift_left(key2, (uint32_t)32U));
  next01[0U] = Lib_IntVector_Intrinsics_vec128_xor(next01[0U], key3);
  Lib_IntVector_Intrinsics_vec128
  v4 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next01[0U], (uint8_t)0U);
  next11[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v4,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key0 = prev1[0U];
  Lib_IntVector_Intrinsics_vec128
  key10 =
    Lib_IntVector_Intrinsics_vec128_xor(key0,
      Lib_IntVector_Intrinsics_vec128_shift_left(key0, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key20 =
    Lib_IntVector_Intrinsics_vec128_xor(key10,
      Lib_IntVector_Intrinsics_vec128_shift_left(key10, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key30 =
    Lib_IntVector_Intrinsics_vec128_xor(key20,
      Lib_IntVector_Intrinsics_vec128_shift_left(key20, (uint32_t)32U));
  next11[0U] = Lib_IntVector_Intrinsics_vec128_xor(next11[0U], key30);
  Lib_IntVector_Intrinsics_vec128 *prev01 = next01;
  Lib_IntVector_Intrinsics_vec128 *prev11 = next11;
  Lib_IntVector_Intrinsics_vec128 *next02 = kex0 + klen * (uint32_t)4U;
  Lib_IntVector_Intrinsics_vec128 *next12 = kex0 + klen * (uint32_t)5U;
  Lib_IntVector_Intrinsics_vec128
  v5 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev11[0U], (uint8_t)0x02U);
  next02[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v5,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key4 = prev01[0U];
  Lib_IntVector_Intrinsics_vec128
  key11 =
    Lib_IntVector_Intrinsics_vec128_xor(key4,
      Lib_IntVector_Intrinsics_vec128_shift_left(key4, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key21 =
    Lib_IntVector_Intrinsics_vec128_xor(key11,
      Lib_IntVector_Intrinsics_vec128_shift_left(key11, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key31 =
    Lib_IntVector_Intrinsics_vec128_xor(key21,
      Lib_IntVector_Intrinsics_vec128_shift_left(key21, (uint32_t)32U));
  next02[0U] = Lib_IntVector_Intrinsics_vec128_xor(next02[0U], key31);
  Lib_IntVector_Intrinsics_vec128
  v6 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next02[0U], (uint8_t)0U);
  next12[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v6,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key5 = prev11[0U];
  Lib_IntVector_Intrinsics_vec128
  key12 =
    Lib_IntVector_Intrinsics_vec128_xor(key5,
      Lib_IntVector_Intrinsics_vec128_shift_left(key5, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key22 =
    Lib_IntVector_Intrinsics_vec128_xor(key12,
      Lib_IntVector_Intrinsics_vec128_shift_left(key12, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key32 =
    Lib_IntVector_Intrinsics_vec128_xor(key22,
      Lib_IntVector_Intrinsics_vec128_shift_left(key22, (uint32_t)32U));
  next12[0U] = Lib_IntVector_Intrinsics_vec128_xor(next12[0U], key32);
  Lib_IntVector_Intrinsics_vec128 *prev02 = next02;
  Lib_IntVector_Intrinsics_vec128 *prev12 = next12;
  Lib_IntVector_Intrinsics_vec128 *next03 = kex0 + klen * (uint32_t)6U;
  Lib_IntVector_Intrinsics_vec128 *next13 = kex0 + klen * (uint32_t)7U;
  Lib_IntVector_Intrinsics_vec128
  v7 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev12[0U], (uint8_t)0x04U);
  next03[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v7,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key6 = prev02[0U];
  Lib_IntVector_Intrinsics_vec128
  key13 =
    Lib_IntVector_Intrinsics_vec128_xor(key6,
      Lib_IntVector_Intrinsics_vec128_shift_left(key6, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key23 =
    Lib_IntVector_Intrinsics_vec128_xor(key13,
      Lib_IntVector_Intrinsics_vec128_shift_left(key13, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key33 =
    Lib_IntVector_Intrinsics_vec128_xor(key23,
      Lib_IntVector_Intrinsics_vec128_shift_left(key23, (uint32_t)32U));
  next03[0U] = Lib_IntVector_Intrinsics_vec128_xor(next03[0U], key33);
  Lib_IntVector_Intrinsics_vec128
  v8 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next03[0U], (uint8_t)0U);
  next13[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v8,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key7 = prev12[0U];
  Lib_IntVector_Intrinsics_vec128
  key14 =
    Lib_IntVector_Intrinsics_vec128_xor(key7,
      Lib_IntVector_Intrinsics_vec128_shift_left(key7, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key24 =
    Lib_IntVector_Intrinsics_vec128_xor(key14,
      Lib_IntVector_Intrinsics_vec128_shift_left(key14, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key34 =
    Lib_IntVector_Intrinsics_vec128_xor(key24,
      Lib_IntVector_Intrinsics_vec128_shift_left(key24, (uint32_t)32U));
  next13[0U] = Lib_IntVector_Intrinsics_vec128_xor(next13[0U], key34);
  Lib_IntVector_Intrinsics_vec128 *prev03 = next03;
  Lib_IntVector_Intrinsics_vec128 *prev13 = next13;
  Lib_IntVector_Intrinsics_vec128 *next04 = kex0 + klen * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec128 *next14 = kex0 + klen * (uint32_t)9U;
  Lib_IntVector_Intrinsics_vec128
  v9 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev13[0U], (uint8_t)0x08U);
  next04[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v9,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key8 = prev03[0U];
  Lib_IntVector_Intrinsics_vec128
  key15 =
    Lib_IntVector_Intrinsics_vec128_xor(key8,
      Lib_IntVector_Intrinsics_vec128_shift_left(key8, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key25 =
    Lib_IntVector_Intrinsics_vec128_xor(key15,
      Lib_IntVector_Intrinsics_vec128_shift_left(key15, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key35 =
    Lib_IntVector_Intrinsics_vec128_xor(key25,
      Lib_IntVector_Intrinsics_vec128_shift_left(key25, (uint32_t)32U));
  next04[0U] = Lib_IntVector_Intrinsics_vec128_xor(next04[0U], key35);
  Lib_IntVector_Intrinsics_vec128
  v10 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next04[0U], (uint8_t)0U);
  next14[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v10,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key9 = prev13[0U];
  Lib_IntVector_Intrinsics_vec128
  key16 =
    Lib_IntVector_Intrinsics_vec128_xor(key9,
      Lib_IntVector_Intrinsics_vec128_shift_left(key9, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key26 =
    Lib_IntVector_Intrinsics_vec128_xor(key16,
      Lib_IntVector_Intrinsics_vec128_shift_left(key16, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key36 =
    Lib_IntVector_Intrinsics_vec128_xor(key26,
      Lib_IntVector_Intrinsics_vec128_shift_left(key26, (uint32_t)32U));
  next14[0U] = Lib_IntVector_Intrinsics_vec128_xor(next14[0U], key36);
  Lib_IntVector_Intrinsics_vec128 *prev04 = next04;
  Lib_IntVector_Intrinsics_vec128 *prev14 = next14;
  Lib_IntVector_Intrinsics_vec128 *next05 = kex0 + klen * (uint32_t)10U;
  Lib_IntVector_Intrinsics_vec128 *next15 = kex0 + klen * (uint32_t)11U;
  Lib_IntVector_Intrinsics_vec128
  v12 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev14[0U], (uint8_t)0x10U);
  next05[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v12,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key17 = prev04[0U];
  Lib_IntVector_Intrinsics_vec128
  key18 =
    Lib_IntVector_Intrinsics_vec128_xor(key17,
      Lib_IntVector_Intrinsics_vec128_shift_left(key17, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key27 =
    Lib_IntVector_Intrinsics_vec128_xor(key18,
      Lib_IntVector_Intrinsics_vec128_shift_left(key18, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key37 =
    Lib_IntVector_Intrinsics_vec128_xor(key27,
      Lib_IntVector_Intrinsics_vec128_shift_left(key27, (uint32_t)32U));
  next05[0U] = Lib_IntVector_Intrinsics_vec128_xor(next05[0U], key37);
  Lib_IntVector_Intrinsics_vec128
  v13 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next05[0U], (uint8_t)0U);
  next15[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v13,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key19 = prev14[0U];
  Lib_IntVector_Intrinsics_vec128
  key110 =
    Lib_IntVector_Intrinsics_vec128_xor(key19,
      Lib_IntVector_Intrinsics_vec128_shift_left(key19, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key28 =
    Lib_IntVector_Intrinsics_vec128_xor(key110,
      Lib_IntVector_Intrinsics_vec128_shift_left(key110, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key38 =
    Lib_IntVector_Intrinsics_vec128_xor(key28,
      Lib_IntVector_Intrinsics_vec128_shift_left(key28, (uint32_t)32U));
  next15[0U] = Lib_IntVector_Intrinsics_vec128_xor(next15[0U], key38);
  Lib_IntVector_Intrinsics_vec128 *prev05 = next05;
  Lib_IntVector_Intrinsics_vec128 *prev15 = next15;
  Lib_IntVector_Intrinsics_vec128 *next06 = kex0 + klen * (uint32_t)12U;
  Lib_IntVector_Intrinsics_vec128 *next16 = kex0 + klen * (uint32_t)13U;
  Lib_IntVector_Intrinsics_vec128
  v14 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev15[0U], (uint8_t)0x20U);
  next06[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v14,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key29 = prev05[0U];
  Lib_IntVector_Intrinsics_vec128
  key111 =
    Lib_IntVector_Intrinsics_vec128_xor(key29,
      Lib_IntVector_Intrinsics_vec128_shift_left(key29, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key210 =
    Lib_IntVector_Intrinsics_vec128_xor(key111,
      Lib_IntVector_Intrinsics_vec128_shift_left(key111, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key39 =
    Lib_IntVector_Intrinsics_vec128_xor(key210,
      Lib_IntVector_Intrinsics_vec128_shift_left(key210, (uint32_t)32U));
  next06[0U] = Lib_IntVector_Intrinsics_vec128_xor(next06[0U], key39);
  Lib_IntVector_Intrinsics_vec128
  v15 = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(next06[0U], (uint8_t)0U);
  next16[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v15,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U,
      (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128 key40 = prev15[0U];
  Lib_IntVector_Intrinsics_vec128
  key112 =
    Lib_IntVector_Intrinsics_vec128_xor(key40,
      Lib_IntVector_Intrinsics_vec128_shift_left(key40, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key211 =
    Lib_IntVector_Intrinsics_vec128_xor(key112,
      Lib_IntVector_Intrinsics_vec128_shift_left(key112, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key310 =
    Lib_IntVector_Intrinsics_vec128_xor(key211,
      Lib_IntVector_Intrinsics_vec128_shift_left(key211, (uint32_t)32U));
  next16[0U] = Lib_IntVector_Intrinsics_vec128_xor(next16[0U], key310);
  Lib_IntVector_Intrinsics_vec128 *prev06 = next06;
  Lib_IntVector_Intrinsics_vec128 *prev16 = next16;
  Lib_IntVector_Intrinsics_vec128 *next07 = kex0 + klen * (uint32_t)14U;
  Lib_IntVector_Intrinsics_vec128
  v = Lib_IntVector_Intrinsics_ni_aes_keygen_assist(prev16[0U], (uint8_t)0x40U);
  next07[0U] =
    Lib_IntVector_Intrinsics_vec128_shuffle32(v,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U,
      (uint32_t)3U);
  Lib_IntVector_Intrinsics_vec128 key41 = prev06[0U];
  Lib_IntVector_Intrinsics_vec128
  key113 =
    Lib_IntVector_Intrinsics_vec128_xor(key41,
      Lib_IntVector_Intrinsics_vec128_shift_left(key41, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key212 =
    Lib_IntVector_Intrinsics_vec128_xor(key113,
      Lib_IntVector_Intrinsics_vec128_shift_left(key113, (uint32_t)32U));
  Lib_IntVector_Intrinsics_vec128
  key311 =
    Lib_IntVector_Intrinsics_vec128_xor(key212,
      Lib_IntVector_Intrinsics_vec128_shift_left(key212, (uint32_t)32U));
  next07[0U] = Lib_IntVector_Intrinsics_vec128_xor(next07[0U], key311);
  uint8_t nb[16U] = { 0U };
  memcpy(nb, n, (uint32_t)12U * sizeof (uint8_t));
  n10[0U] = Lib_IntVector_Intrinsics_vec128_load128_le(nb);
  uint32_t blocks64 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks64; i++)
  {
    uint32_t ctr = c + i * (uint32_t)4U;
    uint8_t *ib = inp + i * (uint32_t)64U;
    uint8_t *ob = out + i * (uint32_t)64U;
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)13U; i0++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i0 * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(ib);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(ib + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(ob + (uint32_t)48U, v31);
  }
  uint32_t rem = len % (uint32_t)64U;
  uint8_t last[64U];
  if (rem > (uint32_t)0U)
  {
    uint32_t ctr = c + blocks64 * (uint32_t)4U;
    uint8_t *ib = inp + blocks64 * (uint32_t)64U;
    uint8_t *ob = out + blocks64 * (uint32_t)64U;
    uint8_t init = (uint8_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      last[i] = init;
    }
    memcpy(last, ib, rem * sizeof (uint8_t));
    Lib_IntVector_Intrinsics_vec128 st[4U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    Lib_IntVector_Intrinsics_vec128 *kex = ctx + (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *n1 = ctx;
    uint32_t counter = ctr;
    uint32_t counter0 = htobe32(counter);
    uint32_t counter1 = htobe32(counter + (uint32_t)1U);
    uint32_t counter2 = htobe32(counter + (uint32_t)2U);
    uint32_t counter3 = htobe32(counter + (uint32_t)3U);
    Lib_IntVector_Intrinsics_vec128 nonce0 = n1[0U];
    st[0U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter0, (uint32_t)3U);
    st[1U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter1, (uint32_t)3U);
    st[2U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter2, (uint32_t)3U);
    st[3U] = Lib_IntVector_Intrinsics_vec128_insert32(nonce0, counter3, (uint32_t)3U);
    uint32_t klen0 = (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec128 *k0 = kex;
    Lib_IntVector_Intrinsics_vec128 *kr = kex + klen0;
    Lib_IntVector_Intrinsics_vec128 *kn = kex + (uint32_t)14U * klen0;
    st[0U] = Lib_IntVector_Intrinsics_vec128_xor(st[0U], k0[0U]);
    st[1U] = Lib_IntVector_Intrinsics_vec128_xor(st[1U], k0[0U]);
    st[2U] = Lib_IntVector_Intrinsics_vec128_xor(st[2U], k0[0U]);
    st[3U] = Lib_IntVector_Intrinsics_vec128_xor(st[3U], k0[0U]);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)13U; i++)
    {
      Lib_IntVector_Intrinsics_vec128 *sub_key = kr + i * (uint32_t)1U;
      st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[0U], sub_key[0U]);
      st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[1U], sub_key[0U]);
      st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[2U], sub_key[0U]);
      st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc(st[3U], sub_key[0U]);
    }
    st[0U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[0U], kn[0U]);
    st[1U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[1U], kn[0U]);
    st[2U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[2U], kn[0U]);
    st[3U] = Lib_IntVector_Intrinsics_ni_aes_enc_last(st[3U], kn[0U]);
    Lib_IntVector_Intrinsics_vec128 v00 = Lib_IntVector_Intrinsics_vec128_load128_le(last);
    Lib_IntVector_Intrinsics_vec128
    v1 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)16U);
    Lib_IntVector_Intrinsics_vec128
    v2 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)32U);
    Lib_IntVector_Intrinsics_vec128
    v3 = Lib_IntVector_Intrinsics_vec128_load128_le(last + (uint32_t)48U);
    Lib_IntVector_Intrinsics_vec128 v01 = Lib_IntVector_Intrinsics_vec128_xor(v00, st[0U]);
    Lib_IntVector_Intrinsics_vec128 v11 = Lib_IntVector_Intrinsics_vec128_xor(v1, st[1U]);
    Lib_IntVector_Intrinsics_vec128 v21 = Lib_IntVector_Intrinsics_vec128_xor(v2, st[2U]);
    Lib_IntVector_Intrinsics_vec128 v31 = Lib_IntVector_Intrinsics_vec128_xor(v3, st[3U]);
    Lib_IntVector_Intrinsics_vec128_store128_le(last, v01);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)16U, v11);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)32U, v21);
    Lib_IntVector_Intrinsics_vec128_store128_le(last + (uint32_t)48U, v31);
    memcpy(ob, last, rem * sizeof (uint8_t));
  }
}

/* SNIPPET_END: Hacl_AES_256_NI_aes256_ctr_decrypt */

