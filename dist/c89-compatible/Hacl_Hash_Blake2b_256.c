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


#include "Hacl_Hash_Blake2b_256.h"

static FStar_UInt128_uint128
update_blake2b_256(
  Lib_IntVector_Intrinsics_vec256 *s,
  FStar_UInt128_uint128 totlen,
  uint8_t *block
)
{
  Lib_IntVector_Intrinsics_vec256 wv[4U];
  {
    uint32_t _i;
    for (_i = 0U; _i < (uint32_t)4U; ++_i)
      wv[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  }
  {
    FStar_UInt128_uint128
    totlen1 =
      FStar_UInt128_add_mod(totlen,
        FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U));
    uint64_t m_w[16U] = { 0U };
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint64_t *os = m_w;
        uint8_t *bj = block + i * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[i] = x;
      }
    }
    {
      Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
      uint64_t wv_14 = (uint64_t)0U;
      uint64_t wv_15 = (uint64_t)0U;
      Lib_IntVector_Intrinsics_vec256 *wv3;
      Lib_IntVector_Intrinsics_vec256 *s00;
      Lib_IntVector_Intrinsics_vec256 *s16;
      Lib_IntVector_Intrinsics_vec256 *r00;
      Lib_IntVector_Intrinsics_vec256 *r10;
      Lib_IntVector_Intrinsics_vec256 *r20;
      Lib_IntVector_Intrinsics_vec256 *r30;
      mask =
        Lib_IntVector_Intrinsics_vec256_load64s(FStar_UInt128_uint128_to_uint64(totlen1),
          FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(totlen1, (uint32_t)64U)),
          wv_14,
          wv_15);
      memcpy(wv, s, (uint32_t)4U * (uint32_t)1U * sizeof (Lib_IntVector_Intrinsics_vec256));
      wv3 = wv + (uint32_t)3U * (uint32_t)1U;
      wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < (uint32_t)12U; i++)
        {
          uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
          KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
          {
            Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
            {
              uint32_t _i;
              for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
            }
            {
              Lib_IntVector_Intrinsics_vec256 *r0 = m_st + (uint32_t)0U * (uint32_t)1U;
              Lib_IntVector_Intrinsics_vec256 *r1 = m_st + (uint32_t)1U * (uint32_t)1U;
              Lib_IntVector_Intrinsics_vec256 *r21 = m_st + (uint32_t)2U * (uint32_t)1U;
              Lib_IntVector_Intrinsics_vec256 *r31 = m_st + (uint32_t)3U * (uint32_t)1U;
              uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
              uint32_t s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
              uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
              uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
              uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
              uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
              uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
              uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
              uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
              uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
              uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
              uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
              uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
              uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
              uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
              uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
              r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
              r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s1], m_w[s3], m_w[s5], m_w[s7]);
              r21[0U] =
                Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8],
                  m_w[s10],
                  m_w[s12],
                  m_w[s14]);
              r31[0U] =
                Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9],
                  m_w[s11],
                  m_w[s13],
                  m_w[s15]);
              {
                Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                uint32_t a = (uint32_t)0U;
                uint32_t b0 = (uint32_t)1U;
                uint32_t c0 = (uint32_t)2U;
                uint32_t d0 = (uint32_t)3U;
                Lib_IntVector_Intrinsics_vec256 *wv_a0 = wv + a * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec256 *wv_b0 = wv + b0 * (uint32_t)1U;
                wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
                wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
                {
                  Lib_IntVector_Intrinsics_vec256 *wv_a1 = wv + d0 * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec256 *wv_b1 = wv + a * (uint32_t)1U;
                  wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
                  wv_a1[0U] =
                    Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U],
                      (uint32_t)32U);
                  {
                    Lib_IntVector_Intrinsics_vec256 *wv_a2 = wv + c0 * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec256 *wv_b2 = wv + d0 * (uint32_t)1U;
                    wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
                    {
                      Lib_IntVector_Intrinsics_vec256 *wv_a3 = wv + b0 * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec256 *wv_b3 = wv + c0 * (uint32_t)1U;
                      wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
                      wv_a3[0U] =
                        Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U],
                          (uint32_t)24U);
                      {
                        Lib_IntVector_Intrinsics_vec256 *wv_a4 = wv + a * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec256 *wv_b4 = wv + b0 * (uint32_t)1U;
                        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
                        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
                        {
                          Lib_IntVector_Intrinsics_vec256 *wv_a5 = wv + d0 * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec256 *wv_b5 = wv + a * (uint32_t)1U;
                          wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
                          wv_a5[0U] =
                            Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U],
                              (uint32_t)16U);
                          {
                            Lib_IntVector_Intrinsics_vec256 *wv_a6 = wv + c0 * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec256 *wv_b6 = wv + d0 * (uint32_t)1U;
                            wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
                            {
                              Lib_IntVector_Intrinsics_vec256 *wv_a7 = wv + b0 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec256 *wv_b7 = wv + c0 * (uint32_t)1U;
                              wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
                              wv_a7[0U] =
                                Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U],
                                  (uint32_t)63U);
                              {
                                Lib_IntVector_Intrinsics_vec256
                                *r11 = wv + (uint32_t)1U * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec256
                                *r22 = wv + (uint32_t)2U * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec256
                                *r32 = wv + (uint32_t)3U * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec256 v00 = r11[0U];
                                Lib_IntVector_Intrinsics_vec256
                                v1 =
                                  Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00,
                                    (uint32_t)1U);
                                r11[0U] = v1;
                                {
                                  Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
                                  Lib_IntVector_Intrinsics_vec256
                                  v10 =
                                    Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01,
                                      (uint32_t)2U);
                                  r22[0U] = v10;
                                  {
                                    Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
                                    Lib_IntVector_Intrinsics_vec256
                                    v11 =
                                      Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02,
                                        (uint32_t)3U);
                                    r32[0U] = v11;
                                    {
                                      uint32_t a0 = (uint32_t)0U;
                                      uint32_t b = (uint32_t)1U;
                                      uint32_t c = (uint32_t)2U;
                                      uint32_t d = (uint32_t)3U;
                                      Lib_IntVector_Intrinsics_vec256
                                      *wv_a = wv + a0 * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec256
                                      *wv_b8 = wv + b * (uint32_t)1U;
                                      wv_a[0U] =
                                        Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U],
                                          wv_b8[0U]);
                                      wv_a[0U] =
                                        Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U],
                                          z[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec256
                                        *wv_a8 = wv + d * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec256
                                        *wv_b9 = wv + a0 * (uint32_t)1U;
                                        wv_a8[0U] =
                                          Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U],
                                            wv_b9[0U]);
                                        wv_a8[0U] =
                                          Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U],
                                            (uint32_t)32U);
                                        {
                                          Lib_IntVector_Intrinsics_vec256
                                          *wv_a9 = wv + c * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec256
                                          *wv_b10 = wv + d * (uint32_t)1U;
                                          wv_a9[0U] =
                                            Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U],
                                              wv_b10[0U]);
                                          {
                                            Lib_IntVector_Intrinsics_vec256
                                            *wv_a10 = wv + b * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec256
                                            *wv_b11 = wv + c * (uint32_t)1U;
                                            wv_a10[0U] =
                                              Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U],
                                                wv_b11[0U]);
                                            wv_a10[0U] =
                                              Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U],
                                                (uint32_t)24U);
                                            {
                                              Lib_IntVector_Intrinsics_vec256
                                              *wv_a11 = wv + a0 * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec256
                                              *wv_b12 = wv + b * (uint32_t)1U;
                                              wv_a11[0U] =
                                                Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U],
                                                  wv_b12[0U]);
                                              wv_a11[0U] =
                                                Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U],
                                                  w[0U]);
                                              {
                                                Lib_IntVector_Intrinsics_vec256
                                                *wv_a12 = wv + d * (uint32_t)1U;
                                                Lib_IntVector_Intrinsics_vec256
                                                *wv_b13 = wv + a0 * (uint32_t)1U;
                                                wv_a12[0U] =
                                                  Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U],
                                                    wv_b13[0U]);
                                                wv_a12[0U] =
                                                  Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U],
                                                    (uint32_t)16U);
                                                {
                                                  Lib_IntVector_Intrinsics_vec256
                                                  *wv_a13 = wv + c * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec256
                                                  *wv_b14 = wv + d * (uint32_t)1U;
                                                  wv_a13[0U] =
                                                    Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U],
                                                      wv_b14[0U]);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec256
                                                    *wv_a14 = wv + b * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec256
                                                    *wv_b = wv + c * (uint32_t)1U;
                                                    wv_a14[0U] =
                                                      Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U],
                                                        wv_b[0U]);
                                                    wv_a14[0U] =
                                                      Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U],
                                                        (uint32_t)63U);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *r12 = wv + (uint32_t)1U * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *r2 = wv + (uint32_t)2U * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *r3 = wv + (uint32_t)3U * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec256 v0 = r12[0U];
                                                      Lib_IntVector_Intrinsics_vec256
                                                      v12 =
                                                        Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0,
                                                          (uint32_t)3U);
                                                      r12[0U] = v12;
                                                      {
                                                        Lib_IntVector_Intrinsics_vec256
                                                        v03 = r2[0U];
                                                        Lib_IntVector_Intrinsics_vec256
                                                        v13 =
                                                          Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03,
                                                            (uint32_t)2U);
                                                        r2[0U] = v13;
                                                        {
                                                          Lib_IntVector_Intrinsics_vec256
                                                          v04 = r3[0U];
                                                          Lib_IntVector_Intrinsics_vec256
                                                          v14 =
                                                            Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04,
                                                              (uint32_t)1U);
                                                          r3[0U] = v14;
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      s00 = s + (uint32_t)0U * (uint32_t)1U;
      s16 = s + (uint32_t)1U * (uint32_t)1U;
      r00 = wv + (uint32_t)0U * (uint32_t)1U;
      r10 = wv + (uint32_t)1U * (uint32_t)1U;
      r20 = wv + (uint32_t)2U * (uint32_t)1U;
      r30 = wv + (uint32_t)3U * (uint32_t)1U;
      s00[0U] = Lib_IntVector_Intrinsics_vec256_xor(s00[0U], r00[0U]);
      s00[0U] = Lib_IntVector_Intrinsics_vec256_xor(s00[0U], r20[0U]);
      s16[0U] = Lib_IntVector_Intrinsics_vec256_xor(s16[0U], r10[0U]);
      s16[0U] = Lib_IntVector_Intrinsics_vec256_xor(s16[0U], r30[0U]);
      return totlen1;
    }
  }
}

void
Hacl_Hash_Blake2b_256_finish_blake2b_256(
  Lib_IntVector_Intrinsics_vec256 *s,
  FStar_UInt128_uint128 ev,
  uint8_t *dst
)
{
  uint32_t double_row = (uint32_t)2U * ((uint32_t)4U * (uint32_t)8U);
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  {
    uint8_t b[double_row];
    memset(b, 0U, double_row * sizeof (uint8_t));
    {
      uint8_t *first = b;
      uint8_t *second = b + (uint32_t)4U * (uint32_t)8U;
      Lib_IntVector_Intrinsics_vec256 *row0 = s + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *row1 = s + (uint32_t)1U * (uint32_t)1U;
      uint8_t *final;
      Lib_IntVector_Intrinsics_vec256_store64_le(first, row0[0U]);
      Lib_IntVector_Intrinsics_vec256_store64_le(second, row1[0U]);
      final = b;
      memcpy(dst, final, (uint32_t)64U * sizeof (uint8_t));
      Lib_Memzero0_memzero(b, double_row * sizeof (b[0U]));
    }
  }
}

FStar_UInt128_uint128
Hacl_Hash_Blake2b_256_update_multi_blake2b_256(
  Lib_IntVector_Intrinsics_vec256 *s,
  FStar_UInt128_uint128 ev,
  uint8_t *blocks,
  uint32_t n_blocks
)
{
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < n_blocks; i++)
    {
      uint32_t sz = (uint32_t)128U;
      uint8_t *block = blocks + sz * i;
      FStar_UInt128_uint128
      v_ =
        update_blake2b_256(s,
          FStar_UInt128_add_mod(ev,
            FStar_UInt128_uint64_to_uint128((uint64_t)i * (uint64_t)(uint32_t)128U)),
          block);
    }
  }
  return
    FStar_UInt128_add_mod(ev,
      FStar_UInt128_uint64_to_uint128((uint64_t)n_blocks * (uint64_t)(uint32_t)128U));
}

FStar_UInt128_uint128
Hacl_Hash_Blake2b_256_update_last_blake2b_256(
  Lib_IntVector_Intrinsics_vec256 *s,
  FStar_UInt128_uint128 ev,
  FStar_UInt128_uint128 prev_len,
  uint8_t *input,
  uint32_t input_len
)
{
  uint32_t blocks_n = input_len / (uint32_t)128U;
  uint32_t blocks_len0 = blocks_n * (uint32_t)128U;
  uint32_t rest_len0 = input_len - blocks_len0;
  K___uint32_t_uint32_t_uint32_t scrut0;
  if (rest_len0 == (uint32_t)0U && blocks_n > (uint32_t)0U)
  {
    uint32_t blocks_n1 = blocks_n - (uint32_t)1U;
    uint32_t blocks_len1 = blocks_len0 - (uint32_t)128U;
    uint32_t rest_len1 = (uint32_t)128U;
    K___uint32_t_uint32_t_uint32_t lit;
    lit.fst = blocks_n1;
    lit.snd = blocks_len1;
    lit.thd = rest_len1;
    scrut0 = lit;
  }
  else
  {
    K___uint32_t_uint32_t_uint32_t lit;
    lit.fst = blocks_n;
    lit.snd = blocks_len0;
    lit.thd = rest_len0;
    scrut0 = lit;
  }
  {
    uint32_t num_blocks0 = scrut0.fst;
    uint32_t blocks_len = scrut0.snd;
    uint32_t rest_len1 = scrut0.thd;
    uint8_t *blocks0 = input;
    uint8_t *rest0 = input + blocks_len;
    K___uint32_t_uint32_t_uint32_t__uint8_t___uint8_t_ lit;
    K___uint32_t_uint32_t_uint32_t__uint8_t___uint8_t_ scrut;
    uint32_t num_blocks;
    uint32_t rest_len;
    uint8_t *blocks;
    uint8_t *rest;
    FStar_UInt128_uint128 ev_;
    lit.fst = num_blocks0;
    lit.snd = blocks_len;
    lit.thd = rest_len1;
    lit.f3 = blocks0;
    lit.f4 = rest0;
    scrut = lit;
    num_blocks = scrut.fst;
    rest_len = scrut.thd;
    blocks = scrut.f3;
    rest = scrut.f4;
    ev_ = Hacl_Hash_Blake2b_256_update_multi_blake2b_256(s, ev, blocks, num_blocks);
    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
    {
      Lib_IntVector_Intrinsics_vec256 wv[(uint32_t)4U * (uint32_t)1U];
      {
        uint32_t _i;
        for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
          wv[_i] = Lib_IntVector_Intrinsics_vec256_zero;
      }
      {
        uint8_t tmp[128U] = { 0U };
        uint8_t *tmp_rest = tmp;
        FStar_UInt128_uint128 totlen;
        memcpy(tmp_rest, rest, rest_len * sizeof (uint8_t));
        totlen = FStar_UInt128_add_mod(ev_, FStar_UInt128_uint64_to_uint128((uint64_t)rest_len));
        {
          uint64_t m_w[16U] = { 0U };
          {
            uint32_t i;
            for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
            {
              uint64_t *os = m_w;
              uint8_t *bj = tmp + i * (uint32_t)8U;
              uint64_t u = load64_le(bj);
              uint64_t r = u;
              uint64_t x = r;
              os[i] = x;
            }
          }
          {
            Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
            uint64_t wv_14 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
            uint64_t wv_15 = (uint64_t)0U;
            Lib_IntVector_Intrinsics_vec256 *wv3;
            Lib_IntVector_Intrinsics_vec256 *s00;
            Lib_IntVector_Intrinsics_vec256 *s16;
            Lib_IntVector_Intrinsics_vec256 *r00;
            Lib_IntVector_Intrinsics_vec256 *r10;
            Lib_IntVector_Intrinsics_vec256 *r20;
            Lib_IntVector_Intrinsics_vec256 *r30;
            mask =
              Lib_IntVector_Intrinsics_vec256_load64s(FStar_UInt128_uint128_to_uint64(totlen),
                FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(totlen, (uint32_t)64U)),
                wv_14,
                wv_15);
            memcpy(wv, s, (uint32_t)4U * (uint32_t)1U * sizeof (Lib_IntVector_Intrinsics_vec256));
            wv3 = wv + (uint32_t)3U * (uint32_t)1U;
            wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < (uint32_t)12U; i++)
              {
                uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256),
                  (uint32_t)4U * (uint32_t)1U);
                {
                  Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
                  {
                    uint32_t _i;
                    for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                      m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
                  }
                  {
                    Lib_IntVector_Intrinsics_vec256 *r0 = m_st + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec256 *r1 = m_st + (uint32_t)1U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec256 *r21 = m_st + (uint32_t)2U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec256 *r31 = m_st + (uint32_t)3U * (uint32_t)1U;
                    uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                    uint32_t s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                    uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                    uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                    uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                    uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                    uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                    uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                    uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                    uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                    uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                    uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                    uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                    uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                    uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                    uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                    r0[0U] =
                      Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0],
                        m_w[s2],
                        m_w[s4],
                        m_w[s6]);
                    r1[0U] =
                      Lib_IntVector_Intrinsics_vec256_load64s(m_w[s1],
                        m_w[s3],
                        m_w[s5],
                        m_w[s7]);
                    r21[0U] =
                      Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8],
                        m_w[s10],
                        m_w[s12],
                        m_w[s14]);
                    r31[0U] =
                      Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9],
                        m_w[s11],
                        m_w[s13],
                        m_w[s15]);
                    {
                      Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                      uint32_t a = (uint32_t)0U;
                      uint32_t b0 = (uint32_t)1U;
                      uint32_t c0 = (uint32_t)2U;
                      uint32_t d0 = (uint32_t)3U;
                      Lib_IntVector_Intrinsics_vec256 *wv_a0 = wv + a * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec256 *wv_b0 = wv + b0 * (uint32_t)1U;
                      wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
                      wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
                      {
                        Lib_IntVector_Intrinsics_vec256 *wv_a1 = wv + d0 * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec256 *wv_b1 = wv + a * (uint32_t)1U;
                        wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
                        wv_a1[0U] =
                          Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U],
                            (uint32_t)32U);
                        {
                          Lib_IntVector_Intrinsics_vec256 *wv_a2 = wv + c0 * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec256 *wv_b2 = wv + d0 * (uint32_t)1U;
                          wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
                          {
                            Lib_IntVector_Intrinsics_vec256 *wv_a3 = wv + b0 * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec256 *wv_b3 = wv + c0 * (uint32_t)1U;
                            wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
                            wv_a3[0U] =
                              Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U],
                                (uint32_t)24U);
                            {
                              Lib_IntVector_Intrinsics_vec256 *wv_a4 = wv + a * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec256 *wv_b4 = wv + b0 * (uint32_t)1U;
                              wv_a4[0U] =
                                Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U],
                                  wv_b4[0U]);
                              wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
                              {
                                Lib_IntVector_Intrinsics_vec256 *wv_a5 = wv + d0 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec256 *wv_b5 = wv + a * (uint32_t)1U;
                                wv_a5[0U] =
                                  Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U],
                                    wv_b5[0U]);
                                wv_a5[0U] =
                                  Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U],
                                    (uint32_t)16U);
                                {
                                  Lib_IntVector_Intrinsics_vec256 *wv_a6 = wv + c0 * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec256 *wv_b6 = wv + d0 * (uint32_t)1U;
                                  wv_a6[0U] =
                                    Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U],
                                      wv_b6[0U]);
                                  {
                                    Lib_IntVector_Intrinsics_vec256 *wv_a7 = wv + b0 * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec256 *wv_b7 = wv + c0 * (uint32_t)1U;
                                    wv_a7[0U] =
                                      Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U],
                                        wv_b7[0U]);
                                    wv_a7[0U] =
                                      Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U],
                                        (uint32_t)63U);
                                    {
                                      Lib_IntVector_Intrinsics_vec256
                                      *r11 = wv + (uint32_t)1U * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec256
                                      *r22 = wv + (uint32_t)2U * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec256
                                      *r32 = wv + (uint32_t)3U * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec256 v00 = r11[0U];
                                      Lib_IntVector_Intrinsics_vec256
                                      v1 =
                                        Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00,
                                          (uint32_t)1U);
                                      r11[0U] = v1;
                                      {
                                        Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
                                        Lib_IntVector_Intrinsics_vec256
                                        v10 =
                                          Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01,
                                            (uint32_t)2U);
                                        r22[0U] = v10;
                                        {
                                          Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
                                          Lib_IntVector_Intrinsics_vec256
                                          v11 =
                                            Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02,
                                              (uint32_t)3U);
                                          r32[0U] = v11;
                                          {
                                            uint32_t a0 = (uint32_t)0U;
                                            uint32_t b = (uint32_t)1U;
                                            uint32_t c = (uint32_t)2U;
                                            uint32_t d = (uint32_t)3U;
                                            Lib_IntVector_Intrinsics_vec256
                                            *wv_a = wv + a0 * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec256
                                            *wv_b8 = wv + b * (uint32_t)1U;
                                            wv_a[0U] =
                                              Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U],
                                                wv_b8[0U]);
                                            wv_a[0U] =
                                              Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U],
                                                z[0U]);
                                            {
                                              Lib_IntVector_Intrinsics_vec256
                                              *wv_a8 = wv + d * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec256
                                              *wv_b9 = wv + a0 * (uint32_t)1U;
                                              wv_a8[0U] =
                                                Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U],
                                                  wv_b9[0U]);
                                              wv_a8[0U] =
                                                Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U],
                                                  (uint32_t)32U);
                                              {
                                                Lib_IntVector_Intrinsics_vec256
                                                *wv_a9 = wv + c * (uint32_t)1U;
                                                Lib_IntVector_Intrinsics_vec256
                                                *wv_b10 = wv + d * (uint32_t)1U;
                                                wv_a9[0U] =
                                                  Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U],
                                                    wv_b10[0U]);
                                                {
                                                  Lib_IntVector_Intrinsics_vec256
                                                  *wv_a10 = wv + b * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec256
                                                  *wv_b11 = wv + c * (uint32_t)1U;
                                                  wv_a10[0U] =
                                                    Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U],
                                                      wv_b11[0U]);
                                                  wv_a10[0U] =
                                                    Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U],
                                                      (uint32_t)24U);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec256
                                                    *wv_a11 = wv + a0 * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec256
                                                    *wv_b12 = wv + b * (uint32_t)1U;
                                                    wv_a11[0U] =
                                                      Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U],
                                                        wv_b12[0U]);
                                                    wv_a11[0U] =
                                                      Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U],
                                                        w[0U]);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *wv_a12 = wv + d * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *wv_b13 = wv + a0 * (uint32_t)1U;
                                                      wv_a12[0U] =
                                                        Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U],
                                                          wv_b13[0U]);
                                                      wv_a12[0U] =
                                                        Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U],
                                                          (uint32_t)16U);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec256
                                                        *wv_a13 = wv + c * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec256
                                                        *wv_b14 = wv + d * (uint32_t)1U;
                                                        wv_a13[0U] =
                                                          Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U],
                                                            wv_b14[0U]);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec256
                                                          *wv_a14 = wv + b * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec256
                                                          *wv_b = wv + c * (uint32_t)1U;
                                                          wv_a14[0U] =
                                                            Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U],
                                                              wv_b[0U]);
                                                          wv_a14[0U] =
                                                            Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U],
                                                              (uint32_t)63U);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec256
                                                            *r12 = wv + (uint32_t)1U * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec256
                                                            *r2 = wv + (uint32_t)2U * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec256
                                                            *r3 = wv + (uint32_t)3U * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec256
                                                            v0 = r12[0U];
                                                            Lib_IntVector_Intrinsics_vec256
                                                            v12 =
                                                              Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0,
                                                                (uint32_t)3U);
                                                            r12[0U] = v12;
                                                            {
                                                              Lib_IntVector_Intrinsics_vec256
                                                              v03 = r2[0U];
                                                              Lib_IntVector_Intrinsics_vec256
                                                              v13 =
                                                                Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03,
                                                                  (uint32_t)2U);
                                                              r2[0U] = v13;
                                                              {
                                                                Lib_IntVector_Intrinsics_vec256
                                                                v04 = r3[0U];
                                                                Lib_IntVector_Intrinsics_vec256
                                                                v14 =
                                                                  Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04,
                                                                    (uint32_t)1U);
                                                                r3[0U] = v14;
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            s00 = s + (uint32_t)0U * (uint32_t)1U;
            s16 = s + (uint32_t)1U * (uint32_t)1U;
            r00 = wv + (uint32_t)0U * (uint32_t)1U;
            r10 = wv + (uint32_t)1U * (uint32_t)1U;
            r20 = wv + (uint32_t)2U * (uint32_t)1U;
            r30 = wv + (uint32_t)3U * (uint32_t)1U;
            s00[0U] = Lib_IntVector_Intrinsics_vec256_xor(s00[0U], r00[0U]);
            s00[0U] = Lib_IntVector_Intrinsics_vec256_xor(s00[0U], r20[0U]);
            s16[0U] = Lib_IntVector_Intrinsics_vec256_xor(s16[0U], r10[0U]);
            s16[0U] = Lib_IntVector_Intrinsics_vec256_xor(s16[0U], r30[0U]);
            return FStar_UInt128_uint64_to_uint128((uint64_t)0U);
          }
        }
      }
    }
  }
}

void Hacl_Hash_Blake2b_256_hash_blake2b_256(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  Hacl_Blake2b_256_blake2b((uint32_t)64U, dst, input_len, input, (uint32_t)0U, NULL);
}

static inline void
blake2b_update_block(
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  bool flag,
  FStar_UInt128_uint128 totlen,
  uint8_t *d
)
{
  uint64_t m_w[16U] = { 0U };
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t *os = m_w;
      uint8_t *bj = d + i * (uint32_t)8U;
      uint64_t u = load64_le(bj);
      uint64_t r = u;
      uint64_t x = r;
      os[i] = x;
    }
  }
  {
    Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
    uint64_t wv_14;
    if (flag)
    {
      wv_14 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
    }
    else
    {
      wv_14 = (uint64_t)0U;
    }
    {
      uint64_t wv_15 = (uint64_t)0U;
      Lib_IntVector_Intrinsics_vec256 *wv3;
      Lib_IntVector_Intrinsics_vec256 *s00;
      Lib_IntVector_Intrinsics_vec256 *s16;
      Lib_IntVector_Intrinsics_vec256 *r00;
      Lib_IntVector_Intrinsics_vec256 *r10;
      Lib_IntVector_Intrinsics_vec256 *r20;
      Lib_IntVector_Intrinsics_vec256 *r30;
      mask =
        Lib_IntVector_Intrinsics_vec256_load64s(FStar_UInt128_uint128_to_uint64(totlen),
          FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(totlen, (uint32_t)64U)),
          wv_14,
          wv_15);
      memcpy(wv, hash, (uint32_t)4U * (uint32_t)1U * sizeof (Lib_IntVector_Intrinsics_vec256));
      wv3 = wv + (uint32_t)3U * (uint32_t)1U;
      wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < (uint32_t)12U; i++)
        {
          uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
          KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
          {
            Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
            {
              uint32_t _i;
              for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
            }
            {
              Lib_IntVector_Intrinsics_vec256 *r0 = m_st + (uint32_t)0U * (uint32_t)1U;
              Lib_IntVector_Intrinsics_vec256 *r1 = m_st + (uint32_t)1U * (uint32_t)1U;
              Lib_IntVector_Intrinsics_vec256 *r21 = m_st + (uint32_t)2U * (uint32_t)1U;
              Lib_IntVector_Intrinsics_vec256 *r31 = m_st + (uint32_t)3U * (uint32_t)1U;
              uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
              uint32_t s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
              uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
              uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
              uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
              uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
              uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
              uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
              uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
              uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
              uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
              uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
              uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
              uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
              uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
              uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
              r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
              r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s1], m_w[s3], m_w[s5], m_w[s7]);
              r21[0U] =
                Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8],
                  m_w[s10],
                  m_w[s12],
                  m_w[s14]);
              r31[0U] =
                Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9],
                  m_w[s11],
                  m_w[s13],
                  m_w[s15]);
              {
                Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                uint32_t a = (uint32_t)0U;
                uint32_t b0 = (uint32_t)1U;
                uint32_t c0 = (uint32_t)2U;
                uint32_t d10 = (uint32_t)3U;
                Lib_IntVector_Intrinsics_vec256 *wv_a0 = wv + a * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec256 *wv_b0 = wv + b0 * (uint32_t)1U;
                wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
                wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
                {
                  Lib_IntVector_Intrinsics_vec256 *wv_a1 = wv + d10 * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec256 *wv_b1 = wv + a * (uint32_t)1U;
                  wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
                  wv_a1[0U] =
                    Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U],
                      (uint32_t)32U);
                  {
                    Lib_IntVector_Intrinsics_vec256 *wv_a2 = wv + c0 * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec256 *wv_b2 = wv + d10 * (uint32_t)1U;
                    wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
                    {
                      Lib_IntVector_Intrinsics_vec256 *wv_a3 = wv + b0 * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec256 *wv_b3 = wv + c0 * (uint32_t)1U;
                      wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
                      wv_a3[0U] =
                        Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U],
                          (uint32_t)24U);
                      {
                        Lib_IntVector_Intrinsics_vec256 *wv_a4 = wv + a * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec256 *wv_b4 = wv + b0 * (uint32_t)1U;
                        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
                        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
                        {
                          Lib_IntVector_Intrinsics_vec256 *wv_a5 = wv + d10 * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec256 *wv_b5 = wv + a * (uint32_t)1U;
                          wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
                          wv_a5[0U] =
                            Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U],
                              (uint32_t)16U);
                          {
                            Lib_IntVector_Intrinsics_vec256 *wv_a6 = wv + c0 * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec256 *wv_b6 = wv + d10 * (uint32_t)1U;
                            wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
                            {
                              Lib_IntVector_Intrinsics_vec256 *wv_a7 = wv + b0 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec256 *wv_b7 = wv + c0 * (uint32_t)1U;
                              wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
                              wv_a7[0U] =
                                Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U],
                                  (uint32_t)63U);
                              {
                                Lib_IntVector_Intrinsics_vec256
                                *r11 = wv + (uint32_t)1U * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec256
                                *r22 = wv + (uint32_t)2U * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec256
                                *r32 = wv + (uint32_t)3U * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec256 v00 = r11[0U];
                                Lib_IntVector_Intrinsics_vec256
                                v1 =
                                  Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00,
                                    (uint32_t)1U);
                                r11[0U] = v1;
                                {
                                  Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
                                  Lib_IntVector_Intrinsics_vec256
                                  v10 =
                                    Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01,
                                      (uint32_t)2U);
                                  r22[0U] = v10;
                                  {
                                    Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
                                    Lib_IntVector_Intrinsics_vec256
                                    v11 =
                                      Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02,
                                        (uint32_t)3U);
                                    r32[0U] = v11;
                                    {
                                      uint32_t a0 = (uint32_t)0U;
                                      uint32_t b = (uint32_t)1U;
                                      uint32_t c = (uint32_t)2U;
                                      uint32_t d1 = (uint32_t)3U;
                                      Lib_IntVector_Intrinsics_vec256
                                      *wv_a = wv + a0 * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec256
                                      *wv_b8 = wv + b * (uint32_t)1U;
                                      wv_a[0U] =
                                        Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U],
                                          wv_b8[0U]);
                                      wv_a[0U] =
                                        Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U],
                                          z[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec256
                                        *wv_a8 = wv + d1 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec256
                                        *wv_b9 = wv + a0 * (uint32_t)1U;
                                        wv_a8[0U] =
                                          Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U],
                                            wv_b9[0U]);
                                        wv_a8[0U] =
                                          Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U],
                                            (uint32_t)32U);
                                        {
                                          Lib_IntVector_Intrinsics_vec256
                                          *wv_a9 = wv + c * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec256
                                          *wv_b10 = wv + d1 * (uint32_t)1U;
                                          wv_a9[0U] =
                                            Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U],
                                              wv_b10[0U]);
                                          {
                                            Lib_IntVector_Intrinsics_vec256
                                            *wv_a10 = wv + b * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec256
                                            *wv_b11 = wv + c * (uint32_t)1U;
                                            wv_a10[0U] =
                                              Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U],
                                                wv_b11[0U]);
                                            wv_a10[0U] =
                                              Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U],
                                                (uint32_t)24U);
                                            {
                                              Lib_IntVector_Intrinsics_vec256
                                              *wv_a11 = wv + a0 * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec256
                                              *wv_b12 = wv + b * (uint32_t)1U;
                                              wv_a11[0U] =
                                                Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U],
                                                  wv_b12[0U]);
                                              wv_a11[0U] =
                                                Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U],
                                                  w[0U]);
                                              {
                                                Lib_IntVector_Intrinsics_vec256
                                                *wv_a12 = wv + d1 * (uint32_t)1U;
                                                Lib_IntVector_Intrinsics_vec256
                                                *wv_b13 = wv + a0 * (uint32_t)1U;
                                                wv_a12[0U] =
                                                  Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U],
                                                    wv_b13[0U]);
                                                wv_a12[0U] =
                                                  Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U],
                                                    (uint32_t)16U);
                                                {
                                                  Lib_IntVector_Intrinsics_vec256
                                                  *wv_a13 = wv + c * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec256
                                                  *wv_b14 = wv + d1 * (uint32_t)1U;
                                                  wv_a13[0U] =
                                                    Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U],
                                                      wv_b14[0U]);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec256
                                                    *wv_a14 = wv + b * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec256
                                                    *wv_b = wv + c * (uint32_t)1U;
                                                    wv_a14[0U] =
                                                      Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U],
                                                        wv_b[0U]);
                                                    wv_a14[0U] =
                                                      Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U],
                                                        (uint32_t)63U);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *r12 = wv + (uint32_t)1U * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *r2 = wv + (uint32_t)2U * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *r3 = wv + (uint32_t)3U * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec256 v0 = r12[0U];
                                                      Lib_IntVector_Intrinsics_vec256
                                                      v12 =
                                                        Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0,
                                                          (uint32_t)3U);
                                                      r12[0U] = v12;
                                                      {
                                                        Lib_IntVector_Intrinsics_vec256
                                                        v03 = r2[0U];
                                                        Lib_IntVector_Intrinsics_vec256
                                                        v13 =
                                                          Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03,
                                                            (uint32_t)2U);
                                                        r2[0U] = v13;
                                                        {
                                                          Lib_IntVector_Intrinsics_vec256
                                                          v04 = r3[0U];
                                                          Lib_IntVector_Intrinsics_vec256
                                                          v14 =
                                                            Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04,
                                                              (uint32_t)1U);
                                                          r3[0U] = v14;
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      s00 = hash + (uint32_t)0U * (uint32_t)1U;
      s16 = hash + (uint32_t)1U * (uint32_t)1U;
      r00 = wv + (uint32_t)0U * (uint32_t)1U;
      r10 = wv + (uint32_t)1U * (uint32_t)1U;
      r20 = wv + (uint32_t)2U * (uint32_t)1U;
      r30 = wv + (uint32_t)3U * (uint32_t)1U;
      s00[0U] = Lib_IntVector_Intrinsics_vec256_xor(s00[0U], r00[0U]);
      s00[0U] = Lib_IntVector_Intrinsics_vec256_xor(s00[0U], r20[0U]);
      s16[0U] = Lib_IntVector_Intrinsics_vec256_xor(s16[0U], r10[0U]);
      s16[0U] = Lib_IntVector_Intrinsics_vec256_xor(s16[0U], r30[0U]);
    }
  }
}

inline void
Hacl_Blake2b_256_blake2b_init(
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  uint32_t kk,
  uint8_t *k,
  uint32_t nn
)
{
  uint8_t b[128U] = { 0U };
  Lib_IntVector_Intrinsics_vec256 *r0 = hash + (uint32_t)0U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r1 = hash + (uint32_t)1U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r2 = hash + (uint32_t)2U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r3 = hash + (uint32_t)3U * (uint32_t)1U;
  uint64_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
  uint64_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
  uint64_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
  uint64_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
  uint64_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
  uint64_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
  uint64_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
  uint64_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
  uint64_t kk_shift_8;
  uint64_t iv0_;
  r2[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0, iv1, iv2, iv3);
  r3[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
  kk_shift_8 = (uint64_t)kk << (uint32_t)8U;
  iv0_ = iv0 ^ ((uint64_t)0x01010000U ^ (kk_shift_8 ^ (uint64_t)nn));
  r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_, iv1, iv2, iv3);
  r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
  if (!(kk == (uint32_t)0U))
  {
    memcpy(b, k, kk * sizeof (uint8_t));
    {
      FStar_UInt128_uint128
      totlen =
        FStar_UInt128_add_mod(FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)0U),
          FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U));
      uint8_t *b1 = b + (uint32_t)0U * (uint32_t)128U;
      blake2b_update_block(wv, hash, false, totlen, b1);
    }
  }
  Lib_Memzero0_memzero(b, (uint32_t)128U * sizeof (b[0U]));
}

inline void
Hacl_Blake2b_256_blake2b_update_multi(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  FStar_UInt128_uint128 prev,
  uint8_t *blocks,
  uint32_t nb
)
{
  uint32_t i;
  for (i = (uint32_t)0U; i < nb; i++)
  {
    FStar_UInt128_uint128
    totlen =
      FStar_UInt128_add_mod(prev,
        FStar_UInt128_uint64_to_uint128((uint64_t)((i + (uint32_t)1U) * (uint32_t)128U)));
    uint8_t *b = blocks + i * (uint32_t)128U;
    blake2b_update_block(wv, hash, false, totlen, b);
  }
}

inline void
Hacl_Blake2b_256_blake2b_update_last(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  FStar_UInt128_uint128 prev,
  uint32_t rem,
  uint8_t *d
)
{
  uint8_t b[128U] = { 0U };
  uint8_t *last = d + len - rem;
  FStar_UInt128_uint128 totlen;
  memcpy(b, last, rem * sizeof (uint8_t));
  totlen = FStar_UInt128_add_mod(prev, FStar_UInt128_uint64_to_uint128((uint64_t)len));
  blake2b_update_block(wv, hash, true, totlen, b);
  Lib_Memzero0_memzero(b, (uint32_t)128U * sizeof (b[0U]));
}

static inline void
blake2b_update_blocks(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  FStar_UInt128_uint128 prev,
  uint8_t *blocks
)
{
  uint32_t nb0 = len / (uint32_t)128U;
  uint32_t rem0 = len % (uint32_t)128U;
  K___uint32_t_uint32_t scrut;
  if (rem0 == (uint32_t)0U && nb0 > (uint32_t)0U)
  {
    uint32_t nb_ = nb0 - (uint32_t)1U;
    uint32_t rem_ = (uint32_t)128U;
    K___uint32_t_uint32_t lit;
    lit.fst = nb_;
    lit.snd = rem_;
    scrut = lit;
  }
  else
  {
    K___uint32_t_uint32_t lit;
    lit.fst = nb0;
    lit.snd = rem0;
    scrut = lit;
  }
  {
    uint32_t nb = scrut.fst;
    uint32_t rem = scrut.snd;
    Hacl_Blake2b_256_blake2b_update_multi(len, wv, hash, prev, blocks, nb);
    Hacl_Blake2b_256_blake2b_update_last(len, wv, hash, prev, rem, blocks);
  }
}

inline void
Hacl_Blake2b_256_blake2b_finish(
  uint32_t nn,
  uint8_t *output,
  Lib_IntVector_Intrinsics_vec256 *hash
)
{
  uint32_t double_row = (uint32_t)2U * ((uint32_t)4U * (uint32_t)8U);
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  {
    uint8_t b[double_row];
    memset(b, 0U, double_row * sizeof (uint8_t));
    {
      uint8_t *first = b;
      uint8_t *second = b + (uint32_t)4U * (uint32_t)8U;
      Lib_IntVector_Intrinsics_vec256 *row0 = hash + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *row1 = hash + (uint32_t)1U * (uint32_t)1U;
      uint8_t *final;
      Lib_IntVector_Intrinsics_vec256_store64_le(first, row0[0U]);
      Lib_IntVector_Intrinsics_vec256_store64_le(second, row1[0U]);
      final = b;
      memcpy(output, final, nn * sizeof (uint8_t));
      Lib_Memzero0_memzero(b, double_row * sizeof (b[0U]));
    }
  }
}

void
Hacl_Blake2b_256_blake2b(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *k
)
{
  uint32_t stlen = (uint32_t)4U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 stzero = Lib_IntVector_Intrinsics_vec256_zero;
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), stlen);
  {
    Lib_IntVector_Intrinsics_vec256 b[stlen];
    {
      uint32_t _i;
      for (_i = 0U; _i < stlen; ++_i)
        b[_i] = stzero;
    }
    {
      FStar_UInt128_uint128 prev0;
      if (kk == (uint32_t)0U)
      {
        prev0 = FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)0U);
      }
      else
      {
        prev0 = FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U);
      }
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), stlen);
      {
        Lib_IntVector_Intrinsics_vec256 b1[stlen];
        {
          uint32_t _i;
          for (_i = 0U; _i < stlen; ++_i)
            b1[_i] = stzero;
        }
        Hacl_Blake2b_256_blake2b_init(b1, b, kk, k, nn);
        blake2b_update_blocks(ll, b1, b, prev0, d);
        Hacl_Blake2b_256_blake2b_finish(nn, output, b);
        Lib_Memzero0_memzero(b1, stlen * sizeof (b1[0U]));
        Lib_Memzero0_memzero(b, stlen * sizeof (b[0U]));
      }
    }
  }
}

