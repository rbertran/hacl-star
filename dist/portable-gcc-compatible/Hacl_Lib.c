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


#include "Hacl_Lib.h"

/* SNIPPET_START: Lib_Transposition64x8_transpose_bits64 */

uint64_t Lib_Transposition64x8_transpose_bits64(uint64_t x)
{
  uint64_t m0 = (uint64_t)0x8040201008040201U;
  uint64_t m1 = (uint64_t)0x4020100804020100U;
  uint64_t m2 = (uint64_t)0x2010080402010000U;
  uint64_t m3 = (uint64_t)0x1008040201000000U;
  uint64_t m4 = (uint64_t)0x0804020100000000U;
  uint64_t m5 = (uint64_t)0x0402010000000000U;
  uint64_t m6 = (uint64_t)0x0201000000000000U;
  uint64_t m7 = (uint64_t)0x0100000000000000U;
  uint64_t y0 = x & m0;
  uint64_t y1 = y0 | (x & m1) >> (uint32_t)7U;
  uint64_t y2 = y1 | (x & m2) >> (uint32_t)14U;
  uint64_t y3 = y2 | (x & m3) >> (uint32_t)21U;
  uint64_t y4 = y3 | (x & m4) >> (uint32_t)28U;
  uint64_t y5 = y4 | (x & m5) >> (uint32_t)35U;
  uint64_t y6 = y5 | (x & m6) >> (uint32_t)42U;
  uint64_t y7 = y6 | (x & m7) >> (uint32_t)49U;
  uint64_t y8 = y7 | (x << (uint32_t)7U & m1);
  uint64_t y9 = y8 | (x << (uint32_t)14U & m2);
  uint64_t y10 = y9 | (x << (uint32_t)21U & m3);
  uint64_t y11 = y10 | (x << (uint32_t)28U & m4);
  uint64_t y12 = y11 | (x << (uint32_t)35U & m5);
  uint64_t y13 = y12 | (x << (uint32_t)42U & m6);
  return y13 | (x << (uint32_t)49U & m7);
}

/* SNIPPET_END: Lib_Transposition64x8_transpose_bits64 */

