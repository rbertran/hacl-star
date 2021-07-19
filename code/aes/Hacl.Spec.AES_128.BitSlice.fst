module Hacl.Spec.AES_128.BitSlice

open Lib.IntTypes

let transpose_bits64 (x:uint64) : Tot uint64 =
  Lib.Transposition64x8.transpose_bits64 x

inline_for_extraction
val transpose_bits64x8:
  i0:uint64 -> i1:uint64 -> i2: uint64 -> i3:uint64 ->
  i4:uint64 -> i5:uint64 -> i6: uint64 -> i7:uint64 ->
  Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

let transpose_bits64x8 i0 i1 i2 i3 i4 i5 i6 i7 =
  //let (((j0,j1),(j2,j3)),((j4,j5),(j6,j7))) =
  //  Lib.Transposition64x8.transpose_bits64x8 (((i0,i1),(i2,i3)),((i4,i5),(i6,i7)))
  //in
  //(j0,j1,j2,j3,j4,j5,j6,j7)
  (i0,i1,i2,i3,i4,i5,i6,i7)

inline_for_extraction
val sub_bytes64x8:
    uint64 -> uint64 -> uint64 -> uint64
  -> uint64 -> uint64 -> uint64 -> uint64 ->
  Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)
let sub_bytes64x8 (st0:uint64) (st1:uint64) (st2:uint64) (st3:uint64) (st4:uint64) (st5:uint64) (st6:uint64) (st7:uint64) =
  //let (s7,(s6,(s5,(s4,(s3,(s2,(s1,(s0,())))))))) :
  //  uint64*(uint64*(uint64*(uint64*(uint64*(uint64*(uint64*(uint64*unit))))))) =
  //  Hacl.Impl.AES.SubBytes.subBytes64 (st7,(st6,(st5,(st4,(st3,(st2,(st1,(st0,()))))))))
  //in
  //(s0,s1,s2,s3,s4,s5,s6,s7)
  (st0,st1,st2,st3,st4,st5,st6,st7)


inline_for_extraction
let shift_row64 (u:uint64) =
  let u = (u &. u64 0x1111111111111111) |.
          ((u &. u64 0x2220222022202220) >>. size 4) |.
          ((u &. u64 0x0002000200020002) <<. size 12) |.
          ((u &. u64 0x4400440044004400) >>. size 8) |.
          ((u &. u64 0x0044004400440044) <<. size 8) |.
          ((u &. u64 0x8000800080008000) >>. size 12) |.
          ((u &. u64 0x0888088808880888) <<. size 4) in
  u
