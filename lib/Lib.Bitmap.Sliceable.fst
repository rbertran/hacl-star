module Lib.Bitmap.Sliceable

open Lib.Sliceable
open Lib.Bitmap

val u1xN (t:intt) (l:secl) (n:nat) : (xN:sig n{xN.t == bitmap t l n})
let u1xN it sl n =
{ t = bitmap it sl n
; v = bitmap_v
; mk = bitmap_mk it sl n
; mk_def = bitmap_mk_def it sl n
; ones_ = bitmap_ones
; zeros_ = bitmap_zeros
; and_ = bitmap_and
; xor_ = bitmap_xor
; or_ = bitmap_or
; not_ = bitmap_not
; zeros_spec = bitmap_zeros_spec #it #sl #n
; ones_spec = bitmap_ones_spec #it #sl #n
; and_spec = bitmap_and_spec
; xor_spec = bitmap_xor_spec
; or_spec = bitmap_or_spec
; not_spec = bitmap_not_spec
}
