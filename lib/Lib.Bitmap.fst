module Lib.Bitmap

open Lib.IntTypes
open Lib.Sliceable

private val aux (t:inttype{unsigned t}) (l:secrecy_level) : (xN:sig (bits t){xN.t == uint_t t l})
#push-options "--fuel 1 --ifuel 1"
let aux t l =
{ t = int_t t l
; v = (fun x i -> FStar.UInt.nth #(bits t) (v x) i)
; mk = (fun f -> mk_int (UInt.from_vec #(bits t) (FStar.Seq.init (bits t) f)))
; mk_def = (fun f i -> ())
; ones_ = Lib.IntTypes.ones t l
; zeros_ = Lib.IntTypes.zeros t l
; and_ = logand
; xor_ = logxor
; or_ = logor
; not_ = lognot
; zeros_spec = (fun i -> UInt.zero_nth_lemma #(bits t) i)
; ones_spec = (fun i -> UInt.ones_nth_lemma #(bits t) i)
; and_spec = (fun x y i -> logand_spec x y)
; xor_spec = (fun x y i -> logxor_spec x y)
; or_spec = (fun x y i -> logor_spec x y)
; not_spec = (fun x i -> lognot_spec x)
}
#pop-options

val bitmap (t:inttype{unsigned t}) (l:secrecy_level) (n:nat) : Type0
let rec bitmap t l n = if n <= bits t then int_t t l else int_t t l * bitmap t l (n-bits t)

val uN (t:inttype{unsigned t}) (l:secrecy_level) (n:nat) : (xN:sig n{xN.t == bitmap t l n})
let rec uN t l n =
  if n = bits t then
    aux t l
  else if n < bits t then
    xN_rest (aux t l) n
  else
    xN_concat (aux t l) (uN t l (n-bits t))
