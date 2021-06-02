module Hacl.Test.Sliceable

open FStar.Mul
open FStar.UInt
open Lib.Sliceable

let circ : circuit 8 62 = fun i -> match i with
| 0 -> Input 0    | 1 -> Input 1    | 2 -> Input 2    | 3 -> Input 3    | 4 -> Input 4    | 5 -> Input 5
| 6 -> Input 6    | 7 -> Input 7    | 8 -> Input 0    | 9 -> Input 1    | 10 -> Input 2   | 11 -> Input 3
| 12 -> Input 4   | 13 -> Input 5   | 14 -> Input 6   | 15 -> Input 7   | 16 -> Xor  0  8 | 17 -> And  0  8
| 18 -> Xor 1 9   | 19 -> Xor 17 18 | 20 -> And 1 9   | 21 -> And 1 17  | 22 -> And 9 17  | 23 -> Or 20 21
| 24 -> Or 22 23  | 25 -> Xor 2 10  | 26 -> Xor 24 25 | 27 -> And 2 10  | 28 -> And 2 24  | 29 -> And 10 24
| 30 -> Or 27 28  | 31 -> Or 29 30  | 32 -> Xor 3 11  | 33 -> Xor 31 32 | 34 -> And 3 11  | 35 -> And 3 31
| 36 -> And 11 31 | 37 -> Or 34 35  | 38 -> Or 36 37  | 39 -> Xor 4 12  | 40 -> Xor 38 39 | 41 -> And 4 12
| 42 -> And 4 38  | 43 -> And 12 38 | 44 -> Or 41 42  | 45 -> Or 43 44  | 46 -> Xor 5 13  | 47 -> Xor 45 46
| 48 -> And 5 13  | 49 -> And 5 45  | 50 -> And 13 45 | 51 -> Or 48 49  | 52 -> Or 50 51  | 53 -> Xor 6 14
| 54 -> Xor 52 53 | 55 -> And 6 14  | 56 -> And 6 52  | 57 -> And 14 52 | 58 -> Or 55 56  | 59 -> Or 57 58
| 60 -> Xor 7 15  | 61 -> Xor 59 60

let outputs : circuit 62 8 = fun i -> match i with
| 0 -> Input 16 | 1 -> Input 19 | 2 -> Input 26 | 3 -> Input 33
| 4 -> Input 40 | 5 -> Input 47 | 6 -> Input 54 | 7 -> Input 61

let impl1 (#n:nat) (#xN:sig n) (x:xNxM xN 8) : xNxM xN 8 =
  circuit_spec outputs (circuit_spec circ x)

val sliceable_impl1 (_:unit) : Lemma (sliceable impl1)
let sliceable_impl1 () = sliceable_comp (circuit_spec outputs) (circuit_spec circ)

let impl2 (#n:nat) (#xN:sig n) (x:xNxM xN 8) : (y:xNxM xN 8{y == impl1 x}) =
  let a0 : xN.t = index x 0 in
  let a1 : xN.t = index x 1 in
  let a2 : xN.t = index x 2 in
  let a3 : xN.t = index x 3 in
  let a4 : xN.t = index x 4 in
  let a5 : xN.t = index x 5 in
  let a6 : xN.t = index x 6 in
  let a7 : xN.t = index x 7 in
  let a8 : xN.t = index x 0 in
  let a9 : xN.t = index x 1 in
  let a10 : xN.t = index x 2 in
  let a11 : xN.t = index x 3 in
  let a12 : xN.t = index x 4 in
  let a13 : xN.t = index x 5 in
  let a14 : xN.t = index x 6 in
  let a15 : xN.t = index x 7 in
  let a16 : xN.t = a0 ^^^ a8 in
  let a17 : xN.t = a0 &&& a8 in
  let a18 : xN.t = a1 ^^^ a9 in
  let a19 : xN.t = a17 ^^^ a18 in
  let a20 : xN.t = a1 &&& a9 in
  let a21 : xN.t = a1 &&& a17 in
  let a22 : xN.t = a9 &&& a17 in
  let a23 : xN.t = a20 ||| a21 in
  let a24 : xN.t = a22 ||| a23 in
  let a25 : xN.t = a2 ^^^ a10 in
  let a26 : xN.t = a24 ^^^ a25 in
  let a27 : xN.t = a2 &&& a10 in
  let a28 : xN.t = a2 &&& a24 in
  let a29 : xN.t = a10 &&& a24 in
  let a30 : xN.t = a27 ||| a28 in
  let a31 : xN.t = a29 ||| a30 in
  let a32 : xN.t = a3 ^^^ a11 in
  let a33 : xN.t = a31 ^^^ a32 in
  let a34 : xN.t = a3 &&& a11 in
  let a35 : xN.t = a3 &&& a31 in
  let a36 : xN.t = a11 &&& a31 in
  let a37 : xN.t = a34 ||| a35 in
  let a38 : xN.t = a36 ||| a37 in
  let a39 : xN.t = a4 ^^^ a12 in
  let a40 : xN.t = a38 ^^^ a39 in
  let a41 : xN.t = a4 &&& a12 in
  let a42 : xN.t = a4 &&& a38 in
  let a43 : xN.t = a12 &&& a38 in
  let a44 : xN.t = a41 ||| a42 in
  let a45 : xN.t = a43 ||| a44 in
  let a46 : xN.t = a5 ^^^ a13 in
  let a47 : xN.t = a45 ^^^ a46 in
  let a48 : xN.t = a5 &&& a13 in
  let a49 : xN.t = a5 &&& a45 in
  let a50 : xN.t = a13 &&& a45 in
  let a51 : xN.t = a48 ||| a49 in
  let a52 : xN.t = a50 ||| a51 in
  let a53 : xN.t = a6 ^^^ a14 in
  let a54 : xN.t = a52 ^^^ a53 in
  let a55 : xN.t = a6 &&& a14 in
  let a56 : xN.t = a6 &&& a52 in
  let a57 : xN.t = a14 &&& a52 in
  let a58 : xN.t = a55 ||| a56 in
  let a59 : xN.t = a57 ||| a58 in
  let a60 : xN.t = a7 ^^^ a15 in
  let a61 : xN.t = a59 ^^^ a60 in
  let y = xNxM_mk xN 8 (fun i -> match i with
  | 0 -> a16 | 1 -> a19 | 2 -> a26 | 3 -> a33
  | 4 -> a40 | 5 -> a47 | 6 -> a54 | 7 -> a61
  ) in
  assume (y == impl1 x);
  y

val sliceable_impl2 (_:unit) : Lemma (sliceable impl2)
let sliceable_impl2 () =
  sliceable_impl1 ();
  sliceable_feq impl1 impl2

val spec (p:uint_t 8) : uint_t 8
let spec p = (2*p)%256

private val spec_lemma (x:u1xM 8) : Lemma (impl2 x == of_uint (spec (to_uint x)))
let spec_lemma x =
    let phi' (p:uint_t 8) : bool = impl2 (of_uint p) = of_uint (spec p) in
    let phi (x:u1xM 8) : Type0 = impl2 x = of_uint (spec (to_uint x)) in
    assert_norm (bruteforce phi');
    bruteforce_lemma phi';
    forall_uint_lemma phi

val spec_theorem (#n:nat) (#xN:sig n) (x:xNxM xN 8) (j:nat{j<n}) :
  Lemma (column j (impl2 x) == of_uint (spec (to_uint (column j x))))
let spec_theorem x j =
  sliceable_impl2 ();
  spec_lemma (column j x)
