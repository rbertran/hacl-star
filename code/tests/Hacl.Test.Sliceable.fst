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

// TODO:
// this should not be written by hand
// but produced by a tactic
#push-options "--z3rlimit 100"
let impl2 (#n:nat) (#xN:sig n) (x:xNxM xN 8) : (y:xNxM xN 8{y == impl1 x}) =
  let a0 : foo circ x 0 = circuit_input 0 in
  let a1 : foo circ x 1 = circuit_input 1 in
  let a2 : foo circ x 2 = circuit_input 2 in
  let a3 : foo circ x 3 = circuit_input 3 in
  let a4 : foo circ x 4 = circuit_input 4 in
  let a5 : foo circ x 5 = circuit_input 5 in
  let a6 : foo circ x 6 = circuit_input 6 in
  let a7 : foo circ x 7 = circuit_input 7 in
  let a8 : foo circ x 8 = circuit_input 0 in
  let a9 : foo circ x 9 = circuit_input 1 in
  let a10 : foo circ x 10 = circuit_input 2 in
  let a11 : foo circ x 11 = circuit_input 3 in
  let a12 : foo circ x 12 = circuit_input 4 in
  let a13 : foo circ x 13 = circuit_input 5 in
  let a14 : foo circ x 14 = circuit_input 6 in
  let a15 : foo circ x 15 = circuit_input 7 in
  let a16 : foo circ x 16 = circuit_xor a0 a8 in
  let a17 : foo circ x 17 = circuit_and a0 a8 in
  let a18 : foo circ x 18 = circuit_xor a1 a9 in
  let a19 : foo circ x 19 = circuit_xor a17 a18 in
  let a20 : foo circ x 20 = circuit_and a1 a9 in
  let a21 : foo circ x 21 = circuit_and a1 a17 in
  let a22 : foo circ x 22 = circuit_and a9 a17 in
  let a23 : foo circ x 23 = circuit_or a20 a21 in
  let a24 : foo circ x 24 = circuit_or a22 a23 in
  let a25 : foo circ x 25 = circuit_xor a2 a10 in
  let a26 : foo circ x 26 = circuit_xor a24 a25 in
  let a27 : foo circ x 27 = circuit_and a2 a10 in
  let a28 : foo circ x 28 = circuit_and a2 a24 in
  let a29 : foo circ x 29 = circuit_and a10 a24 in
  let a30 : foo circ x 30 = circuit_or a27 a28 in
  let a31 : foo circ x 31 = circuit_or a29 a30 in
  let a32 : foo circ x 32 = circuit_xor a3 a11 in
  let a33 : foo circ x 33 = circuit_xor a31 a32 in
  let a34 : foo circ x 34 = circuit_and a3 a11 in
  let a35 : foo circ x 35 = circuit_and a3 a31 in
  let a36 : foo circ x 36 = circuit_and a11 a31 in
  let a37 : foo circ x 37 = circuit_or a34 a35 in
  let a38 : foo circ x 38 = circuit_or a36 a37 in
  let a39 : foo circ x 39 = circuit_xor a4 a12 in
  let a40 : foo circ x 40 = circuit_xor a38 a39 in
  let a41 : foo circ x 41 = circuit_and a4 a12 in
  let a42 : foo circ x 42 = circuit_and a4 a38 in
  let a43 : foo circ x 43 = circuit_and a12 a38 in
  let a44 : foo circ x 44 = circuit_or a41 a42 in
  let a45 : foo circ x 45 = circuit_or a43 a44 in
  let a46 : foo circ x 46 = circuit_xor a5 a13 in
  let a47 : foo circ x 47 = circuit_xor a45 a46 in
  let a48 : foo circ x 48 = circuit_and a5 a13 in
  let a49 : foo circ x 49 = circuit_and a5 a45 in
  let a50 : foo circ x 50 = circuit_and a13 a45 in
  let a51 : foo circ x 51 = circuit_or a48 a49 in
  let a52 : foo circ x 52 = circuit_or a50 a51 in
  let a53 : foo circ x 53 = circuit_xor a6 a14 in
  let a54 : foo circ x 54 = circuit_xor a52 a53 in
  let a55 : foo circ x 55 = circuit_and a6 a14 in
  let a56 : foo circ x 56 = circuit_and a6 a52 in
  let a57 : foo circ x 57 = circuit_and a14 a52 in
  let a58 : foo circ x 58 = circuit_or a55 a56 in
  let a59 : foo circ x 59 = circuit_or a57 a58 in
  let a60 : foo circ x 60 = circuit_xor a7 a15 in
  let a61 : foo circ x 61 = circuit_xor a59 a60 in
  let f (i:nat{i<8}) = match i with
  | 0 -> Foo?.u a16 | 1 -> Foo?.u a19 | 2 -> Foo?.u a26 | 3 -> Foo?.u a33
  | 4 -> Foo?.u a40 | 5 -> Foo?.u a47 | 6 -> Foo?.u a54 | 7 -> Foo?.u a61
  in
  let y : xNxM xN 8 = xNxM_mk _ _ f in
  xNxM_eq_intro y (impl1 x);
  y
#pop-options

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
