module Hacl.Test.Circuits

open Lib.Sliceable
open Lib.Circuits
open FStar.Tactics

module UI=FStar.UInt

let m:pos = 1
let p:pos = 4

let circ : circuit m p =
  let rec aux (i:nat) : circuit m (i+1) =
    if i=0 then
      Cons Empty (Input 0)
    else
      Cons (aux (i-1)) (Xor (i-1) (i-1))
  in
  aux (p-1)

let impl (lN:bar) (x:xNxM lN.xN m) : xNxM lN.xN p =
  circuit_spec2 circ lN x

let spec (a:UI.uint_t m) : UI.uint_t p = a % 2

let foo (lN:bar) : Lemma (
  forall (x:xNxM lN.xN m) (j:nat{j<lN.xN.n}).
  column j (impl lN x) == of_uint (spec (to_uint (column j x)))
  ) =
  let impl' (x:x1xM bool m) : x1xM bool p = impl l1 x in
  circuit_spec2_sliceable circ lN;
  assert(sliceable (impl lN) impl');
  assert(let i = 1 in x1xM_eq (impl' (of_uint i)) (of_uint (spec i))) by (
    //norm [ delta_only [`%impl; `%l1; `%x1; `%Mkfoo?.t]; delta; iota; primops; simplify; nbe ];
    norm [ delta; iota; primops; simplify; nbe ];
    norm [ zeta; delta_only [`%circuit_spec2] ];
    norm [ delta; iota; primops; simplify; nbe ];
    dump "";
    //norm [ delta; zeta; iota; primops; simplify; nbe ];
    qed ()
  );
  admit ()
