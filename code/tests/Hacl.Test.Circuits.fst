module Hacl.Test.Circuits

open Lib.Sliceable
open Lib.Circuits
open FStar.Tactics

module UI=FStar.UInt

let m:pos = 8
let p:pos = 16

let circ : circuit m p =
  normalize_term(
    let rec aux (i:nat) : circuit m (i+1) =
      if i=0 then
        Cons Empty (Input 0)
      else
        Cons (aux (i-1)) (Xor (i-1) (i-1))
    in
    aux (p-1)
  )


open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
module B=Lib.Bitmap
module IT=Lib.IntTypes

let lN = B.uN IT.U64 IT.SEC 64

let pp (_:unit) : Tac unit =
  norm [ delta_only [`%m; `%p] ];
  norm [ delta_only [`%circuit_impl] ];

  // unroll circuit
  norm [ zeta; delta_only [`%rev; `%circ]; iota ];

  // normalize initial acc
  norm [ zeta; delta_only [`%xNxM_empty; `%xNxM_mk]; iota; primops ];

  let _ = repeatn (p+1) (fun _ ->
    norm [ zeta; delta_only [`%circuit_impl_aux] ];
    norm [ zeta; delta_only [`%index]; iota; primops ];
    ()
  ) in

  norm [ delta_only
    [ `%lN
    ; `%Mkfoo?.t
    ; `%Mkbar?.xN
    ; `%Lib.Bitmap.uN
    ; `%Mkbar
    ; `%Mkbar?.xor_
    ]
  ];

  dump "";
  trefl ()

[@@postprocess_with pp]
let test2 (x:xNxM lN.xN m) :
  Stack (xNxM lN.xN p)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> True)
  =
  circuit_impl circ lN x

let pp' (_:unit) : Tac unit =
  norm [ delta_only [`%test2] ];
  norm [ delta_only
    [ `%lN
    ; `%Mkfoo?.t
    ; `%Mkbar?.xN
    ; `%Lib.Bitmap.uN
    ; `%Mkbar
    ; `%Mkbar?.xor_
    ]
  ];
  dump "";
  trefl ()

[@@postprocess_with pp']
let test3 (x:xNxM lN.xN m) :
  Stack (xNxM lN.xN p)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> True)
  =
  test2 x

let impl (lN:bar) (x:xNxM lN.xN m) : xNxM lN.xN p =
  circuit_spec2 circ lN x

let spec (a:UI.uint_t m) : UI.uint_t p = a % 2

let test1 (lN:bar) : Lemma (
  forall (x:xNxM lN.xN m) (j:nat{j<lN.xN.n}).
  column j (impl lN x) == of_uint (spec (to_uint (column j x)))
  ) =
  let impl' (x:x1xM bool m) : x1xM bool p = impl l1 x in
  let phi (i:UI.uint_t m) : bool = x1xM_eq (impl' (of_uint i)) (of_uint (spec i)) in
  assert(bruteforce_aux m phi) by (
    norm [ delta ];
    trefl ()
  );
  admit ()

