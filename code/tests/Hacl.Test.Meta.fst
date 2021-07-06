module Hacl.Test.Meta

open FStar.UInt
open Lib.Sliceable
open FStar.Tactics

#set-options "--fuel 0 --ifuel 0 --z3rlimit 0"

/// Refs:
/// FStar/ulib/experimental/FStar.InteractiveHelpers.*
/// hacl-star/code/Meta.Interface.specialize
/// Construct typing proof by hand?

// "inspect" opens a term (returns a term view)
// "pack" closes a term: term_view -> term

val synthesize_const (xname : string) (x : nat) : Tac decls
let synthesize_const xname x =
  let module_name = cur_module () in
  // ["Hacl"; "Test"; "Meta"; xname]
  let fv = pack_fv (List.Tot.snoc (module_name, xname)) in
  let typ = (`nat) in // Quote `Nat`
  // Or:
  // let typ = pack_fv ["Prims"; "nat"] in
  // let typ = pack (Tv_FVar typ) in
  let body = pack (Tv_Const (C_Int x)) in
  let is_recursive = false in
  // Generate the declaration
  let sig : sigelt_view = Sg_Let is_recursive fv [] typ body in
  [pack_sigelt sig]

// let const0 = 3
%splice[const0](synthesize_const "const0" 3)

[@@"opaque_to_smt"]
let test_opaque : nat = 0

let test_opaque_is_0 () : Lemma (test_opaque == 0) =
  reveal_opaque (`%test_opaque) test_opaque

[@@"opaque_to_smt"]
let ls = [
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;

  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
  0; 0; 0; 0; 0; 0; 0; 0;
]

let ls_length = normalize_term(List.Tot.length ls)

// No need for `assert_norm` because of `normalize_term`
let ls_test () : Lemma (ls_length == 128) = ()
