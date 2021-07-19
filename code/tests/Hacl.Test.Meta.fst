module Hacl.Test.Meta

open FStar.UInt
open Lib.Sliceable
open FStar.Tactics

#set-options "--fuel 0 --ifuel 1 --z3rlimit 0"

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

let pp (_:unit) : Tac unit = norm []; dump ""; trefl ()

// are value of type `term` typed-checked?
// what's inside `bv_view`? inside a binder?

(*
//[@@postprocess_with pp]
val synt_test (_:unit) : Tac decls
let synt_test () = // trying to build `test:(#ty:Type0 -> ty -> ty) = fun (#ty:Type0) (x:ty) -> x`
  let arrow (bv:bv) (typ:term) : Tac term = pack (Tv_Arrow (pack_binder bv Q_Explicit []) (pack_comp (C_Total typ []))) in
  let arrow_implicit (bv:bv) (typ:term) : Tac term = pack (Tv_Arrow (pack_binder bv Q_Implicit []) (pack_comp (C_Total typ []))) in

  let bv0 = pack_bv ({
    bv_ppname = "ty";
    bv_index = 0;
    //bv_sort = pack (Tv_Type ());
    bv_sort = (`Type0);
  }) in
  let typ = pack (Tv_BVar bv0) in
  let bv1 = pack_bv ({
    bv_ppname = "x";
    bv_index = 1;
    bv_sort = typ;
  }) in

  // build type
  let decltyp = arrow_implicit bv0 (arrow bv1 typ) in

  // build term
  let binder0 = pack_binder bv0 Q_Implicit [] in
  let binder1 = pack_binder bv1 Q_Explicit [] in
  let body = pack (Tv_Abs binder0 (Tv_Abs binder1 (pack (Tv_BVar bv1)))) in

  // Generate the declaration
  let xname:string = "test" in
  let module_name = cur_module () in
  let fv = pack_fv (List.Tot.snoc (module_name, xname)) in
  let is_recursive = false in
  let sig : sigelt_view = Sg_Let is_recursive fv [] decltyp body in
  [pack_sigelt sig]

let foo = ()

%splice[test](synt_test ())
*)
