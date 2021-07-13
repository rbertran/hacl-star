module Lib.Circuits

#set-options "--fuel 0 --ifuel 0"

open Lib.Sliceable

(*** Circuits ***)

type gate (m:nat) (c:nat) =
| Zeros
| Ones
| Input : (i:nat{i<m}) -> gate m c
| Xor : (a:nat{a<c}) -> (b:nat{b<c}) -> gate m c
| And : (a:nat{a<c}) -> (b:nat{b<c}) -> gate m c
| Or : (a:nat{a<c}) -> (b:nat{b<c}) -> gate m c
| Not : (a:nat{a<c}) -> gate m c

type circuit (m p:nat) = (i:nat{i<p}) -> gate m i

noeq type bar =
{ xN : foo bool
; ones_: xN.t
; zeros_: xN.t
; and_: xN.t -> xN.t -> xN.t
; xor_: xN.t -> xN.t -> xN.t
; or_: xN.t -> xN.t -> xN.t
; not_: xN.t -> xN.t
; ones_spec: i:nat{i<xN.n} -> Lemma ((_).v ones_ i == true)
; zeros_spec: i:nat{i<xN.n} -> Lemma ((_).v zeros_ i == false)
; and_spec: x:xN.t -> y:xN.t -> i:nat{i<xN.n} -> Lemma ((_).v (and_ x y) i == ((_).v x i && (_).v y i))
; xor_spec: x:xN.t -> y:xN.t -> i:nat{i<xN.n} -> Lemma ((_).v (xor_ x y) i == ((_).v x i ^ (_).v y i))
; or_spec: x:xN.t -> y:xN.t -> i:nat{i<xN.n} -> Lemma ((_).v (or_ x y) i == ((_).v x i || (_).v y i))
; not_spec: x:xN.t -> i:nat{i<xN.n} -> Lemma ((_).v (not_ x) i == not((_).v x i))
}

let l1 : bar =
{ xN = x1 bool
; ones_ = true
; zeros_ = false
; and_ = (fun x y -> x && y)
; xor_ = (fun x y -> x <> y)
; or_ = (fun x y -> x || y)
; not_ = (fun x -> not x)
; ones_spec = (fun 0 -> ())
; zeros_spec = (fun 0 -> ())
; and_spec = (fun x y 0 -> ())
; xor_spec = (fun x y 0 -> ())
; or_spec = (fun x y 0 -> ())
; not_spec = (fun x 0 -> ())
}

let l1xM_def (m:nat) : Lemma (xNxM l1.xN m == x1xM bool m) [SMTPat (xNxM l1.xN m)] = ()

val circuit_def (#m #m':nat) (circ:circuit m m') (#lN:bar) (x:xNxM lN.xN m) (i:nat{i<m'}) : lN.xN.t
#push-options "--ifuel 1"
let rec circuit_def circ #lN x i =
  match circ i with
  | Input j -> index #bool #lN.xN x j
  | Zeros -> lN.zeros_
  | Ones -> lN.ones_
  | And a b -> lN.and_ (circuit_def circ x a) (circuit_def circ x b)
  | Or a b -> lN.or_ (circuit_def circ x a) (circuit_def circ x b)
  | Xor a b -> lN.xor_ (circuit_def circ x a) (circuit_def circ x b)
  | Not a -> lN.not_ (circuit_def circ x a)
#pop-options

val circuit_def_lemma (#m #m':nat) (circ:circuit m m') (#lN:bar) (x:xNxM lN.xN m) (i:nat{i<m'-1}) :
  Lemma (circuit_def #_ #(m'-1) circ x i == circuit_def #_ #m' circ x i)
  [SMTPat (circuit_def #m #m' circ x i)]
#push-options "--fuel 1 --ifuel 1"
let rec circuit_def_lemma circ x i =
  match circ i with
  | Input j -> ()
  | Ones -> ()
  | Zeros -> ()
  | Xor a b -> circuit_def_lemma circ x a; circuit_def_lemma circ x b
  | And a b -> circuit_def_lemma circ x a; circuit_def_lemma circ x b
  | Or a b -> circuit_def_lemma circ x a; circuit_def_lemma circ x b
  | Not a -> circuit_def_lemma circ x a
#pop-options

val lN_mk_def (lN:bar) (f:(i:nat{i<lN.xN.n} -> bool)) (i:nat{i<lN.xN.n}) :
  Lemma (lN.xN.v ((_).mk f) i == f i)
  [SMTPat (lN.xN.v ((_).mk f) i)]
let lN_mk_def lN f i = lN.xN.mk_def f i

val lN_ones_spec (lN:bar) (i:nat{i<lN.xN.n}) :
  Lemma ((_).v lN.ones_ i == true)
  [SMTPat ((_).v lN.ones_ i)]
let lN_ones_spec lN i = lN.ones_spec i

val lN_zeros_spec (lN:bar) (i:nat{i<lN.xN.n}) :
  Lemma ((_).v lN.zeros_ i == false)
  [SMTPat ((_).v lN.zeros_ i)]
let lN_zeros_spec lN i = lN.zeros_spec i

val lN_and_spec (lN:bar) (x y:lN.xN.t) (i:nat{i<lN.xN.n}) :
  Lemma ((_).v (lN.and_ x y) i == ((_).v x i && (_).v y i))
  [SMTPat ((_).v (lN.and_ x y) i)]
let lN_and_spec lN x y i = lN.and_spec x y i

val lN_or_spec (lN:bar) (x y:lN.xN.t) (i:nat{i<lN.xN.n}) :
  Lemma ((_).v (lN.or_ x y) i == ((_).v x i || (_).v y i))
  [SMTPat ((_).v (lN.or_ x y) i)]
let lN_or_spec lN x y i = lN.or_spec x y i

val lN_xor_spec (lN:bar) (x y:lN.xN.t) (i:nat{i<lN.xN.n}) :
  Lemma ((_).v (lN.xor_ x y) i == ((_).v x i <> (_).v y i))
  [SMTPat ((_).v (lN.xor_ x y) i)]
let lN_xor_spec lN x y i = lN.xor_spec x y i

val lN_not_spec (lN:bar) (x:lN.xN.t) (i:nat{i<lN.xN.n}) :
  Lemma ((_).v (lN.not_ x) i == not((_).v x i))
  [SMTPat ((_).v (lN.not_ x) i)]
let lN_not_spec lN x i = lN.not_spec x i

private val sliceable_circuit_lemma
  (#m #m':nat)
  (circ:circuit m m')
  (#lN:bar)
  (x:xNxM lN.xN m)
  (i:nat{i<m'})
  (j:nat{j<lN.xN.n})
  : Lemma ( (_).v (circuit_def circ x i) j == (x1 bool).v (circuit_def circ #l1 (column j x) i) 0 )
#push-options "--fuel 1 --ifuel 1"
let rec sliceable_circuit_lemma circ x i j = match circ i with
  | Ones -> ()
  | Zeros -> ()
  | Input _ -> ()
  | Xor a b -> sliceable_circuit_lemma circ x a j; sliceable_circuit_lemma circ x b j
  | And a b -> sliceable_circuit_lemma circ x a j; sliceable_circuit_lemma circ x b j
  | Or a b -> sliceable_circuit_lemma circ x a j; sliceable_circuit_lemma circ x b j
  | Not a -> sliceable_circuit_lemma circ x a j
#pop-options

val circuit_spec (#m #m':nat) (circ:circuit m m') (lN:bar) (x:xNxM lN.xN m) : xNxM lN.xN m'
let circuit_spec circ _ x = xNxM_mk _ _ (circuit_def circ x)

val circuit_spec_lemma (#m #m':nat) (circ:circuit m m') (lN:bar) (x:xNxM lN.xN m) (i:nat{i<m'}) :
  Lemma (index (circuit_spec circ lN x) i == circuit_def circ x i)
  [SMTPat (index (circuit_spec circ lN x) i)]
let circuit_spec_lemma circ x lN i = ()

val circuit_spec' (#m #m':nat) (circ:circuit m m') (lN:bar) (x:xNxM lN.xN m) : (y:xNxM lN.xN m'{y == circuit_spec circ lN x})
#push-options "--fuel 1 --ifuel 1"
let rec circuit_spec' #m #m' circ lN x =
  if m' = 0 then
    ()
  else (
    let _ : (i:nat{i<m'}) = m'-1 in
    let y : xNxM lN.xN (m'-1) = circuit_spec' #_ #(m'-1) circ lN x in
    let w : (w:lN.xN.t{w == circuit_def circ x (m'-1)}) =
      match circ (m'-1) with
      | Input j -> index x j
      | Ones -> (_).ones_
      | Zeros -> (_).zeros_
      | Xor a b -> (_).xor_ (index y a) (index y b)
      | And a b -> (_).and_ (index y a) (index y b)
      | Or a b -> (_).or_ (index y a) (index y b)
      | Not a -> (_).not_ (index y a)
    in
    let z : xNxM lN.xN m' = ((w <: lN.xN.t), y) in
    xNxM_eq_intro z (circuit_spec circ lN x);
    z
  )
#pop-options

val sliceable_circuit (#m #m':nat) (circ:circuit m m') (lN:bar) :
  Lemma (sliceable (circuit_spec circ lN) (circuit_spec circ l1))
  [SMTPat (sliceable (circuit_spec circ lN) (circuit_spec circ l1))]
let sliceable_circuit circ lN =
  sliceable_intro (circuit_spec circ lN) (circuit_spec circ l1) (fun x j ->
    xNxM_eq_intro (FStar.Classical.forall_intro (fun i -> sliceable_circuit_lemma circ x i j);
    circuit_spec circ l1 (column j x)) (column j (circuit_spec circ lN x))
  )
