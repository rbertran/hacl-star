module Lib.Sliceable

open FStar.Tactics
open FStar.UInt
//open FStar.FunctionalExtensionality

#set-options "--fuel 0 --ifuel 0"

(*** xN and xNxM ***)

let (^) (a b:bool) : bool = (a && (not b)) || ((not a) && b)

noeq type sig (n:nat) : Type =
{ t: Type
; v: t -> (i:nat{i<n}) -> bool
; mk: (i:nat{i<n} -> bool) -> t
; mk_def: f:(i:nat{i<n} -> bool) -> i:nat{i<n} -> Lemma (v (mk f) i == f i)
; ones_: t
; zeros_: t
; and_: t -> t -> t
; xor_: t -> t -> t
; or_: t -> t -> t
; not_: t -> t
; ones_spec: i:nat{i<n} -> Lemma (v ones_ i == true)
; zeros_spec: i:nat{i<n} -> Lemma (v zeros_ i == false)
; and_spec: x:t -> y:t -> i:nat{i<n} -> Lemma (v (and_ x y) i == (v x i && v y i))
; xor_spec: x:t -> y:t -> i:nat{i<n} -> Lemma (v (xor_ x y) i == (v x i ^ v y i))
; or_spec: x:t -> y:t -> i:nat{i<n} -> Lemma (v (or_ x y) i == (v x i || v y i))
; not_spec: x:t -> i:nat{i<n} -> Lemma (v (not_ x) i == not(v x i))
}

let ( &&& ) (#n:nat) (#xN:sig n) (x y:xN.t) : xN.t = xN.and_ x y
let ( ^^^ ) (#n:nat) (#xN:sig n) (x y:xN.t) : xN.t = xN.xor_ x y
let ( ||| ) (#n:nat) (#xN:sig n) (x y:xN.t) : xN.t = xN.or_ x y
let ( ~~~ ) (#n:nat) (#xN:sig n) (x:xN.t) : xN.t = xN.not_ x
let ones (#n:nat) (xN:sig n) : xN.t = xN.ones_
let zeros (#n:nat) (xN:sig n) : xN.t = xN.zeros_

let op_String_Access (#n:nat) (#xN:sig n) (x:xN.t) (i:nat{i<n}) : bool = xN.v x i

let xN_mk_def (#n:nat) (#xN:sig n) (f:(i:nat{i<n} -> bool)) (i:nat{i<n}) :
  Lemma ((xN.mk f).[i] == f i)
  [SMTPat (xN.mk f).[i]]
  = xN.mk_def f i

let xN_ones_spec (#n:nat) (#xN:sig n) (i:nat{i<n}) :
  Lemma ((ones xN).[i] == true)
  [SMTPat (ones xN).[i]]
  = xN.ones_spec i

let xN_zeros_spec (#n:nat) (#xN:sig n) (i:nat{i<n}) :
  Lemma ((zeros xN).[i] == false)
  [SMTPat (zeros xN).[i]]
  = xN.zeros_spec i

let xN_and_spec (#n:nat) (#xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma ((x &&& y).[i] == (x.[i] && y.[i]))
  [SMTPat (x &&& y).[i]]
  = xN.and_spec x y i

let xN_xor_spec (#n:nat) (#xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma ((x ^^^ y).[i] == (x.[i] ^ y.[i]))
  [SMTPat (x ^^^ y).[i]]
  = xN.xor_spec x y i

let xN_or_spec (#n:nat) (#xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma ((x ||| y).[i] == (x.[i] || y.[i]))
  [SMTPat (x ||| y).[i]]
  = xN.or_spec x y i

let xN_not_spec (#n:nat) (#xN:sig n) (x:xN.t) (i:nat{i<n}) :
  Lemma ((~~~ x).[i] == not x.[i])
  [SMTPat (~~~x).[i]]
  = xN.not_spec x i

//TODO: declaring type of xNxM before definition doesn't work
let rec xNxM (#n:nat) (xN:sig n) (m:nat) : Type = if m = 0 then unit else xN.t * xNxM xN (m-1)

val index (#n:nat) (#xN:sig n) (#m:nat) (x:xNxM xN m) (i:nat{i<m}) : xN.t
#push-options "--fuel 1"
let rec index #n #xN #m x i =
if m = 0 then
  ()
else
  let (u, v) : xN.t * xNxM xN (m-1) = x in
  if i = 0 then
    u
  else
    index v (i-1)
#pop-options

private val offset (#a:Type) (#m:nat) (f:(i:nat{i<m}) -> a) (off:nat) (i:nat{i<m-off}) : a
let offset f off i = f (i+off)

val xNxM_mk (#n:nat) (xN:sig n) (m:nat) (f:(i:nat{i<m} -> xN.t)) : xNxM xN m
#push-options "--fuel 1"
let rec xNxM_mk xN m f =
  if m = 0 then () else (f 0, xNxM_mk xN (m-1) (offset #_ #m f 1))
#pop-options


val xNxM_mk_def (#n:nat) (xN:sig n) (m:nat) (f:(i:nat{i<m} -> xN.t)) (i:nat{i<m}) :
  Lemma (index (xNxM_mk xN m f) i == f i)
  [SMTPat (index (xNxM_mk xN m f) i)]
#push-options "--fuel 1"
let rec xNxM_mk_def xN m f i =
  if i = 0 then
    ()
  else
    xNxM_mk_def xN (m-1) (offset #_ #m f 1) (i-1)
#pop-options

val xNxM_eq_intro (#n:nat) (#xN:sig n) (#m:nat) (x y:xNxM xN m) :
  Lemma
    (requires forall (i:nat{i<m}). index x i == index y i)
    (ensures x == y)
#push-options "--fuel 1"
let rec xNxM_eq_intro #n #xN #m x y =
  if m = 0 then
    ()
  else
    let (a, u) : xN.t * xNxM xN (m-1) = x in
    let (b, v) : xN.t * xNxM xN (m-1) = y in
    assert (forall (i:nat{i<m-1}). index u i == index x (i+1));
    xNxM_eq_intro u v;
    //assert (index x 0 == a);
    assert (index y 0 == b)
#pop-options

(*** u1 and u1xM ***)

let u1 : sig 1 =
{ t = bool
; v = (fun x 0 -> x)
; mk = (fun f -> f 0)
; mk_def = (fun f i -> ())
; ones_ = true
; zeros_ = false
; and_ = (fun x y -> x && y)
; xor_ = (fun x y -> x ^ y)
; or_ = (fun x y -> x || y)
; not_ = (fun x -> not x)
; ones_spec = (fun i -> ())
; zeros_spec = (fun i -> ())
; and_spec = (fun x y i -> ())
; xor_spec = (fun x y i -> ())
; or_spec = (fun x y i -> ())
; not_spec = (fun x i -> ())
}

val u1_of_bool (b:bool) : u1.t
let u1_of_bool b = u1.mk (fun 0 -> b)

val u1_of_bool_def (b:bool) : Lemma ((u1_of_bool b).[0] == b) [SMTPat (u1_of_bool b).[0]]
let u1_of_bool_def b = ()

// TODO
let u1xM (m:nat) : Type = xNxM u1 m

val u1xM_mk (m:nat) (f:(i:nat{i<m} -> bool)) : u1xM m
let u1xM_mk m f = xNxM_mk _ _ (fun i -> u1_of_bool (f i))

val column (#n:nat) (#xN:sig n) (#m:nat) (j:nat{j<n}) (x:xNxM xN m) : u1xM m
let column j x =
  let aux1 i k : bool = (index x i).[j] in
  let aux2 i : u1.t = u1.mk (aux1 i) in
  xNxM_mk u1 _ aux2

val column_lemma (#n:nat) (#xN:sig n) (#m:nat) (x:xNxM xN m) (i:nat{i<m}) (j:nat{j<n}) :
  Lemma ( (index (column j x) i).[0] == (index x i).[j] )
  [SMTPat (index (column j x) i).[0]]
let column_lemma x i j = ()

val column_column (#m:nat) (x:u1xM m) :
  Lemma (column 0 x == x)
  [SMTPat (column 0 x)]
let column_column x = xNxM_eq_intro (column 0 x) x

(*** Sliceability ***)

//TODO: broken
//val sliceable (#m #m':nat) (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m')) : Type0
//let sliceable #m #m' f =
let sliceable (#m #m':nat) (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m')) : Type0 =
  forall (n:nat) (xN:sig n) (x:xNxM xN m) (j:nat{j<n}).
  ( column j (f x) == f (column j x))

val sliceable_intro
  (#m #m':nat)
  (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  (pr:(#n:nat -> #xN:sig n -> x:xNxM xN m -> j:nat{j<n} -> Lemma (column j (f x) == f (column j x))))
  : Lemma (sliceable f)
let sliceable_intro f pr =
  FStar.Classical.forall_intro_2 (fun (n:nat) (xN:sig n) ->
    FStar.Classical.forall_intro_2 (fun (x:xNxM xN _) (j:nat{j<n}) ->
      pr x j
    )
  )

val sliceable_elim
  (#m #m':nat)
  (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable f})
  (#n:nat) (#xN:sig n) (x:xNxM xN m)
  (j:nat{j<n})
  : Lemma ( column j (f x) == f (column j x) )
let sliceable_elim f x j = ()

val sliceable_comp
  (#m1 #m2 #m3:nat)
  (f1:(#n:nat -> #xN:sig n -> xNxM xN m1 -> xNxM xN m2))
  (f2:(#n:nat -> #xN:sig n -> xNxM xN m2 -> xNxM xN m3))
  : Lemma
    (requires sliceable f1 /\ sliceable f2)
    (ensures sliceable (fun x -> f2 (f1 x)))
let sliceable_comp f1 f2 = ()

val sliceable_feq
  (#m #m':nat)
  (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable f})
  (g:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  : Lemma
    (requires forall (n:nat) (xN:sig n) (x:xNxM xN m). f x == g x)
    (ensures sliceable g)
let sliceable_feq f g = ()

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

val circuit_def (#m #m':nat) (circ:circuit m m') (#n:nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m'}) : xN.t
#push-options "--ifuel 1"
let rec circuit_def circ x i =
  match circ i with
  | Input j -> index x j
  | Ones -> ones _
  | Zeros -> zeros _
  | Xor a b -> circuit_def circ x a ^^^ circuit_def circ x b
  | And a b -> circuit_def circ x a &&& circuit_def circ x b
  | Or a b -> circuit_def circ x a ||| circuit_def circ x b
  | Not a -> ~~~(circuit_def circ x a)
#pop-options

[@"opaqe_to_smt"]
noeq
type foo
  (#m #m':nat) (circ:circuit m m')
  (#n:nat) (#xN:sig n) (x:xNxM xN m)
  (i:nat{i<m'}) =
  | Foo : (u:xN.t{u == circuit_def circ x i}) -> foo circ x i

[@"opaque_to_smt"]
val circuit_input
  (#m #m':nat) (#circ:circuit m m')
  (#n:nat) (#xN:sig n) (#x:xNxM xN m)
  (#c:nat{c<m'})
  (j:nat{j<m})
  : Pure (foo circ x c) (requires circ c == Input j) (ensures fun _ -> True)

[@"opaque_to_smt"]
val circuit_ones
  (#m #m':nat) (#circ:circuit m m')
  (#n:nat) (#xN:sig n) (#x:xNxM xN m)
  (#c:nat{c<m'})
  : Pure (foo circ x c) (requires circ c == Ones) (ensures fun _ -> True)

[@"opaque_to_smt"]
val circuit_zeros
  (#m #m':nat) (#circ:circuit m m')
  (#n:nat) (#xN:sig n) (#x:xNxM xN m)
  (#c:nat{c<m'})
  : Pure (foo circ x c) (requires circ c == Zeros) (ensures fun _ -> True)

[@"opaque_to_smt"]
val circuit_and
  (#m #m':nat) (#circ:circuit m m')
  (#n:nat) (#xN:sig n) (#x:xNxM xN m)
  (#c:nat{c<m'})
  (#a:nat{a<c}) (u:foo circ x a)
  (#b:nat{b<c}) (v:foo circ x b)
  : Pure (foo circ x c) (requires circ c == And a b) (ensures fun _ -> True)

[@"opaque_to_smt"]
val circuit_xor
  (#m #m':nat) (#circ:circuit m m')
  (#n:nat) (#xN:sig n) (#x:xNxM xN m)
  (#c:nat{c<m'})
  (#a:nat{a<c}) (u:foo circ x a)
  (#b:nat{b<c}) (v:foo circ x b)
  : Pure (foo circ x c) (requires circ c == Xor a b) (ensures fun _ -> True)

[@"opaque_to_smt"]
val circuit_or
  (#m #m':nat) (#circ:circuit m m')
  (#n:nat) (#xN:sig n) (#x:xNxM xN m)
  (#c:nat{c<m'})
  (#a:nat{a<c}) (u:foo circ x a)
  (#b:nat{b<c}) (v:foo circ x b)
  : Pure (foo circ x c) (requires circ c == Or a b) (ensures fun _ -> True)

[@"opaque_to_smt"]
val circuit_not
  (#m #m':nat) (#circ:circuit m m')
  (#n:nat) (#xN:sig n) (#x:xNxM xN m)
  (#c:nat{c<m'})
  (#a:nat{a<c}) (u:foo circ x a)
  : Pure (foo circ x c) (requires circ c == Not a) (ensures fun _ -> True)

#push-options "--fuel 1"
let circuit_input #_ #_ #_ #_ #_ #x #_ j = Foo (index x j)
let circuit_ones #_ #_ #_ #_ #_ #_ #_ = Foo (ones _)
let circuit_zeros #_ #_ #_ #_ #_ #_ #_ = Foo (zeros _)
let circuit_and u v = Foo (Foo?.u u &&& Foo?.u v)
let circuit_xor u v = Foo (Foo?.u u ^^^ Foo?.u v)
let circuit_or u v = Foo (Foo?.u u ||| Foo?.u v)
let circuit_not u = Foo (~~~(Foo?.u u))
#pop-options

val circuit_spec (#m #m':nat) (circ:circuit m m') (#n:nat) (#xN:sig n) (x:xNxM xN m) : xNxM xN m'
let circuit_spec #_ #m' circ #_ #xN x = xNxM_mk xN m' (circuit_def circ x)

private val sliceable_circuit_lemma
  (#m #m':nat)
  (circ:circuit m m')
  (#n:nat)
  (#xN:sig n)
  (x:xNxM xN m)
  (i:nat{i<m'})
  (j:nat{j<n})
  : Lemma ( (circuit_def circ x i).[j] == (circuit_def circ (column j x) i).[0] )
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

val sliceable_circuit (#m #m':nat) (circ:circuit m m') :
  Lemma (sliceable (circuit_spec circ))
  [SMTPat (sliceable (circuit_spec circ))]
let sliceable_circuit circ =
  sliceable_intro (circuit_spec circ) (fun x j ->
    xNxM_eq_intro (FStar.Classical.forall_intro (fun i -> sliceable_circuit_lemma circ x i j);
    circuit_spec circ (column j x)) (column j (circuit_spec circ x))
  )

(*** of_uint and to_uint ***)

val of_uint_spec (#m:nat) (p:uint_t m) : u1xM m
#push-options "--fuel 1"
let of_uint_spec #m p =
  if m = 0 then
    ()
  else
    u1xM_mk _ (FStar.UInt.nth p)
#pop-options

val to_uint_spec (#m:nat) (x:u1xM m) : uint_t m
let to_uint_spec #m x = FStar.UInt.from_vec (FStar.Seq.init m (index x))

val to_uint (#m:nat) (x:u1xM m) : (p:uint_t m{p == to_uint_spec x})
let to_uint #m x =
  let rec aux (j:nat{j<=m})
    : (p:uint_t j{p == FStar.UInt.from_vec (FStar.Seq.init j (index x))})
    =
    if j = 0 then
      0
    else (
      let r = Prims.op_Multiply 2 (aux (j-1)) + (if index x (j-1) then 1 else 0) in
      assume (r <= pow2 j - 1);
      let r : uint_t j = r in
      let v = FStar.Seq.init j (index x) in
      assume (r == FStar.UInt.from_vec (FStar.Seq.init j (index x)));
      r
    )
  in
  aux m

val of_uint (#m:nat) (p:uint_t m) : (x:u1xM m{x == of_uint_spec p})
#push-options "--fuel 1"
let of_uint #m p =
  let rec aux (j:nat{j<=m}) (q:uint_t j) : (x:u1xM j{x == of_uint_spec #j q}) =
    if j = 0 then
      ()
    else (
      let u : u1.t = q%2 = 1 in
      let v : u1xM (j-1) = aux (j-1) (q/2) in
      let x : u1xM j = (u, v) in
      assume (x == of_uint_spec #j q);
      x
    )
  in
  aux m p
#pop-options

val to_uint_of_uint (#m:nat) (p:uint_t m) :
  Lemma (to_uint (of_uint p) == p)
  [SMTPat (to_uint (of_uint p))]
let to_uint_of_uint #m p =
  if m = 0 then
    ()
  else
    FStar.UInt.nth_lemma (to_uint (of_uint p)) p

val of_uint_to_uint (#m:nat) (x:u1xM m) :
  Lemma (of_uint (to_uint x) == x)
  [SMTPat (of_uint (to_uint x))]
let of_uint_to_uint x = xNxM_eq_intro (of_uint (to_uint x)) x

(*** Bruteforce lemmas and tactics ***)

private val bruteforce_aux (n:nat) (phi:(i:nat{i<n} -> bool)) : bool
let rec bruteforce_aux n phi =
  if n = 0 then true else phi (n-1) && bruteforce_aux (n-1) phi

private val bruteforce_aux_lemma (n:nat) (phi:(i:nat{i<n} -> bool)) :
  Lemma
    (requires bruteforce_aux n phi)
    (ensures forall (i:nat{i<n}). phi i)
#push-options "--fuel 1"
let rec bruteforce_aux_lemma n phi =
  if n = 0 then () else bruteforce_aux_lemma (n-1) phi
#pop-options

val bruteforce (#n:nat) (phi:(i:uint_t n -> bool)) : bool
let bruteforce #n phi = bruteforce_aux (pow2 n) phi

val bruteforce_lemma (#n:nat) (phi:(i:uint_t n -> bool)) :
  Lemma
    (requires bruteforce phi)
    (ensures forall (i:uint_t n). phi i)
let bruteforce_lemma #n phi = bruteforce_aux_lemma (pow2 n) phi

val forall_uint_lemma (#m:nat) (phi:u1xM m -> Type0) :
  Lemma
    (requires forall (i:uint_t m). phi (of_uint i))
    (ensures forall x. phi x)
let forall_uint_lemma phi =
  FStar.Classical.forall_intro (fun x -> of_uint_to_uint x <: Lemma (phi x))

val nat_ind
  (n:pos)
  (phi:((i:nat{i<n}) -> Type))
  (_:squash (phi (n-1)))
  (_:squash (forall (i:nat{i<n-1}). phi i))
  : Lemma (forall (i:nat{i<n}). phi i)
let nat_ind n phi _ _ = ()

val bool_ind
  (phi:(bool -> Type))
  (_:squash (phi true))
  (_:squash (phi false))
  : Lemma (forall b. phi b)
let bool_ind phi _ _ = ()

val nat_less_zero (phi : (i:nat{i<0}) -> Type) : Lemma (forall i. phi i)
let nat_less_zero phi = ()

val bruteforce_nat (n:nat) (tac:unit -> Tac unit) : Tac unit
let bruteforce_nat n tac =
  let _ = repeatn n (fun _ -> apply_lemma (`nat_ind); tac ()) in
  apply_lemma (`nat_less_zero)

val bruteforce_bool (n:nat) (tac:unit -> Tac unit) : Tac unit
let bruteforce_bool n tac =
  let _ = repeatn n (fun _ -> iterAll (fun _ -> apply_lemma (`bool_ind))) in
  iterAll tac
