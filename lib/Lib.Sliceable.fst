module Lib.Sliceable

open FStar.UInt
//open FStar.Tactics

#set-options "--fuel 0 --ifuel 0 --z3rlimit 0"

(*** Helper functions ***)

let (^) (a b:bool) : bool = (a && (not b)) || ((not a) && b)

private val offset (#a:Type) (#m:nat) (f:(i:nat{i<m}) -> a) (off:nat) (i:nat{i<m-off}) : a
let offset f off i = f (i+off)

(*** xN and xNxM ***)

noeq type foo (a:Type0) =
{ n:nat
; t:Type0
; v: t -> (i:nat{i<n}) -> a
; mk: (i:nat{i<n} -> a) -> t
; mk_def: f:(i:nat{i<n} -> a) -> i:nat{i<n} -> Lemma (v (mk f) i == f i)
}

val xN_mk_def (#a:Type0) (xN:foo a) (f:(i:nat{i<xN.n} -> a)) (i:nat{i<xN.n}) :
  Lemma (xN.v (xN.mk f) i == f i)
  [SMTPat (xN.v (xN.mk f) i)]
let xN_mk_def xN f i = xN.mk_def f i

val xNxM (#a:Type0) (xN:foo a) (m:nat) : Type0
#push-options "--fuel 1 --ifuel 1"
let rec xNxM xN m = if m = 0 then unit else xN.t * xNxM xN (m-1)
#pop-options

noextract
val index (#a:Type0) (#xN:foo a) (#m:nat) (i:nat{i<m}) (x:xNxM xN m) : xN.t
#push-options "--ifuel 1 --fuel 1"
let rec index #n #xN #m i x =
if m = 0 then
  ()
else
  let (u, v) : xN.t * xNxM xN (m-1) = x in
  if i = m-1 then
    u
  else
    index i v
#pop-options

val xNxM_mk (#a:Type0) (xN:foo a) (m:nat) (f:(i:nat{i<m} -> xN.t)) : xNxM xN m
#push-options "--fuel 1"
let rec xNxM_mk xN m f =
  if m = 0 then () else (f (m-1), xNxM_mk xN (m-1) f)
#pop-options

val xNxM_mk_def (#a:Type0) (xN:foo a) (m:nat) (f:(i:nat{i<m} -> xN.t)) (i:nat{i<m}) :
  Lemma (index i (xNxM_mk xN m f) == f i)
  [SMTPat (index i (xNxM_mk xN m f))]
#push-options "--fuel 1"
let rec xNxM_mk_def xN m f i =
  if m = 0 then
    ()
  else if i = m-1 then
    ()
  else
    xNxM_mk_def xN (m-1) f i
#pop-options

val xNxM_empty (#a:Type0) (xN:foo a) : xNxM xN 0
let xNxM_empty xN = xNxM_mk _ _ (fun _ -> ())

val xNxM_eq_intro (#a:Type0) (#xN:foo a) (#m:nat) (x y:xNxM xN m) :
  Lemma
    (requires forall (i:nat{i<m}). index i x == index i y)
    (ensures x == y)
#push-options "--fuel 1"
let rec xNxM_eq_intro #n #xN #m x y =
  if m = 0 then
    ()
  else
    let (a, u) : xN.t * xNxM xN (m-1) = x in
    let (b, v) : xN.t * xNxM xN (m-1) = y in
    assert (forall (i:nat{i<m-1}). index i u == index i x);
    xNxM_eq_intro u v;
    //assert (index x (m-1) == a);
    assert (index (m-1) y == b)
#pop-options

(*** x1 and x1xM ***)

let x1 (a:Type0) : (xN:foo a{xN.n==1}) =
{ n = 1
; t = a
; v = (fun x 0 -> x)
; mk = (fun f -> f 0)
; mk_def = (fun f i -> ())
}

val x1_of (#a:Type0) (x:a) : (x1 a).t
let x1_of #a x = (x1 a).mk (fun 0 -> x)

val x1_of_def (#a:Type0) (x:a) : Lemma ((x1 a).v (x1_of x) 0 == x) [SMTPat ((x1 a).v (x1_of x) 0)]
let x1_of_def x = ()

let x1xM (a:Type0) (m:nat) : Type0 = xNxM (x1 a) m

val x1xM_eq (#a:eqtype) (#m:nat) (u v:x1xM a m) : bool
#push-options "--fuel 1 --ifuel 1"
let rec x1xM_eq #a #m x y =
  if m = 0 then
    true
  else
    let (u0, u1) = x <: (x1 a).t * x1xM a (m-1) in
    let (v0, v1) = y <: (x1 a).t * x1xM a (m-1) in
    (u0 = v0) && x1xM_eq u1 v1
#pop-options

val x1xM_eq_lemma (#a:eqtype) (#m:nat) (u v:x1xM a m) : Lemma (requires x1xM_eq u v) (ensures u == v)
#push-options "--fuel 1 --ifuel 1"
let rec x1xM_eq_lemma #a #m u v =
  if m = 0 then
    ()
  else
    let (u0, u1) = u <: (x1 a).t * x1xM a (m-1) in
    let (v0, v1) = v <: (x1 a).t * x1xM a (m-1) in
    x1xM_eq_lemma u1 v1
#pop-options

val x1xM_mk (#a:Type0) (m:nat) (f:(i:nat{i<m} -> a)) : x1xM a m
let x1xM_mk m f = xNxM_mk _ _ (fun i -> x1_of (f i))

noextract
val column (#a:Type0) (#xN:foo a) (#m:nat) (j:nat{j<xN.n}) (x:xNxM xN m) : x1xM a m
let column j x =
  let aux1 i k = (_).v (index i x) j in
  let aux2 i = (_).mk (aux1 i) in
  xNxM_mk _ _ aux2

val column_def (#a:Type0) (#xN:foo a) (#m:nat) (j:nat{j<xN.n}) (x:xNxM xN m) (i:nat{i<m}) :
  Lemma ((_).v (index i (column j x)) 0 == (_).v (index i x) j)
  [SMTPat ((_).v (index i (column j x)) 0)]
let column_def j x i = ()

val column_lemma (#a:Type0) (#xN:foo a) (#m:nat) (x:xNxM xN m) (i:nat{i<m}) (j:nat{j<xN.n}) :
  Lemma ( (x1 a).v (index i (column j x)) 0 == xN.v (index i x) j )
  [SMTPat ((x1 a).v (index i (column j x)) 0)]
let column_lemma x i j = ()

val column_column (#a:Type0) (#m:nat) (x:x1xM a m) :
  Lemma (column 0 x == x)
  [SMTPat (column 0 x)]
let column_column x = xNxM_eq_intro (column 0 x) x

(*** Sliceability ***)

val sliceable (#a:Type0) (#xN:foo a) (#m #m':nat) (f:(xNxM xN m -> xNxM xN m')) (g:(x1xM a m -> x1xM a m')) : Type0
let sliceable #a #xN #m #m' f g =
  forall (x:xNxM xN m) (j:nat{j<xN.n}).
  (column j (f x) == g (column j x))

val sliceable_intro
  (#a:Type0) (#xN:foo a)
  (#m #m':nat)
  (f:(xNxM xN m -> xNxM xN m'))
  (g:(x1xM a m -> x1xM a m'))
  (pr:(x:xNxM xN m -> j:nat{j<xN.n} -> Lemma (column j (f x) == g (column j x))))
  : Lemma (sliceable f g)
let sliceable_intro #a #xN #m #m' f g pr = FStar.Classical.forall_intro_2 pr

val sliceable_def
  (#a:Type0) (#xN:foo a)
  (#m #m':nat)
  (f:(xNxM xN m -> xNxM xN m'))
  (g:(x1xM a m -> x1xM a m'))
  : Lemma (requires sliceable f g) (ensures (forall (x:xNxM xN m) (j:nat{j<xN.n}). column j (f x) == g (column j x)))
    [SMTPat (sliceable f g)]
let sliceable_def f g = ()

val sliceable_feq
  (#a:Type0) (#xN:foo a)
  (#m #m':nat)
  (f:(xNxM xN m -> xNxM xN m'))
  (g:(x1xM a m -> x1xM a m'){sliceable f g})
  (h:(xNxM xN m -> xNxM xN m'))
  : Lemma
    (requires forall (x:xNxM xN m). f x == h x)
    (ensures sliceable h g)
let sliceable_feq f g h = ()

noextract
val reduce_output
  (#a:Type0) (#xN:foo a)
  (#m #m':nat)
  (f:(xNxM xN m -> xNxM xN m'))
  (m'':nat) (r:(i:nat{i<m''} -> j:nat{j<m'}))
  : xNxM xN m -> xNxM xN m''
let reduce_output f m'' r x = xNxM_mk _ _ (fun i -> index (r i) (f x))

val reduce_output_def
  (#a:Type0) (#xN:foo a)
  (#m #m':nat)
  (f:( xNxM xN m -> xNxM xN m'))
  (m'':nat) (r:(i:nat{i<m''} -> j:nat{j<m'}))
  (x:xNxM xN m) (i:nat{i<m''})
  : Lemma (index i (reduce_output f m'' r x) == index (r i) (f x))
  [SMTPat (index i (reduce_output f m'' r x))]
let reduce_output_def f m'' r x i = ()

val reduce_output_sliceable
  (#a:Type0) (#xN:foo a)
  (#m #m':nat)
  (f:(xNxM xN m -> xNxM xN m'))
  (g:(x1xM a m -> x1xM a m'){sliceable f g})
  (m'':nat{m''<=m'}) (r:(i:nat{i<m''} -> j:nat{j<m'}))
  : Lemma (sliceable (reduce_output f m'' r) (reduce_output g m'' r))
  [SMTPat (sliceable (reduce_output f m'' r) (reduce_output g m'' r))]
let reduce_output_sliceable f g m'' r =
  sliceable_intro (reduce_output f m'' r) (reduce_output g m'' r)
    (fun x j -> xNxM_eq_intro (reduce_output g m'' r (column j x)) (column j (reduce_output f m'' r x)))

(*** of_uint and to_uint ***)

module UI = FStar.UInt
module S = FStar.Seq

noextract
val to_uint_spec (#m:nat) (x:x1xM bool m) : uint_t m
let to_uint_spec #m x = UI.from_vec (S.init m (fun i -> index i x))

noextract
val of_uint_spec (#m:nat) (p:uint_t m) : x1xM bool m
#push-options "--fuel 1"
let of_uint_spec #m p =
  if m = 0 then
    ()
  else
    x1xM_mk _ (UI.nth p)
#pop-options

noextract
val to_uint (#m:nat) (x:x1xM bool m) : (p:uint_t m{p == to_uint_spec x})
let to_uint #m x =
  normalize_term(
    let rec aux (j:nat{j<=m})
      : (p:uint_t j{p == UI.from_vec (S.init j (fun i -> index i x))})
      =
      if j = 0 then
        0
      else (
        let r = Prims.op_Multiply 2 (aux (j-1)) + (if index (j-1) x then 1 else 0) in
        assume (r <= pow2 j - 1);
        let r : uint_t j = r in
        let v = S.init j (fun i -> index i x) in
        assume (r == UI.from_vec (S.init j (fun i -> index i x)));
        r
      )
    in
    aux m
  )

noextract
val of_uint (#m:nat) (p:uint_t m) : (x:x1xM bool m{x == of_uint_spec p})
let of_uint #m p =
  normalize_term(
    let aux (q:uint_t m) (i:nat{i<m}) : (r:bool{r == UI.nth p i}) =
      admit ();
      q / (pow2 i) % 2 = 1
    in
    let x = x1xM_mk _ (aux p) in
    xNxM_eq_intro x (of_uint_spec p);
    x
  )

val to_uint_of_uint (#m:nat) (p:uint_t m) :
  Lemma (to_uint (of_uint p) == p)
  [SMTPat (to_uint (of_uint p))]
let to_uint_of_uint #m p =
  if m = 0 then
    ()
  else
    UI.nth_lemma (to_uint (of_uint p)) p

val of_uint_to_uint (#m:nat) (x:x1xM bool m) :
  Lemma (of_uint (to_uint x) == x)
  [SMTPat (of_uint (to_uint x))]
let of_uint_to_uint x = xNxM_eq_intro (of_uint (to_uint x)) x

(*** Bruteforce lemmas and tactics ***)

val forall_uint_lemma (#m:nat) (phi:x1xM bool m -> Type0) :
  Lemma
    (requires forall (i:uint_t m). phi (of_uint i))
    (ensures forall x. phi x)
let forall_uint_lemma phi =
  FStar.Classical.forall_intro (fun x -> of_uint_to_uint x <: Lemma (phi x))

let rec bruteforce_aux_aux (n:nat) (phi:(i:nat{i<n} -> bool)) :
  Pure
    bool
    (requires True)
    (ensures fun r -> if r then forall (i:nat{i<n}). phi i else True)
  = if n = 0 then true else phi (n-1) && bruteforce_aux_aux (n-1) phi

let bruteforce_aux (n:nat) (phi:(i:uint_t n -> bool)) :
  Pure
    bool
    (requires True)
    (fun r -> if r then forall (i:uint_t n). phi i else True)
  =
  bruteforce_aux_aux (pow2 n) phi

#push-options "--fuel 1 --ifuel 1"
noextract
let bruteforce
  (#xN:foo bool)
  (#m #m':nat)
  (impl_n:(xNxM xN m -> xNxM xN m'))
  (impl_1:(x1xM bool m -> x1xM bool m'))
  (spec:(uint_t m -> uint_t m'))
  : Pure
    bool
    (requires sliceable impl_n impl_1)
    (ensures fun r ->
      if r then
        forall (x:xNxM xN m) (j:nat{j<xN.n}).
        column j (impl_n x) == of_uint (spec (to_uint (column j x)))
      else
        True
    )
  =
  let phi0 (x:x1xM bool m) : Type0 = impl_1 x == of_uint (spec (to_uint x)) in
  let phi1 (i:uint_t m) : bool = x1xM_eq (impl_1 (of_uint i)) (of_uint (spec i)) in
  let r = bruteforce_aux m phi1 in
  if r then (
    FStar.Classical.forall_intro (fun (i:uint_t m) ->
      x1xM_eq_lemma (impl_1 (of_uint i)) (of_uint (spec i))
      <: Lemma (impl_1 (of_uint i) == of_uint (spec i))
    );
    forall_uint_lemma phi0
  ) else ();
  r
#pop-options

open FStar.Tactics

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

noextract
val bruteforce_nat (n:nat) (tac:unit -> Tac unit) : Tac unit
let bruteforce_nat n tac =
  let _ = repeatn n (fun _ -> apply_lemma (`nat_ind); tac ()) in
  apply_lemma (`nat_less_zero)

noextract
val bruteforce_bool (n:nat) (tac:unit -> Tac unit) : Tac unit
let bruteforce_bool n tac =
  let _ = repeatn n (fun _ -> iterAll (fun _ -> apply_lemma (`bool_ind))) in
  iterAll tac
