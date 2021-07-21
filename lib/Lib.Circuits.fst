module Lib.Circuits

#set-options "--fuel 0 --ifuel 0"

open Lib.Sliceable

(*** Circuits ***)

type gate (m p:nat) =
| Zeros : gate m p
| Ones : gate m p
| Input : i:nat{i<m} -> gate m p
| And : a:nat{a<p} -> b:nat{b<p} -> gate m p
| Xor : a:nat{a<p} -> b:nat{b<p} -> gate m p
| Or : a:nat{a<p} -> b:nat{b<p} -> gate m p
| Not : a:nat{a<p} -> gate m p

type circuit (m:nat) : nat -> Type0 =
| Empty : circuit m 0
| Cons : #p:nat -> circ:circuit m p -> g:gate m p -> circuit m (p+1)

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

noextract
val circuit_def (#m #p:nat) (circ:circuit m p) (#lN:bar) (x:xNxM lN.xN m) (i:nat{i<p}) : lN.xN.t
#push-options "--ifuel 1"
let rec circuit_def #m #p circ #lN x i =
  let Cons circ g = circ in
  if i=p-1 then
    match g with
    | Input j -> index j x
    | Zeros -> (_).zeros_
    | Ones -> (_).ones_
    | And a b -> (_).and_ (circuit_def circ x a) (circuit_def circ x b)
    | Or a b -> (_).or_ (circuit_def circ x a) (circuit_def circ x b)
    | Xor a b -> (_).xor_ (circuit_def circ x a) (circuit_def circ x b)
    | Not a -> (_).not_ (circuit_def circ x a)
  else
    circuit_def circ x i
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

private val circuit_spec1_sliceable_lemma
  (#m #p:nat)
  (circ:circuit m p)
  (#lN:bar)
  (x:xNxM lN.xN m)
  (i:nat{i<p})
  (j:nat{j<lN.xN.n})
  : Lemma ( (_).v (circuit_def circ x i) j == (x1 bool).v (circuit_def circ #l1 (column j x) i) 0 )
#push-options "--fuel 1 --ifuel 1"
let rec circuit_spec1_sliceable_lemma #m #p circ #lN x i j =
  let Cons circ g = circ in
  if i=p-1 then
    match g with
    | Ones -> ()
    | Zeros -> ()
    | Input _ -> ()
    | Xor a b -> circuit_spec1_sliceable_lemma circ x a j; circuit_spec1_sliceable_lemma circ x b j
    | And a b -> circuit_spec1_sliceable_lemma circ x a j; circuit_spec1_sliceable_lemma circ x b j
    | Or a b -> circuit_spec1_sliceable_lemma circ x a j; circuit_spec1_sliceable_lemma circ x b j
    | Not a -> circuit_spec1_sliceable_lemma circ x a j
  else
   circuit_spec1_sliceable_lemma circ x i j
#pop-options

noextract
val circuit_spec1 (#m #m':nat) (circ:circuit m m') (lN:bar) (x:xNxM lN.xN m) : xNxM lN.xN m'
let circuit_spec1 circ _ x = xNxM_mk _ _ (circuit_def circ x)

val circuit_spec1_lemma (#m #m':nat) (circ:circuit m m') (lN:bar) (x:xNxM lN.xN m) (i:nat{i<m'}) :
  Lemma (index i (circuit_spec1 circ lN x) == circuit_def circ x i)
  [SMTPat (index i (circuit_spec1 circ lN x))]
let circuit_spec1_lemma circ x lN i = ()

val circuit_spec1_sliceable (#m #m':nat) (circ:circuit m m') (lN:bar) :
  Lemma (sliceable (circuit_spec1 circ lN) (circuit_spec1 circ l1))
  [SMTPat (sliceable (circuit_spec1 circ lN) (circuit_spec1 circ l1))]
let circuit_spec1_sliceable circ lN =
  sliceable_intro (circuit_spec1 circ lN) (circuit_spec1 circ l1) (fun x j ->
    xNxM_eq_intro (FStar.Classical.forall_intro (fun i -> circuit_spec1_sliceable_lemma circ x i j);
    circuit_spec1 circ l1 (column j x)) (column j (circuit_spec1 circ lN x))
  )

type circuit_rev (m p:nat) : nat -> Type0 =
| End : circuit_rev m p 0
| Concat : #i:nat{i<p} -> circuit_rev m p i -> gate m (p-i-1) -> circuit_rev m p (i+1)

#push-options "--ifuel 1"
noextract let rev (#m #p:nat) (circ:circuit m p) : circuit_rev m p p =
  let rec aux (#i:nat{i<=p}) (circ:circuit m i) (acc:circuit_rev m p (p-i)) : circuit_rev m p p =
    match circ with
    | Empty -> acc
    | Cons circ g -> aux circ (Concat acc g)
  in
  aux circ End
#pop-options

//#push-options "--ifuel 1"
//noextract let rev' (#m #p:nat) (cric:circuit_rev m p p) : circuit m p =
//  let rec aux (#i:nat{i<=p}) (cric:circuit_rev m p i) (acc:circuit m (p-i)) : circuit m p =
//    match cric with
//    | End -> acc
//    | Concat cric g ->
//      let g : gate m (p-(i-1)-1) = g in
//      assert(p-(i-1)-1 == p-i);
//      let g : gate m ((p-i)+(1-1)) = g in
//      let g : gate m (p-i) = g in
//      aux cric (Cons acc g)
//  in
//  aux cric Empty
//#pop-options

#push-options "--ifuel 1 --fuel 1"
noextract
let rec circuit_spec2_aux (#m #p:nat) (#i:nat{i<=p}) (cric:circuit_rev m p i) (lN:bar) (x:xNxM lN.xN m) (acc:xNxM lN.xN (p-i)) :
  xNxM lN.xN p =
  match cric with
  | End -> acc
  | Concat cric g ->
    let r : lN.xN.t = match g with
    | Zeros -> (_).zeros_
    | Ones -> (_).ones_
    | Input j -> index j x
    | And a b ->
        let xa = index a acc in
        let xb = index b acc in
        (_).and_ xa xb
    | Xor a b ->
        let xa = index a acc in
        let xb = index b acc in
        (_).xor_ xa xb
    | Or a b ->
        let xa = index a acc in
        let xb = index b acc in
        (_).or_ xa xb
    | Not a ->
        let xa = index a acc in
        (_).not_ xa
    in
    circuit_spec2_aux cric lN x (r, acc)
#pop-options

noextract
//val circuit_spec2 (#m #p:nat) (circ:circuit m p) (lN:bar) (x:xNxM lN.xN m) : (y:xNxM lN.xN p{y == circuit_spec circ lN x})
val circuit_spec2 (#m #p:nat) (circ:circuit m p) (lN:bar) (x:xNxM lN.xN m) : xNxM lN.xN p
let circuit_spec2 circ lN x = circuit_spec2_aux (rev circ) lN x (xNxM_empty _)

val circuit_spec2_sliceable (#m #p:nat) (circ:circuit m p) (lN:bar) :
  Lemma (sliceable (circuit_spec2 circ lN) (circuit_spec2 circ l1))
let circuit_spec2_sliceable circ lN = admit ()

type circ_st =
{ m: nat
; p: nat
; circ: circuit m p
}
let circ_st_empty (m:nat) =
{ m = m
; p = 0
; circ = Empty
}

type st_monad (b:Type0) (a:Type0) = b -> a * b
noextract let bind (#b:Type0) (m:st_monad b 'a) (f:'a -> st_monad b 'b) : st_monad b 'b =
fun s -> let (a, s') = m s in f a s'
noextract let return (#b:Type0) (x:'a) : st_monad b 'a =
fun s -> (x,s)
noextract let put (#b:Type0) (s:b) : st_monad b unit =
fun _ -> ((),s)
noextract let get (#b:Type0) : st_monad b b =
fun s -> (s,s)
noextract let run (#b:Type0) (m:st_monad b 'a) (s:b) : 'a*b = m s

noextract let bld_aux (st:circ_st) (g:gate st.m st.p) : circ_st =
{ m = st.m
; p = st.p+1
; circ = Cons st.circ g
}

noextract let bld_zeros : st_monad circ_st nat =
  st <-- get;
  _ <-- put (bld_aux st Zeros);
  return st.p

noextract let bld_ones : st_monad circ_st nat =
  st <-- get;
  _ <-- put (bld_aux st Ones);
  return st.p

noextract let bld_input (j:nat) : st_monad circ_st nat =
  st <-- get;
  _ <-- put (bld_aux st (if j<st.m then Input j else Zeros));
  return st.p

noextract let bld_and (a b:nat) : st_monad circ_st nat =
  st <-- get;
  _ <-- put (bld_aux st (if a<st.p && b<st.p then And a b else Zeros));
  return st.p

noextract let bld_xor (a b:nat) : st_monad circ_st nat =
  st <-- get;
  _ <-- put (bld_aux st (if a<st.p && b<st.p then Xor a b else Zeros));
  return st.p

noextract let bld_or (a b:nat) : st_monad circ_st nat =
  st <-- get;
  _ <-- put (bld_aux st (if a<st.p && b<st.p then Or a b else Zeros));
  return st.p

noextract let bld_not (a:nat) : st_monad circ_st nat =
  st <-- get;
  _ <-- put (bld_aux st (if a<st.p then Not a else Zeros));
  return st.p

#push-options "--ifuel 1"
noextract let rec nth_gate (#m #p:nat) (circ:circuit m p) (i:nat{i<p}) : gate m i =
  let Cons circ g = circ in
  if i=p-1 then g else nth_gate circ i
#pop-options

#push-options "--fuel 1"
let nth_gate_lemma (#m #p:nat) (circ:circuit m p) (g:gate m p) (i:nat{i<p}) :
  Lemma (nth_gate circ i == nth_gate (Cons circ g) i)
  [SMTPat (nth_gate (Cons circ g) i)]
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec nth_gate_eq_intro (#m #p:nat) (circ1 circ2:circuit m p) :
  Lemma
    (requires forall (i:nat{i<p}). nth_gate circ1 i == nth_gate circ2 i)
    (ensures circ1 == circ2) =
  if p=0 then () else (
    let Cons tl1 g1 = circ1 in
    let Cons tl2 g2 = circ2 in
    assert(g1 == nth_gate circ1 (p-1));
    assert(forall (i:nat{i<p-1}). nth_gate tl1 i == nth_gate circ1 i);
    nth_gate_eq_intro tl1 tl2
  )
#pop-options

#push-options "--fuel 1"
noextract let rec circuit_of_fun (#m #p:nat) (f:(i:nat{i<p} -> gate m i)) : (circ:circuit m p{forall (i:nat{i<p}). nth_gate circ i == f i}) =
  if p=0 then Empty else Cons (circuit_of_fun f) (f (p-1))
#pop-options

let circuit_of_fun_nth_gate (#m #p:nat) (circ:circuit m p) : Lemma (circuit_of_fun (nth_gate circ) == circ) =
  nth_gate_eq_intro (circuit_of_fun (nth_gate circ)) circ

val circuit_def_lemma (#m #p:nat) (circ:circuit m p) (g:gate m p) (#lN:bar) (x:xNxM lN.xN m) (i:nat{i<p}) :
  Lemma (circuit_def (Cons circ g) x i == circuit_def circ x i)
  //[SMTPat (circuit_def (Cons circ g) x i)]
#push-options "--fuel 1"
let circuit_def_lemma #m #p circ g #lN x i = ()
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec nth_gate_zeros (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  : Lemma (requires nth_gate circ i == Zeros) (ensures circuit_def circ inputs i == (_).zeros_)
  =
  if i=p-1 then () else let Cons circ' g = circ in nth_gate_zeros circ' inputs i

let rec nth_gate_ones (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  : Lemma (requires nth_gate circ i == Ones) (ensures circuit_def circ inputs i == (_).ones_)
  =
  if i=p-1 then () else let Cons circ' g = circ in nth_gate_ones circ' inputs i

let rec nth_gate_input (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  (j:nat{j<m})
  : Lemma (requires nth_gate circ i == Input j) (ensures circuit_def circ inputs i == index j inputs)
  =
  if i=p-1 then () else let Cons circ' g = circ in nth_gate_input circ' inputs i j

let rec nth_gate_and (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  (a:nat{a<i}) (x:(_).t{x==circuit_def circ inputs a}) (b:nat{b<i}) (y:(_).t{y==circuit_def circ inputs b})
  : Lemma (requires nth_gate circ i == And a b) (ensures circuit_def circ inputs i == (_).and_ x y)
  =
  if i=p-1 then () else let Cons circ' g = circ in nth_gate_and circ' inputs i a x b y

let rec nth_gate_xor (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  (a:nat{a<i}) (x:(_).t{x==circuit_def circ inputs a}) (b:nat{b<i}) (y:(_).t{y==circuit_def circ inputs b})
  : Lemma (requires nth_gate circ i == Xor a b) (ensures circuit_def circ inputs i == (_).xor_ x y)
  =
  if i=p-1 then () else let Cons circ' g = circ in nth_gate_xor circ' inputs i a x b y

let rec nth_gate_or (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  (a:nat{a<i}) (x:(_).t{x==circuit_def circ inputs a}) (b:nat{b<i}) (y:(_).t{y==circuit_def circ inputs b})
  : Lemma (requires nth_gate circ i == Or a b) (ensures circuit_def circ inputs i == (_).or_ x y)
  =
  if i=p-1 then () else let Cons circ' g = circ in nth_gate_or circ' inputs i a x b y

let rec nth_gate_not (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  (a:nat{a<i}) (x:(_).t{x==circuit_def circ inputs a})
  : Lemma (requires nth_gate circ i == Not a) (ensures circuit_def circ inputs i == (_).not_ x)
  =
  if i=p-1 then () else let Cons circ' g = circ in nth_gate_not circ' inputs i a x
#pop-options

noextract let compile_zeros (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  : Pure (_).t (requires nth_gate circ i == Zeros) (ensures fun x -> x == circuit_def circ inputs i)
  = nth_gate_zeros circ inputs i; normalize_term((_).zeros_)

noextract let compile_ones (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  : Pure (_).t (requires nth_gate circ i == Ones) (ensures fun x -> x == circuit_def circ inputs i)
  = nth_gate_ones circ inputs i; normalize_term((_).ones_)

noextract let compile_input (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  (j:nat{j<m}) : Pure (_).t (requires nth_gate circ i == Input j) (ensures fun x -> x == circuit_def circ inputs i)
  =
  nth_gate_input circ inputs i j;
  let y = normalize_term(index j) inputs in
  assume(y == index j inputs);
  y

noextract let compile_and (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  (a:nat{a<i}) (x:(_).t{x==circuit_def circ inputs a})
  (b:nat{b<i}) (y:(_).t{y==circuit_def circ inputs b})
  : Pure (_).t (requires nth_gate circ i == And a b) (ensures fun z -> z == circuit_def circ inputs i)
  = nth_gate_and circ inputs i a x b y; normalize_term((_).and_) x y

noextract let compile_xor (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  (a:nat{a<i}) (x:(_).t{x==circuit_def circ inputs a})
  (b:nat{b<i}) (y:(_).t{y==circuit_def circ inputs b})
  : Pure (_).t (requires nth_gate circ i == Xor a b) (ensures fun z -> z == circuit_def circ inputs i)
  = nth_gate_xor circ inputs i a x b y; normalize_term((_).xor_) x y

noextract let compile_or (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  (a:nat{a<i}) (x:(_).t{x==circuit_def circ inputs a})
  (b:nat{b<i}) (y:(_).t{y==circuit_def circ inputs b})
  : Pure (_).t (requires nth_gate circ i == Or a b) (ensures fun z -> z == circuit_def circ inputs i)
  = nth_gate_or circ inputs i a x b y; normalize_term((_).or_) x y

noextract let compile_not (#m #p:nat) (circ:circuit m p) (#lN:bar) (inputs:xNxM lN.xN m) (i:nat{i<p})
  (a:nat{a<i}) (x:(_).t{x==circuit_def circ inputs a})
  : Pure (_).t (requires nth_gate circ i == Not a) (ensures fun y -> y == circuit_def circ inputs i)
  = nth_gate_not circ inputs i a x; normalize_term((_).not_) x
