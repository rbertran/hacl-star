module Lib.Bitmap

open Lib.IntTypes

(*** Bitmap ***)

#push-options "--fuel 1 --ifuel 1"

private val nth (#t:intt) (#l:secl) (x:int_t t l) (i:nat{i<bits t}) : bool
let nth #t #l x i = UInt.nth #(bits t) (v x) i

let rec bitmap t l n =
  if n <= bits t then
    int_t t l
  else
    int_t t l * bitmap t l (n-bits t)

let rec bitmap_v #t #l #n x i =
  if n <= bits t then (
    nth (x <: int_t t l) i
  ) else (
    let (fst, rst) : int_t t l * bitmap t l (n-bits t) = x in
    if i < bits t then (
      nth fst i
    ) else (
      bitmap_v rst (i-bits t)
    )
  )

private val offset (#a:Type) (#m:nat) (f:(i:nat{i<m}) -> a) (off:nat) (i:nat{i<m-off}) : a
let offset f off i = f (i+off)

let rec bitmap_mk t l n f =
  if n <= bits t then (
    let r = UInt.from_vec #(bits t) (FStar.Seq.init (bits t) (fun i -> if i<n then f i else false)) in
    mk_int r <: int_t t l
  ) else (
    let r = UInt.from_vec #(bits t) (FStar.Seq.init (bits t) f) in
    (mk_int r, bitmap_mk t l (n-bits t) (offset #_ #n f (bits t)))
    <: int_t t l * bitmap t l (n-bits t)
  )

let rec bitmap_mk_def t l n f i =
  if i < bits t then
    ()
  else
    bitmap_mk_def t l (n-bits t) (offset #_ #n f (bits t)) (i-bits t)

let rec bitmap_ones #t #l #n =
  if n <= bits t then
    ones t l
  else
    ((ones t l <: int_t t l), bitmap_ones #t #l #(n-bits t))

let rec bitmap_zeros #t #l #n =
  if n <= bits t then
    zeros t l
  else
    ((zeros t l <: int_t t l), bitmap_zeros #t #l #(n-bits t))

let rec bitmap_xor #t #l #n x y =
  if n <= bits t then (
    let u : int_t t l = x in
    let v : int_t t l = y in
    logxor u v
  ) else (
    let (u, r) : int_t t l * bitmap t l (n-bits t) = x in
    let (v, s) : int_t t l * bitmap t l (n-bits t) = y in
    (logxor u v, bitmap_xor r s)
  )

let rec bitmap_and #t #l #n x y =
  if n <= bits t then (
    let u : int_t t l = x in
    let v : int_t t l = y in
    logand u v
  ) else (
    let (u, r) : int_t t l * bitmap t l (n-bits t) = x in
    let (v, s) : int_t t l * bitmap t l (n-bits t) = y in
    (logand u v, bitmap_and r s)
  )

let rec bitmap_or #t #l #n x y =
  if n <= bits t then (
    let u : int_t t l = x in
    let v : int_t t l = y in
    logor u v
  ) else (
    let (u, r) : int_t t l * bitmap t l (n-bits t) = x in
    let (v, s) : int_t t l * bitmap t l (n-bits t) = y in
    (logor u v, bitmap_or r s)
  )

let rec bitmap_not #t #l #n x =
  if n <= bits t then (
    let u : int_t t l = x in
    lognot u
  ) else (
    let (u, r) : int_t t l * bitmap t l (n-bits t) = x in
    (lognot u, bitmap_not r)
  )

let rec bitmap_ones_spec #t #l #n i =
  if i < bits t then
    ()
  else
    bitmap_ones_spec #t #l #(n-bits t) (i-bits t)

let rec bitmap_zeros_spec #t #l #n i =
  if i < bits t then
    UInt.zero_nth_lemma #(bits t) i
  else
    bitmap_zeros_spec #t #l #(n-bits t) (i-bits t)

let rec bitmap_xor_spec #t #l #n x y i =
  if n <= bits t then
    logxor_spec (x <: int_t t l) (y <: int_t t l)
  else
    let (u1, v1) : int_t t l * bitmap t l (n-bits t) = x in
    let (u2, v2) : int_t t l * bitmap t l (n-bits t) = y in
    if i < bits t then
      logxor_spec u1 u2
    else
      bitmap_xor_spec #t #l #(n-bits t) v1 v2 (i-bits t)

let rec bitmap_and_spec #t #l #n x y i =
  if n <= bits t then
    logand_spec (x <: int_t t l) (y <: int_t t l)
  else
    let (u1, v1) : int_t t l * bitmap t l (n-bits t) = x in
    let (u2, v2) : int_t t l * bitmap t l (n-bits t) = y in
    if i < bits t then
      logand_spec u1 u2
    else
      bitmap_and_spec #t #l #(n-bits t) v1 v2 (i-bits t)

let rec bitmap_or_spec #t #l #n x y i =
  if n <= bits t then
    logor_spec (x <: int_t t l) (y <: int_t t l)
  else
    let (u1, v1) : int_t t l * bitmap t l (n-bits t) = x in
    let (u2, v2) : int_t t l * bitmap t l (n-bits t) = y in
    if i < bits t then
      logor_spec u1 u2
    else
      bitmap_or_spec #t #l #(n-bits t) v1 v2 (i-bits t)

let rec bitmap_not_spec #t #l #n x i =
  if n <= bits t then
    lognot_spec (x <: int_t t l)
  else
    let (u, v) : int_t t l * bitmap t l (n-bits t) = x in
    if i < bits t then
      lognot_spec u
    else
      bitmap_not_spec #t #l #(n-bits t) v (i-bits t)
