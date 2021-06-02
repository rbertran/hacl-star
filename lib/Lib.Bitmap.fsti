module Lib.Bitmap

let secl : Type = Lib.IntTypes.secrecy_level
let intt : Type = (t:Lib.IntTypes.inttype{Lib.IntTypes.unsigned t})

let (^) (a b:bool) : bool = (a && (not b)) || ((not a) && b)

val bitmap (t:intt) (l:secl) (n:nat) : Tot Type0 (decreases n)
val bitmap_v (#t:intt) (#l:secl) (#n:nat) (x:bitmap t l n) (i:nat{i<n}) : Tot bool (decreases i)

val bitmap_mk (t:intt) (l:secl) (n:nat) (f:((i:nat{i<n}) -> bool)) : bitmap t l n
val bitmap_mk_def (t:intt) (l:secl) (n:nat) (f:((i:nat{i<n}) -> bool)) (i:nat{i<n}) :
  Lemma (bitmap_v (bitmap_mk t l n f) i == f i)
  [SMTPat (bitmap_v (bitmap_mk t l n f) i)]

val bitmap_ones (#t:intt) (#l:secl) (#n:nat) : bitmap t l n
val bitmap_zeros (#t:intt) (#l:secl) (#n:nat) : bitmap t l n

val bitmap_xor (#t:intt) (#l:secl) (#n:nat) (x y:bitmap t l n) : bitmap t l n
val bitmap_and (#t:intt) (#l:secl) (#n:nat) (x y:bitmap t l n) : bitmap t l n
val bitmap_or  (#t:intt) (#l:secl) (#n:nat) (x y:bitmap t l n) : bitmap t l n
val bitmap_not (#t:intt) (#l:secl) (#n:nat) (x:bitmap t l n) : bitmap t l n

val bitmap_ones_spec (#t:intt) (#l:secl) (#n:nat) (i:nat{i<n}) :
  Lemma (bitmap_v (bitmap_ones #t #l #n) i == true)
  [SMTPat (bitmap_v (bitmap_ones #t #l #n) i)]
val bitmap_zeros_spec (#t:intt) (#l:secl) (#n:nat) (i:nat{i<n}) :
  Lemma (bitmap_v (bitmap_zeros #t #l #n) i == false)
  [SMTPat (bitmap_v (bitmap_zeros #t #l #n) i)]

val bitmap_xor_spec (#t:intt) (#l:secl) (#n:nat) (x y:bitmap t l n) (i:nat{i<n}) :
  Lemma (bitmap_v (bitmap_xor x y) i ==  bitmap_v x i ^ bitmap_v y i)
  [SMTPat (bitmap_v (bitmap_xor x y) i)]
val bitmap_and_spec (#t:intt) (#l:secl) (#n:nat) (x y:bitmap t l n) (i:nat{i<n}) :
  Lemma (bitmap_v (bitmap_and x y) i ==  (bitmap_v x i && bitmap_v y i))
  [SMTPat (bitmap_v (bitmap_and x y) i)]
val bitmap_or_spec (#t:intt) (#l:secl) (#n:nat) (x y:bitmap t l n) (i:nat{i<n}) :
  Lemma (bitmap_v (bitmap_or x y) i ==  (bitmap_v x i || bitmap_v y i))
  [SMTPat (bitmap_v (bitmap_or x y) i)]
val bitmap_not_spec (#t:intt) (#l:secl) (#n:nat) (x:bitmap t l n) (i:nat{i<n}) :
  Lemma (bitmap_v (bitmap_not x) i ==  not (bitmap_v x i))
  [SMTPat (bitmap_v (bitmap_not x) i)]
