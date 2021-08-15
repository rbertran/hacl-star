module Hacl.Impl.AES.SubBytes

open FStar.UInt
open FStar.Tactics
open Lib.Sliceable
open Lib.Circuits

#set-options "--fuel 0 --ifuel 0 --z3rlimit 0"

let circuit_builder : st_monad circ_st (nat*nat*nat*nat*nat*nat*nat*nat) =
a0 <-- bld_input 7;
a1 <-- bld_input 6;
a2 <-- bld_input 5;
a3 <-- bld_input 4;
a4 <-- bld_input 3;
a5 <-- bld_input 2;
a6 <-- bld_input 1;
a7 <-- bld_input 0;
a8 <-- bld_xor a6 a4;
a9 <-- bld_xor a3 a0;
a10 <-- bld_xor a1 a2;
a11 <-- bld_xor a7 a10;
a12 <-- bld_xor a8 a9;
a13 <-- bld_xor a1 a5;
a14 <-- bld_xor a0 a6;
a15 <-- bld_xor a8 a13;
a16 <-- bld_xor a6 a11;
a17 <-- bld_xor a3 a11;
a18 <-- bld_xor a7 a12;
a19 <-- bld_xor a12 a13;
a20 <-- bld_xor a2 a5;
a21 <-- bld_xor a10 a12;
a22 <-- bld_xor a5 a14;
a23 <-- bld_xor a0 a5;
a24 <-- bld_xor a7 a15;
a25 <-- bld_xor a6 a5;
a26 <-- bld_xor a9 a25;
a27 <-- bld_xor a11 a22;
a28 <-- bld_xor a8 a20;
a29 <-- bld_xor a0 a11;
a46 <-- bld_xor a28 a12;
a47 <-- bld_xor a28 a14;
a48 <-- bld_xor a14 a26;
a49 <-- bld_xor a23 a21;
a50 <-- bld_xor a29 a24;
a51 <-- bld_and a26 a12;
a52 <-- bld_and a27 a18;
a53 <-- bld_xor a19 a51;
a54 <-- bld_and a17 a7;
a55 <-- bld_xor a54 a51;
a56 <-- bld_and a14 a28;
a57 <-- bld_and a16 a11;
a58 <-- bld_xor a47 a56;
a59 <-- bld_and a29 a24;
a60 <-- bld_xor a59 a56;
a61 <-- bld_and a9 a15;
a62 <-- bld_and a48 a46;
a63 <-- bld_xor a62 a61;
a64 <-- bld_and a23 a21;
a65 <-- bld_xor a64 a61;
a66 <-- bld_xor a53 a52;
a67 <-- bld_xor a55 a49;
a68 <-- bld_xor a58 a57;
a69 <-- bld_xor a60 a65;
a70 <-- bld_xor a66 a63;
a71 <-- bld_xor a67 a65;
a72 <-- bld_xor a68 a63;
a73 <-- bld_xor a69 a50;
a74 <-- bld_xor a72 a73;
a75 <-- bld_and a72 a70;
a76 <-- bld_xor a71 a75;
a77 <-- bld_xor a70 a71;
a78 <-- bld_xor a73 a75;
a79 <-- bld_and a78 a77;
a80 <-- bld_and a76 a74;
a81 <-- bld_and a70 a73;
a82 <-- bld_and a77 a81;
a83 <-- bld_xor a77 a75;
a84 <-- bld_and a71 a72;
a85 <-- bld_and a74 a84;
a86 <-- bld_xor a74 a75;
a87 <-- bld_xor a71 a79;
a88 <-- bld_xor a82 a83;
a89 <-- bld_xor a73 a80;
a90 <-- bld_xor a85 a86;
a91 <-- bld_xor a88 a90;
a92 <-- bld_xor a87 a89;
a93 <-- bld_xor a87 a88;
a94 <-- bld_xor a89 a90;
a95 <-- bld_xor a92 a91;
a96 <-- bld_and a94 a12;
a97 <-- bld_and a90 a18;
a98 <-- bld_and a89 a7;
a99 <-- bld_and a93 a28;
a100 <-- bld_and a88 a11;
a101 <-- bld_and a87 a24;
a102 <-- bld_and a92 a15;
a103 <-- bld_and a95 a46;
a104 <-- bld_and a91 a21;
a105 <-- bld_and a94 a26;
a106 <-- bld_and a90 a27;
a107 <-- bld_and a89 a17;
a108 <-- bld_and a93 a14;
a109 <-- bld_and a88 a16;
a110 <-- bld_and a87 a29;
a111 <-- bld_and a92 a9;
a112 <-- bld_and a95 a48;
a113 <-- bld_and a91 a23;
a114 <-- bld_xor a111 a112;
a115 <-- bld_xor a100 a106;
a116 <-- bld_xor a103 a114;
a117 <-- bld_xor a105 a115;
a118 <-- bld_xor a98 a108;
a119 <-- bld_xor a96 a99;
a120 <-- bld_xor a114 a119;
a121 <-- bld_xor a97 a117;
a122 <-- bld_xor a96 a102;
a123 <-- bld_xor a101 a109;
a124 <-- bld_xor a104 a110;
a125 <-- bld_xor a98 a121;
a126 <-- bld_xor a118 a124;
a127 <-- bld_xor a107 a115;
a128 <-- bld_xor a99 a102;
a129 <-- bld_xor a117 a128;
a130 <-- bld_xor a113 a126;
a131 <-- bld_xor a111 a122;
a132 <-- bld_xor a118 a123;
a135 <-- bld_xor a101 a114;
a138 <-- bld_xor a100 a108;
a139 <-- bld_xor a119 a127;
a141 <-- bld_xor a104 a123;
a142 <-- bld_xor a138 a141;
a143 <-- bld_xor a100 a122;
a145 <-- bld_xor a126 a139;
a147 <-- bld_xor a121 a143;
a148 <-- bld_xor a120 a132;
a149 <-- bld_not a148;
a150 <-- bld_xor a116 a142;
a151 <-- bld_not a150;
a152 <-- bld_xor a116 a145;
a153 <-- bld_xor a125 a135;
a154 <-- bld_xor a120 a121;
a155 <-- bld_xor a130 a131;
a156 <-- bld_not a155;
a157 <-- bld_xor a116 a147;
a158 <-- bld_not a157;
a159 <-- bld_xor a116 a129;
return (a149,a151,a152,a153,a154,a156,a158,a159)

let circuit_info = normalize_term(run circuit_builder (circ_st_empty 8))

let circ_size : nat =
  normalize_term(
    let (_,st) = circuit_info in
    st.p
  )

let circ : circuit 8 circ_size =
  normalize_term(
    let (_,st) = circuit_info in
    st.circ
  )

private val outputs : i:nat{i<8} -> j:nat{j<circ_size}
let outputs =
  let (outputs,_) = circuit_info in
  let (r0,r1,r2,r3,r4,r5,r6,r7) = outputs in
  let open FStar.Tactics in
  fun i -> match i with
  | 0 -> r0
  | 1 -> r1
  | 2 -> r2
  | 3 -> r3
  | 4 -> r4
  | 5 -> r5
  | 6 -> r6
  | 7 -> r7

private val subBytes (lN:lN) (x:xNxM lN.xN 8) : xNxM lN.xN 8
let subBytes lN x = reduce_output (circuit_spec2 circ lN) 8 outputs x

private val subBytes_sliceable (lN:lN) : Lemma (sliceable (subBytes lN) (subBytes l1))
let subBytes_sliceable lN =
  circuit_spec2_sliceable circ lN;
  reduce_output_sliceable (circuit_spec2 circ lN) (circuit_spec2 circ l1) 8 outputs;
  ()

open Hacl.Spec.AES.SubBytes
module UI=FStar.UInt

val subBytes_def (lN:lN) (x:xNxM lN.xN 8) (j:nat{j<lN.xN.n}) :
  Lemma (column j (subBytes lN x) == of_uint (sbox (to_uint (column j x))))
let subBytes_def lN x j =
 subBytes_sliceable lN;
 assume(bruteforce (subBytes lN) (subBytes l1) sbox);
 ()

open Lib.IntTypes
open Lib.Bitmap

let subBytes64 (x:xNxM (uN U64 SEC 64).xN 8) : xNxM (uN U64 SEC 64).xN 8 = subBytes (uN U64 SEC 64) x
