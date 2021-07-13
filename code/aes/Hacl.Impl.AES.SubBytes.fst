module Hacl.Impl.AES.SubBytes

open FStar.UInt
open Lib.Sliceable
open Lib.Circuits

#set-options "--fuel 0 --ifuel 0 --z3rlimit 0"

private val circ : circuit 8 160
let circ =
fun i -> match i with
| 0 -> Input 7 | 1 -> Input 6 | 2 -> Input 5 | 3 -> Input 4 | 4 -> Input 3 | 5 -> Input 2
| 6 -> Input 1 | 7 -> Input 0 | 8 -> Xor 6 4 | 9 -> Xor 3 0 | 10 -> Xor 1 2 | 11 -> Xor 7 10
| 12 -> Xor 8 9 | 13 -> Xor 1 5 | 14 -> Xor 0 6 | 15 -> Xor 8 13 | 16 -> Xor 6 11 | 17 -> Xor 3 11 
| 18 -> Xor 7 12 | 19 -> Xor 12 13 | 20 -> Xor 2 5 | 21 -> Xor 10 12 | 22 -> Xor 5 14 | 23 -> Xor 0 5
| 24 -> Xor 7 15 | 25 -> Xor 6 5 | 26 -> Xor 9 25 | 27 -> Xor 11 22 | 28 -> Xor 8 20 | 29 -> Xor 0 11
| 30 -> Zeros | 31 -> Zeros | 32 -> Zeros | 33 -> Zeros | 34 -> Zeros | 35 -> Zeros
| 36 -> Zeros | 37 -> Zeros | 38 -> Zeros | 39 -> Zeros | 40 -> Zeros | 41 -> Zeros
| 42 -> Zeros | 43 -> Zeros | 44 -> Zeros | 45 -> Zeros | 46 -> Xor 28 12 | 47 -> Xor 28 14
| 48 -> Xor 14 26 | 49 -> Xor 23 21 | 50 -> Xor 29 24 | 51 -> And 26 12 | 52 -> And 27 18 | 53 -> Xor 19 51
| 54 -> And 17 7 | 55 -> Xor 54 51 | 56 -> And 14 28 | 57 -> And 16 11 | 58 -> Xor 47 56 | 59 -> And 29 24
| 60 -> Xor 59 56 | 61 -> And 9 15 | 62 -> And 48 46 | 63 -> Xor 62 61 | 64 -> And 23 21 | 65 -> Xor 64 61
| 66 -> Xor 53 52 | 67 -> Xor 55 49 | 68 -> Xor 58 57 | 69 -> Xor 60 65 | 70 -> Xor 66 63 | 71 -> Xor 67 65 
| 72 -> Xor 68 63 | 73 -> Xor 69 50 | 74 -> Xor 72 73 | 75 -> And 72 70 | 76 -> Xor 71 75 | 77 -> Xor 70 71 
| 78 -> Xor 73 75 | 79 -> And 78 77 | 80 -> And 76 74 | 81 -> And 70 73 | 82 -> And 77 81 | 83 -> Xor 77 75 
| 84 -> And 71 72 | 85 -> And 74 84 | 86 -> Xor 74 75 | 87 -> Xor 71 79 | 88 -> Xor 82 83 | 89 -> Xor 73 80 
| 90 -> Xor 85 86 | 91 -> Xor 88 90 | 92 -> Xor 87 89 | 93 -> Xor 87 88 | 94 -> Xor 89 90 | 95 -> Xor 92 91 
| 96 -> And 94 12 | 97 -> And 90 18 | 98 -> And 89 7 | 99 -> And 93 28 | 100 -> And 88 11 | 101 -> And 87 24 
| 102 -> And 92 15 | 103 -> And 95 46 | 104 -> And 91 21 | 105 -> And 94 26 | 106 -> And 90 27 | 107 -> And 89 17 
| 108 -> And 93 14 | 109 -> And 88 16 | 110 -> And 87 29 | 111 -> And 92 9 | 112 -> And 95 48 | 113 -> And 91 23 
| 114 -> Xor 111 112 | 115 -> Xor 100 106 | 116 -> Xor 103 114 | 117 -> Xor 105 115 | 118 -> Xor 98 108 | 119 -> Xor 96 99 
| 120 -> Xor 114 119 | 121 -> Xor 97 117 | 122 -> Xor 96 102 | 123 -> Xor 101 109 | 124 -> Xor 104 110  | 125 -> Xor 98 121 
| 126 -> Xor 118 124 | 127 -> Xor 107 115 | 128 -> Xor 99 102 | 129 -> Xor 117 128 | 130 -> Xor 113 126 | 131 -> Xor 111 122 
| 132 -> Xor 118 123 | 133 -> Zeros | 134 -> Zeros | 135 -> Xor 101 114 | 136 -> Zeros | 137 -> Zeros
| 138 -> Xor 100 108 | 139 -> Xor 119 127 | 140 -> Zeros | 141 -> Xor 104 123 | 142 -> Xor 138 141 | 143 -> Xor 100 122 
| 144 -> Zeros | 145 -> Xor 126 139 | 146 -> Zeros | 147 -> Xor 121 143 | 148 -> Xor 120 132 | 149 -> Not 148
| 150 -> Xor 116 142 | 151 -> Not 150 | 152 -> Xor 116 145 | 153 -> Xor 125 135 | 154 -> Xor 120 121 | 155 -> Xor 130 131
| 156 -> Not 155 | 157 -> Xor 116 147 | 158 -> Not 157 | 159 -> Xor 116 129

private val outputs : (i:nat{i<8}) -> (j:nat{j<160})
let outputs i =
match i with
| 0 -> 149
| 1 -> 151
| 2 -> 152
| 3 -> 153
| 4 -> 154
| 5 -> 156
| 6 -> 158
| 7 -> 159

private val subBytes_def (lN:bar) (x:xNxM lN.xN 8) : xNxM lN.xN 8
let subBytes_def lN x = reduce_output (circuit_spec circ lN) 8 outputs x

private val sliceable_subBytes_def (lN:bar) : Lemma (sliceable (subBytes_def lN) (subBytes_def l1))
let sliceable_subBytes_def lN =
  reduce_output_sliceable (circuit_spec circ lN) (circuit_spec circ l1) 8 outputs;
  ()

#push-options "--fuel 1 --ifuel 1"
let subBytes (lN:bar) (x:xNxM lN.xN 8) : xNxM lN.xN 8 =
let (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7,())))))))) : lN.xN.t*(lN.xN.t*(lN.xN.t*(lN.xN.t*(lN.xN.t*(lN.xN.t*(lN.xN.t*(lN.xN.t*unit))))))) = x in
let a8 = lN.xor_ a6 a4 in let a9 = lN.xor_ a3 a0 in let a10 = lN.xor_ a1 a2 in let a11 = lN.xor_ a7 a10 in
let a12 = lN.xor_ a8 a9 in let a13 = lN.xor_ a1 a5 in let a14 = lN.xor_ a0 a6 in let a15 = lN.xor_ a8 a13 in
let a16 = lN.xor_ a6 a11 in let a17 = lN.xor_ a3 a11 in let a18 = lN.xor_ a7 a12 in let a19 = lN.xor_ a12 a13 in
let a20 = lN.xor_ a2 a5 in let a21 = lN.xor_ a10 a12 in let a22 = lN.xor_ a5 a14 in let a23 = lN.xor_ a0 a5 in
let a24 = lN.xor_ a7 a15 in let a25 = lN.xor_ a6 a5 in let a26 = lN.xor_ a9 a25 in let a27 = lN.xor_ a11 a22 in
let a28 = lN.xor_ a8 a20 in let a29 = lN.xor_ a0 a11 in let a30 = lN.zeros_ in let a31 = lN.zeros_ in
let a32 = lN.zeros_ in let a33 = lN.zeros_ in let a34 = lN.zeros_ in let a35 = lN.zeros_ in
let a36 = lN.zeros_ in let a37 = lN.zeros_ in let a38 = lN.zeros_ in let a39 = lN.zeros_ in
let a40 = lN.zeros_ in let a41 = lN.zeros_ in let a42 = lN.zeros_ in let a43 = lN.zeros_ in
let a44 = lN.zeros_ in let a45 = lN.zeros_ in let a46 = lN.xor_ a28 a12 in let a47 = lN.xor_ a28 a14 in
let a48 = lN.xor_ a14 a26 in let a49 = lN.xor_ a23 a21 in let a50 = lN.xor_ a29 a24 in let a51 = lN.and_ a26 a12 in
let a52 = lN.and_ a27 a18 in let a53 = lN.xor_ a19 a51 in let a54 = lN.and_ a17 a7 in let a55 = lN.xor_ a54 a51 in
let a56 = lN.and_ a14 a28 in let a57 = lN.and_ a16 a11 in let a58 = lN.xor_ a47 a56 in let a59 = lN.and_ a29 a24 in
let a60 = lN.xor_ a59 a56 in let a61 = lN.and_ a9 a15 in let a62 = lN.and_ a48 a46 in let a63 = lN.xor_ a62 a61 in
let a64 = lN.and_ a23 a21 in let a65 = lN.xor_ a64 a61 in let a66 = lN.xor_ a53 a52 in let a67 = lN.xor_ a55 a49 in
let a68 = lN.xor_ a58 a57 in let a69 = lN.xor_ a60 a65 in let a70 = lN.xor_ a66 a63 in let a71 = lN.xor_ a67 a65 in
let a72 = lN.xor_ a68 a63 in let a73 = lN.xor_ a69 a50 in let a74 = lN.xor_ a72 a73 in let a75 = lN.and_ a72 a70 in
let a76 = lN.xor_ a71 a75 in let a77 = lN.xor_ a70 a71 in let a78 = lN.xor_ a73 a75 in let a79 = lN.and_ a78 a77 in
let a80 = lN.and_ a76 a74 in let a81 = lN.and_ a70 a73 in let a82 = lN.and_ a77 a81 in let a83 = lN.xor_ a77 a75 in
let a84 = lN.and_ a71 a72 in let a85 = lN.and_ a74 a84 in let a86 = lN.xor_ a74 a75 in let a87 = lN.xor_ a71 a79 in
let a88 = lN.xor_ a82 a83 in let a89 = lN.xor_ a73 a80 in let a90 = lN.xor_ a85 a86 in let a91 = lN.xor_ a88 a90 in
let a92 = lN.xor_ a87 a89 in let a93 = lN.xor_ a87 a88 in let a94 = lN.xor_ a89 a90 in let a95 = lN.xor_ a92 a91 in
let a96 = lN.and_ a94 a12 in let a97 = lN.and_ a90 a18 in let a98 = lN.and_ a89 a7 in let a99 = lN.and_ a93 a28 in
let a100 = lN.and_ a88 a11 in let a101 = lN.and_ a87 a24 in let a102 = lN.and_ a92 a15 in let a103 = lN.and_ a95 a46 in
let a104 = lN.and_ a91 a21 in let a105 = lN.and_ a94 a26 in let a106 = lN.and_ a90 a27 in let a107 = lN.and_ a89 a17 in
let a108 = lN.and_ a93 a14 in let a109 = lN.and_ a88 a16 in let a110 = lN.and_ a87 a29 in let a111 = lN.and_ a92 a9 in
let a112 = lN.and_ a95 a48 in let a113 = lN.and_ a91 a23 in let a114 = lN.xor_ a111 a112 in let a115 = lN.xor_ a100 a106 in
let a116 = lN.xor_ a103 a114 in let a117 = lN.xor_ a105 a115 in let a118 = lN.xor_ a98 a108 in let a119 = lN.xor_ a96 a99 in
let a120 = lN.xor_ a114 a119 in let a121 = lN.xor_ a97 a117 in let a122 = lN.xor_ a96 a102 in let a123 = lN.xor_ a101 a109 in
let a124 = lN.xor_ a104 a110 in let a125 = lN.xor_ a98 a121 in let a126 = lN.xor_ a118 a124 in let a127 = lN.xor_ a107 a115 in
let a128 = lN.xor_ a99 a102 in let a129 = lN.xor_ a117 a128 in let a130 = lN.xor_ a113 a126 in let a131 = lN.xor_ a111 a122 in
let a132 = lN.xor_ a118 a123 in let a133 = lN.zeros_ in let a134 = lN.zeros_ in let a135 = lN.xor_ a101 a114 in
let a136 = lN.zeros_ in let a137 = lN.zeros_ in let a138 = lN.xor_ a100 a108 in let a139 = lN.xor_ a119 a127 in
let a140 = lN.zeros_ in let a141 = lN.xor_ a104 a123 in let a142 = lN.xor_ a138 a141 in let a143 = lN.xor_ a100 a122 in
let a144 = lN.zeros_ in let a145 = lN.xor_ a126 a139 in let a146 = lN.zeros_ in let a147 = lN.xor_ a121 a143 in
let a148 = lN.xor_ a120 a132 in let a149 = lN.not_ a148 in let a150 = lN.xor_ a116 a142 in let a151 = lN.not_ a150 in
let a152 = lN.xor_ a116 a145 in let a153 = lN.xor_ a125 a135 in let a154 = lN.xor_ a120 a121 in let a155 = lN.xor_ a130 a131 in
let a156 = lN.not_ a155 in let a157 = lN.xor_ a116 a147 in let a158 = lN.not_ a157 in let a159 = lN.xor_ a116 a129 in
let f (i:nat{i<8}) : lN.xN.t =
  match i with
  | 0 -> a149 | 1 -> a151 | 2 -> a152 | 3 -> a153
  | 4 -> a154 | 5 -> a156 | 6 -> a158 | 7 -> a159
in
xNxM_mk lN.xN 8 f

val subBytes_eq_def (lN:bar) : Lemma (forall (x:xNxM lN.xN 8) (i:nat{i<8}). subBytes lN x == subBytes_def lN x)
let subBytes_eq_def lN = admit ()

val subBytes_sliceable (lN:bar) : Lemma (sliceable (subBytes lN) (subBytes l1))
let subBytes_sliceable lN =
  sliceable_intro (subBytes lN) (subBytes l1) (fun x j ->
    subBytes_eq_def lN;
    subBytes_eq_def l1;
    sliceable_subBytes_def lN;
    ()
  )

val sbox (i:nat{i<256}) : (r:nat{r<256})
let sbox i = match i with
|   0 -> 0x63 |   1 -> 0x7c |   2 -> 0x77 |   3 -> 0x7b |   4 -> 0xf2 |   5 -> 0x6b |   6 -> 0x6f |   7 -> 0xc5
|   8 -> 0x30 |   9 -> 0x01 |  10 -> 0x67 |  11 -> 0x2b |  12 -> 0xfe |  13 -> 0xd7 |  14 -> 0xab |  15 -> 0x76
|  16 -> 0xca |  17 -> 0x82 |  18 -> 0xc9 |  19 -> 0x7d |  20 -> 0xfa |  21 -> 0x59 |  22 -> 0x47 |  23 -> 0xf0
|  24 -> 0xad |  25 -> 0xd4 |  26 -> 0xa2 |  27 -> 0xaf |  28 -> 0x9c |  29 -> 0xa4 |  30 -> 0x72 |  31 -> 0xc0
|  32 -> 0xb7 |  33 -> 0xfd |  34 -> 0x93 |  35 -> 0x26 |  36 -> 0x36 |  37 -> 0x3f |  38 -> 0xf7 |  39 -> 0xcc
|  40 -> 0x34 |  41 -> 0xa5 |  42 -> 0xe5 |  43 -> 0xf1 |  44 -> 0x71 |  45 -> 0xd8 |  46 -> 0x31 |  47 -> 0x15
|  48 -> 0x04 |  49 -> 0xc7 |  50 -> 0x23 |  51 -> 0xc3 |  52 -> 0x18 |  53 -> 0x96 |  54 -> 0x05 |  55 -> 0x9a
|  56 -> 0x07 |  57 -> 0x12 |  58 -> 0x80 |  59 -> 0xe2 |  60 -> 0xeb |  61 -> 0x27 |  62 -> 0xb2 |  63 -> 0x75
|  64 -> 0x09 |  65 -> 0x83 |  66 -> 0x2c |  67 -> 0x1a |  68 -> 0x1b |  69 -> 0x6e |  70 -> 0x5a |  71 -> 0xa0
|  72 -> 0x52 |  73 -> 0x3b |  74 -> 0xd6 |  75 -> 0xb3 |  76 -> 0x29 |  77 -> 0xe3 |  78 -> 0x2f |  79 -> 0x84
|  80 -> 0x53 |  81 -> 0xd1 |  82 -> 0x00 |  83 -> 0xed |  84 -> 0x20 |  85 -> 0xfc |  86 -> 0xb1 |  87 -> 0x5b
|  88 -> 0x6a |  89 -> 0xcb |  90 -> 0xbe |  91 -> 0x39 |  92 -> 0x4a |  93 -> 0x4c |  94 -> 0x58 |  95 -> 0xcf
|  96 -> 0xd0 |  97 -> 0xef |  98 -> 0xaa |  99 -> 0xfb | 100 -> 0x43 | 101 -> 0x4d | 102 -> 0x33 | 103 -> 0x85
| 104 -> 0x45 | 105 -> 0xf9 | 106 -> 0x02 | 107 -> 0x7f | 108 -> 0x50 | 109 -> 0x3c | 110 -> 0x9f | 111 -> 0xa8
| 112 -> 0x51 | 113 -> 0xa3 | 114 -> 0x40 | 115 -> 0x8f | 116 -> 0x92 | 117 -> 0x9d | 118 -> 0x38 | 119 -> 0xf5
| 120 -> 0xbc | 121 -> 0xb6 | 122 -> 0xda | 123 -> 0x21 | 124 -> 0x10 | 125 -> 0xff | 126 -> 0xf3 | 127 -> 0xd2
| 128 -> 0xcd | 129 -> 0x0c | 130 -> 0x13 | 131 -> 0xec | 132 -> 0x5f | 133 -> 0x97 | 134 -> 0x44 | 135 -> 0x17
| 136 -> 0xc4 | 137 -> 0xa7 | 138 -> 0x7e | 139 -> 0x3d | 140 -> 0x64 | 141 -> 0x5d | 142 -> 0x19 | 143 -> 0x73
| 144 -> 0x60 | 145 -> 0x81 | 146 -> 0x4f | 147 -> 0xdc | 148 -> 0x22 | 149 -> 0x2a | 150 -> 0x90 | 151 -> 0x88
| 152 -> 0x46 | 153 -> 0xee | 154 -> 0xb8 | 155 -> 0x14 | 156 -> 0xde | 157 -> 0x5e | 158 -> 0x0b | 159 -> 0xdb
| 160 -> 0xe0 | 161 -> 0x32 | 162 -> 0x3a | 163 -> 0x0a | 164 -> 0x49 | 165 -> 0x06 | 166 -> 0x24 | 167 -> 0x5c
| 168 -> 0xc2 | 169 -> 0xd3 | 170 -> 0xac | 171 -> 0x62 | 172 -> 0x91 | 173 -> 0x95 | 174 -> 0xe4 | 175 -> 0x79
| 176 -> 0xe7 | 177 -> 0xc8 | 178 -> 0x37 | 179 -> 0x6d | 180 -> 0x8d | 181 -> 0xd5 | 182 -> 0x4e | 183 -> 0xa9
| 184 -> 0x6c | 185 -> 0x56 | 186 -> 0xf4 | 187 -> 0xea | 188 -> 0x65 | 189 -> 0x7a | 190 -> 0xae | 191 -> 0x08
| 192 -> 0xba | 193 -> 0x78 | 194 -> 0x25 | 195 -> 0x2e | 196 -> 0x1c | 197 -> 0xa6 | 198 -> 0xb4 | 199 -> 0xc6
| 200 -> 0xe8 | 201 -> 0xdd | 202 -> 0x74 | 203 -> 0x1f | 204 -> 0x4b | 205 -> 0xbd | 206 -> 0x8b | 207 -> 0x8a
| 208 -> 0x70 | 209 -> 0x3e | 210 -> 0xb5 | 211 -> 0x66 | 212 -> 0x48 | 213 -> 0x03 | 214 -> 0xf6 | 215 -> 0x0e
| 216 -> 0x61 | 217 -> 0x35 | 218 -> 0x57 | 219 -> 0xb9 | 220 -> 0x86 | 221 -> 0xc1 | 222 -> 0x1d | 223 -> 0x9e
| 224 -> 0xe1 | 225 -> 0xf8 | 226 -> 0x98 | 227 -> 0x11 | 228 -> 0x69 | 229 -> 0xd9 | 230 -> 0x8e | 231 -> 0x94
| 232 -> 0x9b | 233 -> 0x1e | 234 -> 0x87 | 235 -> 0xe9 | 236 -> 0xce | 237 -> 0x55 | 238 -> 0x28 | 239 -> 0xdf
| 240 -> 0x8c | 241 -> 0xa1 | 242 -> 0x89 | 243 -> 0x0d | 244 -> 0xbf | 245 -> 0xe6 | 246 -> 0x42 | 247 -> 0x68
| 248 -> 0x41 | 249 -> 0x99 | 250 -> 0x2d | 251 -> 0x0f | 252 -> 0xb0 | 253 -> 0x54 | 254 -> 0xbb | 255 -> 0x16

val subBytes_spec (lN:bar) (x:xNxM lN.xN 8) (j:nat{j<lN.xN.n}) :
  Lemma (column j (subBytes lN x) == of_uint (sbox (to_uint (column j x))))
let subBytes_spec lN x j =
  subBytes_sliceable lN;
  assert_norm(bruteforce (subBytes lN) (subBytes l1) sbox)

open Lib.IntTypes
open Lib.Bitmap

let subBytes64 (x:xNxM (uN U64 SEC 64).xN 8) : xNxM (uN U64 SEC 64).xN 8 = subBytes (uN U64 SEC 64) x
