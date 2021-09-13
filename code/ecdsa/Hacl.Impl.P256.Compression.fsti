module Hacl.Impl.P256.Compression

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

open Hacl.Spec.MontgomeryMultiplication


#set-options "--z3rlimit 200 --ifuel 0 --fuel 0" 


let notCompressedForm (c: curve) = lbuffer uint8 (getCoordinateLenU c *! 2ul +! 1ul)

let compressedForm (c: curve) = lbuffer uint8 (getCoordinateLenU c +! 1ul)


inline_for_extraction
val decompressionNotCompressedForm: #c: curve -> b: notCompressedForm c -> result: lbuffer uint8 (getCoordinateLenU c *! 2ul) -> Stack bool 
  (requires fun h -> live h b /\ live h result /\ disjoint b result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ (
    let len = v (getCoordinateLenU c) in 
    
    let id = Lib.Sequence.index (as_seq h0 b) 0 in 
    let x = Lib.Sequence.sub (as_seq h0 b) 1 len in 
    let y = Lib.Sequence.sub (as_seq h0 b) (len + 1) len in 

    let xResult = Lib.Sequence.sub (as_seq h1 result) 0 len in 
    let yResult = Lib.Sequence.sub (as_seq h1 result) len len in 
    if uint_v id = 4 then 
       r == true /\ x == xResult /\ y == yResult
    else 
      r == false))


inline_for_extraction
val decompressionCompressedForm: #c: curve -> b: compressedForm -> result: lbuffer uint8 (size 64) -> Stack bool 
  (requires fun h -> live h b /\ live h result /\ disjoint b result)
  (ensures fun h0 r h1 -> 
    (
      let id = Lib.Sequence.index (as_seq h0 b) 0 in 
      let xSequence = Lib.Sequence.sub (as_seq h0 b) 1 32 in 
      let x =  Lib.ByteSequence.nat_from_bytes_be xSequence in 
      if uint_v id = 2 || uint_v id = 3 then
	if x < prime256 then 
	  r == true /\ 
	  (
	    let y = 
              let sq = sq_root_spec  #c #DH (((x * x * x + aCoordinate #P256 * x + bCoordinate #P256) % prime256)) in 
              if (uint_v id) % 2 = (sq % 2) then 
		sq
              else
	         (0 - sq) % prime256 
	    in 
	    as_seq h1 (gsub result (size 0) (size 32)) == xSequence /\
	    as_seq h1 (gsub result (size 32) (size 32)) == Lib.ByteSequence.nat_to_bytes_be 32 y)
	else 
	  r == false
      else 
	r == false) /\
  modifies (loc result) h0 h1)

inline_for_extraction
val compressionNotCompressedForm: #c: curve -> b: lbuffer uint8 (size 64) -> result: notCompressedForm -> 
  Stack unit 
    (requires fun h -> live h b /\ live h result /\ disjoint b result)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      (
	let id = Lib.Sequence.index (as_seq h1 result) 0 in 
	let x = Lib.Sequence.sub (as_seq h0 b) 0 32 in 
	  let xResult = Lib.Sequence.sub (as_seq h1 result) 1 32 in 
	let y = Lib.Sequence.sub (as_seq h0 b) 32 32 in 
	  let yResult = Lib.Sequence.sub (as_seq h1 result) 33 32 in 
	uint_v id == 4 /\ xResult == x /\ yResult == y 	
      )
    )

inline_for_extraction
val compressionCompressedForm: #c: curve -> b: lbuffer uint8 (size 64) -> result: compressedForm -> 
  Stack unit 
    (requires fun h -> live h b /\ live h result /\ disjoint b result)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      (
        let identifier = Lib.Sequence.index (as_seq h1 result) 0 in 
        let x = Lib.Sequence.sub (as_seq h0 b) 0 32 in 
	  let xResult = Lib.Sequence.sub (as_seq h1 result) 1 32 in 
        let y = Lib.Sequence.sub (as_seq h0 b) 32 32 in 
        uint_v identifier == (Lib.ByteSequence.nat_from_intseq_be y % pow2 1)  + 2 /\
	x == xResult	
      )  
  )
