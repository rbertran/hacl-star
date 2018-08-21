module Hacl.Frodo.Clear

open FStar.HyperStack.All
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.PQ.Buffer

// REMARK:
// The C implementation clears one 32-bit word at a time, so we need [len] 
// to be such that we clear an exact multiple of 32-bit words.
// This condition can be relaxed, but it's enough for our use in Frodo.

val clear_words_u16:
    nwords:size_t{v nwords % 2 == 0}
  -> b:buffer uint16{v nwords <= length b}
  -> Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer b) h0 h1 /\ 
      as_seq h1 (gsub #_ #(length b) #(v nwords) b (size 0) nwords) == 
      Seq.create (v nwords) (u16 0))

val clear_words_u8:
    nwords:size_t{v nwords % 4 == 0}
  -> b:buffer uint8{v nwords <= length b}
  -> Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer b) h0 h1 /\
      as_seq h1 (gsub #_ #(length b) #(v nwords) b (size 0) nwords) == 
      Seq.create (v nwords) (u8 0))
