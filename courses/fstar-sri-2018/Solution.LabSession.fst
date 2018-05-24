module Solution.LabSession

/// Lab Session: Programming in Low*. This is intended as a warm-up to get
/// familiar with Low*. The module defines a few aliases that may come in handy.
module B = LowStar.Buffer
module U32 = FStar.UInt32
module I32 = FStar.Int32
module HS = FStar.HyperStack

open LowStar.BufferOps
open FStar.HyperStack.ST
open LowStar.Modifies

(***** Machine integers *)
/// First exercise, related to machine integers. Complete the definition below
/// for the absolute value. This is, of course, tricky, since with fixed-width
/// integers, one cannot always compute the absolute value (why?). You will need
/// to craft a suitable pre-condition to make the function go through.
/// We first define the pure specification.
let abs (x: int): Tot int = if x > 0 then x else -x

/// In order to move forward, you will need the definition of the smallest
/// representable signed 32-bit integer.
let min_int32 = I32.(0l -^ 0x7fffffffl -^ 1l)

/// Then show that our function that operates on machine integers performs that
/// operation properly. Remember that computations over machine integers are
/// performed like this: I32.( 0l -^ 1l)
/// - no unary minus
/// - local open syntax I32.( ... )
/// - arithmetic operations are suffixed with ^
let abs1 (x: Int32.t): Pure Int32.t
  (requires x <> min_int32) // enhance this pre-condition
  (ensures (fun y -> I32.v y = abs (I32.v x))) // enhance this post-condition to use abs above
= let open I32 in
  if x <^ 0l then 0l -^ x else x

/// A second variant: this one will take True as a precondition, but will return
/// an option type for those inputs whose absolute value cannot be computed.
let abs2 (x: Int32.t): Pure (option Int32.t)
  (requires True) // must leave True here
  (ensures (function None -> x = min_int32 | Some y -> I32.v y = abs (I32.v x)))
= if x = min_int32 then None
  else Some (abs1 x)

(***** Working with references *)
/// The classic swap on references: provide suitable pre- and post-conditions.
/// Two useful operations: b *= (e), for writing into a pointer, and !*(e), for
/// dereferencing a pointer.
let swap (x: B.pointer UInt32.t) (y: B.pointer UInt32.t): Stack unit
  (requires fun h0 -> B.live h0 x /\ B.live h0 y /\ B.disjoint x y)
  (ensures fun h0 _ h1 ->
           modifies (loc_union (loc_buffer x) (loc_buffer y)) h0 h1 /\
           B.get h1 x 0 = B.get h0 y 0 /\
           B.get h1 y 0 = B.get h0 x 0)
= let tmp = !* x in
  x *= !* y;
  y *= tmp


(***** Working with buffers *)

/// The next exercise is a copy from a source to a destination. Just like in the
/// earlier lecture, we will prove memory safety. We will also prove functional
/// correctness, i.e. that after copy i elements from src to dst, the sequences
/// that reflect the contents of the buffer are equal.

/// Our first useful definition is a type abbreviation for a buffer whose length
/// is known at type-checking time.
let lbuffer (len:U32.t) (a:Type) = b:B.buffer a{U32.(len <=^ B.len b)}

/// A predicate, stating that b1 and b2 are equal, in memory h, over their first
/// i elements.
let prefix_equal (#l:U32.t) (#a:Type) (h:HS.mem) (b1 b2: lbuffer l a) (i:U32.t{U32.(i <=^ l)}) =
  forall (j:nat). j < U32.v i ==> B.get h b1 j == B.get h b2 j

/// For this version, you are expected to verify safety, but also functional
/// correctness. Start by writing the code, then proving that it is memory safe.
/// Here is the list of predicates you will need:
/// - B.live h b, to show that buffer b is live in memory h
/// - B.disjoint b1 b2, to show that two buffers do not overlap
/// - U32.( ... <=^ ... ), less-than-or-equal comparison for unsigned 32-bit ints
/// - loc_buffer b, the injection of a buffer into the generic type of memory locations
/// - modifies l h0 h1, a predicate stating that going from memory h0 to memory
///   h1, only location l was modified.
/// Once you have proved memory safety, show how copy_correct extends the
/// prefix_equal predicate.
let rec copy_correct (#len:U32.t) (dst src:lbuffer len U32.t) (cur: U32.t): Stack unit
  (requires (fun h0 ->
            let open U32 in
                B.live h0 src 
              /\ B.live h0 dst
              /\ B.disjoint src dst
              /\ cur <=^ len
              /\ prefix_equal h0 src dst cur))
  (ensures fun h0 _ h1 ->
           B.live h1 src
           /\ B.live h1 dst
           /\ modifies (loc_buffer dst) h0 h1
           /\ prefix_equal h1 src dst len)
= let open U32 in
  if cur <> len
  then begin
    dst.(cur) <- src.(cur);
    copy_correct dst src (cur +^ 1ul)
 end
