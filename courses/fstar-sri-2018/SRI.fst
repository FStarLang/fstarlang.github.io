module SRI

/// Some of the code demos intended for SRI's summer school. Presented in
/// the same order as they appear in the slides at https://jonathan.protzenko.fr

module B = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module M = LowStar.Modifies

open LowStar.BufferOps
open FStar.HyperStack.ST

/// Introductory demonstration (live): a copy function that is stateful,
/// operates on a low-level data structure (buffers), and requires spatial and
/// temporal reasoning. Of course, a naïve version fails to verify.
[@fail]
let rec copy1 (dst src: B.buffer U32.t) (i: U32.t): St unit =
  if U32.( i >^ 0ul ) then begin
    dst.(0ul) <- src.(0ul);
    let remaining = U32.(i -^ 1ul) in
    copy1 (B.sub dst 1ul remaining) (B.sub src 1ul remaining) remaining
  end

/// This version does not have a very deep specification, but has enough in
/// terms of pre- and post-conditions to make it go through. This function can
/// be compiled to a C recursive function, or one can rely on KreMLin to
/// generate a while-loop using -ftail-calls.
let rec copy2 (dst src: B.buffer U32.t) (i: U32.t): ST unit
  (requires fun h ->
    B.disjoint dst src /\ B.live h dst /\ B.live h src /\
    B.length dst >= U32.v i /\ B.length src >= U32.v i)
  (ensures fun _ _ _ -> True)
=
  let open B in
  if U32.( i >^ 0ul ) then begin
    dst.(0ul) <- src.(0ul);
    copy2 (B.offset dst 1ul) (B.offset src 1ul) U32.(i -^ 1ul)
  end

unfold inline_for_extraction
let malloc #a x =
  ralloc_mm #a #(FStar.Heap.trivial_preorder a) HS.root x

unfold inline_for_extraction
let free #a r =
  rfree #a #(FStar.Heap.trivial_preorder a) r

unfold inline_for_extraction
let ref a = mreference a (Heap.trivial_preorder a)

unfold inline_for_extraction
let live #a h (r: ref a) = HS.contains h r

/// A test on heap-allocated references
let test (): St UInt32.t =
  let r: ref UInt32.t = malloc 0ul in
  let x: UInt32.t = !r in
  free r;
  x

/// Use-after-free: ruled out
[@fail]
let test2 (): St UInt32.t =
  let r: ref UInt32.t = malloc 0ul in
  free r;
  !r

/// Double-free: ruled out
[@fail]
let test3 (): St UInt32.t =
  let r: ref UInt32.t = malloc 0ul in
  let x: UInt32.t = !r in
  free r;
  free r;
  x

/// Allocating without pushing a frame: ruled out
[@fail]
let test4 (): St unit =
  let r = salloc 0ul in
  ()

/// Returning the address of a reference on the stack: *not* ruled out, but
/// caller can't do anything with it!
let test5 (): St (stackref UInt32.t) =
  push_frame ();
  let r = salloc 0ul in
  let x = !r in
  pop_frame ();
  r

[@fail]
let test6 (): St UInt32.t =
  push_frame ();
  let r = test5 () in
  let x = !r in
  pop_frame ();
  x

/// Increment a counter
let incr #a (r: ref UInt32.t): ST unit
  (requires fun h -> live h r /\ HS.sel h r <> 0xfffffffful)
  (ensures fun h _ h' -> U32.(HS.sel h' r = HS.sel h r +^ 1ul))
=
  r := U32.(!r +^ 1ul)
