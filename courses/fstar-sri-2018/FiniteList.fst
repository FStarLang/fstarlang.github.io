module FiniteList

open FStar.UInt32

/// We define the canonical abbreviations, taking care to shadow ST to make sure
/// we don't end up referring to FStar.ST by accident.
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module M = LowStar.Modifies
module ST = FStar.HyperStack.ST
module S = FStar.Seq

/// This brings into scope the ``!*`` and ``*=`` operators, which are
/// specifically designed to operate on buffers of size 1, i.e. on pointers.
open LowStar.BufferOps
open FStar.HyperStack.ST
open LowStar.Modifies

noeq
type t_struct a = {
  b: B.buffer a;
  first: U32.t;
  total_length: v:U32.t
}
type t a = B.pointer (t_struct a)

/// To facilitate writing predicates, we define a handy shortcut that is the
/// reflection of the ``!*`` operator at the proof level.
unfold
let deref #a (h: HS.mem) (x: B.pointer a) = B.get h x 0

/// Here's a representation predicate tying a `t a` to a sequence in a given
/// memory h.
let repr #a (h: HS.mem) (xs: t a) (l:Seq.seq a) =
  let open FStar.UInt32 in
  B.live h xs /\
  (let x = deref h xs in
   // Memory safety
   B.live h x.b /\
   B.disjoint x.b xs /\
   // Specification
   B.len x.b = x.total_length /\
   x.first <=^ x.total_length /\
   Seq.equal l (B.as_seq h (B.gsub x.b x.first (x.total_length -^ x.first))))

/// A predicate stating that l is the empty sequence.
let emp #a (l:Seq.seq a) =
  Seq.equal l Seq.createEmpty

/// A predicate stating that l occupies all the space in x.
let full #a h (l:Seq.seq a) (x: t a) =
  Seq.length l == U32.v (deref h x).total_length

/// Two specialized helpers you will need.
let cons #a e (l:Seq.seq a) =
  Seq.cons e l

let nil #a : Seq.seq a = Seq.createEmpty #a

/// Similarly, two accessors to facilite that rest of this exercise.
let head #a (l:Seq.seq a {~(emp l)}) =
  Seq.head l

let tail #a (l:Seq.seq a {~(emp l)}) =
  Seq.tail l

/// Your goal is now to write suitable pre- and post-conditions for this
/// function, along with its body. Start with the pre-condition: what is the
/// predicate that will allow us to always pop an element off the front of the
/// list? Then, provide a suitable post-condition that captures both the memory
/// safety and the semantics of the function.
let pop #a (l:Seq.seq a) (x: t a): Stack a
  (requires fun h -> True)
  (ensures fun h0 r h1 -> True)
=
  admit ()

/// Similar thing with push.
let push #a (l:Seq.seq a) (x: t a) (e:a) : Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)
=
  admit ()

unfold inline_for_extraction
let malloc #a (init: a) len = B.malloc #a HS.root init len

/// Finally, the create function. Find a suitable pre-condition, and reflect the
/// semantics and memory changes in the post-condition.
let create #a (def:a) (len:U32.t) : ST (t a)
  (requires fun h -> True)
  (ensures fun h0 r h1 -> True)
=
  admit ()

/// As a sanity check, this main function ought to type-check once you've removed
/// all the admits. Then, try compiling this code with:
///
/// krml -no-prefix FiniteList FiniteList.fst -add-include '"kremlin/prims_int.h"'
/// 
/// Once you replace sequences with erased sequences, the -add-include
/// argument will become optional.
let main (): St Int32.t =
  let l = create 1l 120ul in
  push Seq.createEmpty l 0l;
  pop FStar.Seq.(cons 0l createEmpty) l

