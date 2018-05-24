module Solution.FiniteListWithErasure

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
let repr #a (h: HS.mem) (xs: t a) (l:Ghost.erased (Seq.seq a)) =
  let open FStar.UInt32 in
  B.live h xs /\
  (let x = deref h xs in
   // Memory safety
   B.live h x.b /\
   B.disjoint x.b xs /\
   // Specification
   B.len x.b = x.total_length /\
   x.first <=^ x.total_length /\
   Seq.equal (Ghost.reveal l) (B.as_seq h (B.gsub x.b x.first (x.total_length -^ x.first))))

/// A predicate stating that l is the empty sequence.
let emp #a (l:Ghost.erased (Seq.seq a)) =
  Seq.equal (Ghost.reveal l) Seq.createEmpty

/// A predicate stating that l occupies all the space in x.
let full #a h (l:Ghost.erased (Seq.seq a)) (x: t a) =
  Seq.length (Ghost.reveal l) == U32.v (deref h x).total_length

/// We are using computationally-irrelevant sequences; two helpers to construct
/// such sequences, to save the user the trouble of writing hide / reveal.
let cons #a e (l:Ghost.erased (Seq.seq a)) =
  Ghost.hide (Seq.cons e (Ghost.reveal l))

let nil #a : Ghost.erased (Seq.seq a) = Ghost.hide (Seq.createEmpty #a)

/// Similarly, two accessors operating on ghost sequences.
let head #a (l:Ghost.erased (Seq.seq a) {~(emp l)}) =
  Seq.head (Ghost.reveal l)

let tail #a (l:Ghost.erased (Seq.seq a) {~(emp l)}) =
  Ghost.hide (Seq.tail (Ghost.reveal l))

/// Your goal is now to write suitable pre- and post-conditions for this
/// function, along with its body. Start with the pre-condition: what is the
/// predicate that will allow us to always pop an element off the front of the
/// list? Then, provide a suitable post-condition that captures both the memory
/// safety and the semantics of the function.
let pop #a (l:Ghost.erased (Seq.seq a)) (x: t a): Stack a
  (requires fun h -> ~(emp l) /\ repr h x l)
  (ensures fun h0 r h1 ->
            repr h1 x (tail l)
         /\  r == head l
         /\  modifies (loc_union (loc_buffer x)
                                (loc_buffer (deref h0 x).b)) h0 h1)
= let v = !* x in
  let res : a = v.b.(v.first) in
  let next = v.first +^ 1ul in
  x *= {v with first=next};
  res
  
/// Similar thing with push.
let push #a (l:Ghost.erased (Seq.seq a)) (x: t a) (e:a) : Stack unit
  (requires fun h -> ~(full h l x) /\ repr h x l)
  (ensures fun h0 _ h1 ->
            repr h1 x (cons e l)
         /\  modifies (loc_union (loc_buffer x)
                                (loc_buffer (deref h0 x).b)) h0 h1)
= let v = !* x in
  let next = v.first -^ 1ul in
  v.b.(next) <- e;
  x *= {v with first=next}

unfold inline_for_extraction
let malloc #a (init: a) len = B.malloc #a HS.root init len

/// Finally, the create function. Find a suitable pre-condition, and reflect the
/// semantics and memory changes in the post-condition.
let create #a (def:a) (len:U32.t) : ST (t a)
  (requires fun h -> len <> 0ul)
  (ensures fun h0 r h1 ->
            repr h1 r nil
          /\ (deref h1 r).total_length = len
          /\ modifies loc_none h0 h1)
 = let buf = {
       b = malloc def len;
       first = len;
       total_length = len
   } in
   B.malloc FStar.Monotonic.HyperHeap.root buf 1ul

module I32 = FStar.Int32
let main (): St I32.t =
  let l = create 1l 120ul in
  push nil l 0l;
  pop (cons 0l nil) l 
