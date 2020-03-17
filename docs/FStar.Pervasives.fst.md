# FStar.Pervasives

```fstar
module FStar.Pervasives
```

This is a file from the core library, dependencies must be explicit

```fstar
open Prims
include FStar.Pervasives.Native
```

> This module is implicitly opened in the scope of all other
> modules.
>
> It provides several basic definitions in F* that are common to
> most programs. Broadly, these include:
>
> - Utility types and functions, like [id], [either], dependent
>   tuples, etc.
>
> - Utility effect definitions, including [DIV] for divergence,
>   [EXN] of exceptions, [STATE_h] a template for state, and (the
>   poorly named) [ALL_h] which combines them all.
>
> - Some utilities to control proofs, e.g., inversion of inductive
>   type definitions.
>
> - Built-in attributes that can be used to decorate definitions and
>   trigger various kinds of special treatments for those
>   definitions.

#### id

The polymorphic identity function

```fstar
unfold
let id (#a: Type) (x: a) : a = x
```

#### trivial_pure_post

Trivial postconditions for the `PURE` effect

```fstar
unfold
let trivial_pure_post (a: Type) : pure_post a = fun _ -> True
```

#### ambient

Sometimes it is convenient to explicit introduce nullary symbols
into the ambient context, so that SMT can appeal to their definitions
even when they are no mentioned explicitly in the program, e.g., when
needed for triggers.

```fstar
abstract
let ambient (#a: Type) (x: a) = True
```

Use `intro_ambient t` for that.
See, e.g., LowStar.Monotonic.Buffer.fst and its usage there for loc_none

#### intro_ambient

cf. [`ambient`](#ambient), above

```fstar
abstract
let intro_ambient (#a: Type) (x: a) : squash (ambient x) = ()
```

> The [DIV] effect for divergent computations

#### DIV

The effect of divergence: from a specificational perspective it is
identical to PURE, however the specs are given a partial
correctness interpretation. Computations with the [`DIV`](#DIV) effect may
not terminate.

```fstar
new_effect DIV = PURE
```

`PURE` computations can be silently promoted for use in a [`DIV`](#DIV) context

```fstar
sub_effect PURE ~> DIV { lift_wp = purewp_id }
```

#### Div

[`Div`](#Div) is the Hoare-style counterpart of the wp-indexed [`DIV`](#DIV)

```fstar
effect Div (a: Type) (pre: pure_pre) (post: pure_post' a pre) =
  DIV a (fun (p: pure_post a) -> pre /\ (forall a. post a ==> p a))
```

#### Dv

[`Dv`](#Dv) is the instance of [`DIV`](#DIV) with trivial pre- and postconditions

```fstar
effect Dv (a: Type) = DIV a (fun (p: pure_post a) -> (forall (x: a). p x))
```

#### EXT

We use the [`EXT`](#EXT) effect to underspecify external system calls
as being impure but having no observable effect on the state

```fstar
effect EXT (a: Type) = Dv a
```

> The [STATE_h] effect template for stateful computations, generic
> in the type of the state.
>
> Note, [STATE_h] is itself not a computation type in F*, since it
> is parameterized by the type of heap. However, instantiations of
> [STATE_h] with specific types of the heap are computation
> types. See, e.g., [FStar.ST] for such instantiations.
>
> Weakest preconditions for stateful computations transform
> [st_post_h] postconditions to [st_pre_h] preconditions. Both are
> parametric in the type of the state, here denoted by the
> [heap:Type] variable.

#### st_pre_h

Preconditions are predicates on the `heap`

```fstar
let st_pre_h (heap: Type) = heap -> GTot Type0
```

#### st_post_h'

Postconditions relate `a`-typed results to the final `heap`, here
refined by some pure proposition `pre`, typically instantiated to
the precondition applied to the initial `heap`

```fstar
let st_post_h' (heap a pre: Type) = a -> _: heap{pre} -> GTot Type0
```

#### st_post_h

Postconditions without refinements

```fstar
let st_post_h (heap a: Type) = st_post_h' heap a True
```

#### st_wp_h

The type of the main WP-transformer for stateful comptuations

```fstar
let st_wp_h (heap a: Type) = st_post_h heap a -> Tot (st_pre_h heap)
```

#### st_return

Returning a value does not transform the state

```fstar
unfold
let st_return (heap a: Type) (x: a) (p: st_post_h heap a) = p x
```

#### st_bind_wp

Sequential composition of stateful WPs

```fstar
unfold
let st_bind_wp
      (heap: Type)
      (r1: range)
      (a b: Type)
      (wp1: st_wp_h heap a)
      (wp2: (a -> GTot (st_wp_h heap b)))
      (p: st_post_h heap b)
      (h0: heap)
     = wp1 (fun a h1 -> wp2 a p h1) h0
```

#### st_if_then_else

Branching for stateful WPs

```fstar
unfold
let st_if_then_else
      (heap a p: Type)
      (wp_then wp_else: st_wp_h heap a)
      (post: st_post_h heap a)
      (h0: heap)
     = l_ITE p (wp_then post h0) (wp_else post h0)
```

#### st_ite_wp

As with `PURE` the `ite_wp` combinator names the postcondition as
`k` to avoid duplicating it.

```fstar
unfold
let st_ite_wp (heap a: Type) (wp: st_wp_h heap a) (post: st_post_h heap a) (h0: heap) =
  forall (k: st_post_h heap a).
    (forall (x: a) (h: heap). {:pattern (guard_free (k x h))} post x h ==> k x h) ==> wp k h0
```

#### st_stronger

Subsumption for stateful WPs

```fstar
unfold
let st_stronger (heap a: Type) (wp1 wp2: st_wp_h heap a) =
  (forall (p: st_post_h heap a) (h: heap). wp1 p h ==> wp2 p h)
```

#### st_close_wp

Closing the scope of a binder within a stateful WP

```fstar
unfold
let st_close_wp (heap a b: Type) (wp: (b -> GTot (st_wp_h heap a))) (p: st_post_h heap a) (h: heap) =
  (forall (b: b). wp b p h)
```

#### st_trivial

Applying a stateful WP to a trivial postcondition

```fstar
unfold
let st_trivial (heap a: Type) (wp: st_wp_h heap a) = (forall h0. wp (fun r h1 -> True) h0)
```

#### STATE_h

Introducing a new effect template [`STATE_h`](#STATE_h)

```fstar
new_effect {
  STATE_h (heap: Type) : result: Type -> wp: st_wp_h heap result -> Effect
  with
    return_wp = st_return heap
  ; bind_wp = st_bind_wp heap
  ; if_then_else = st_if_then_else heap
  ; ite_wp = st_ite_wp heap
  ; stronger = st_stronger heap
  ; close_wp = st_close_wp heap
  ; trivial = st_trivial heap
}
```

> The [EXN] effect for computations that may raise exceptions or
> fatal errors
>
> Weakest preconditions for stateful computations transform
> [ex_post] postconditions (predicates on [result]s) to [ex_pre]
> precondition propositions.

#### result

Normal results are represented using `V x`.
Handleable exceptions are represented `E e`.
Fatal errors are `Err msg`.

```fstar
noeq
type result (a: Type) =
  | V : v: a -> result a
  | E : e: exn -> result a
  | Err : msg: string -> result a
```

#### ex_pre

Exceptional preconditions are just propositions

```fstar
let ex_pre = Type0
```

#### ex_post'

Postconditions on results refined by a precondition

```fstar
let ex_post' (a pre: Type) = _: result a {pre} -> GTot Type0
```

#### ex_post

Postconditions on results

```fstar
let ex_post (a: Type) = ex_post' a True
```

#### ex_wp

Exceptions WP-predicate transformers

```fstar
let ex_wp (a: Type) = ex_post a -> GTot ex_pre
```

#### ex_return

Returning a value `x` normally promotes it to the `V x` result

```fstar
unfold
let ex_return (a: Type) (x: a) (p: ex_post a) : GTot Type0 = p (V x)
```

#### ex_bind_wp

Sequential composition of exception-raising code requires case analysing
the result of the first computation before "running" the second one

```fstar
unfold
let ex_bind_wp (r1: range) (a b: Type) (wp1: ex_wp a) (wp2: (a -> GTot (ex_wp b))) (p: ex_post b)
    : GTot Type0 =
  forall (k: ex_post b).
    (forall (rb: result b). {:pattern (guard_free (k rb))} p rb ==> k rb) ==>
    (wp1 (function
          | V ra1 -> wp2 ra1 k
          | E e -> k (E e)
          | Err m -> k (Err m)))
```

#### ex_if_then_else

As for other effects, branching in [`ex_wp`](#ex_wp) appears in two forms.
First, a simple case analysis on `p`

```fstar
unfold
let ex_if_then_else (a p: Type) (wp_then wp_else: ex_wp a) (post: ex_post a) =
  l_ITE p (wp_then post) (wp_else post)
```

#### ex_ite_wp

Naming continuations for use with branching

```fstar
unfold
let ex_ite_wp (a: Type) (wp: ex_wp a) (post: ex_post a) =
  forall (k: ex_post a).
    (forall (rb: result a). {:pattern (guard_free (k rb))} post rb ==> k rb) ==> wp k
```

#### ex_stronger

Subsumption for exceptional WPs

```fstar
unfold
let ex_stronger (a: Type) (wp1 wp2: ex_wp a) = (forall (p: ex_post a). wp1 p ==> wp2 p)
```

#### ex_close_wp

Closing the scope of a binder for exceptional WPs

```fstar
unfold
let ex_close_wp (a b: Type) (wp: (b -> GTot (ex_wp a))) (p: ex_post a) = (forall (b: b). wp b p)
```

#### ex_trivial

Applying a computation with a trivial poscondition

```fstar
unfold
let ex_trivial (a: Type) (wp: ex_wp a) = wp (fun r -> True)
```

#### EXN

Introduce a new effect for [`EXN`](#EXN)

```fstar
new_effect {
  EXN : result: Type -> wp: ex_wp result -> Effect
  with
    return_wp = ex_return
  ; bind_wp = ex_bind_wp
  ; if_then_else = ex_if_then_else
  ; ite_wp = ex_ite_wp
  ; stronger = ex_stronger
  ; close_wp = ex_close_wp
  ; trivial = ex_trivial
}
```

#### Exn

A Hoare-style abbreviation for EXN

```fstar
effect Exn (a: Type) (pre: ex_pre) (post: ex_post' a pre) =
  EXN a (fun (p: ex_post a) -> pre /\ (forall (r: result a). post r ==> p r))
```

#### lift_div_exn

We include divergence in exceptions.

```fstar
unfold
let lift_div_exn (a: Type) (wp: pure_wp a) (p: ex_post a) = wp (fun a -> p (V a))
sub_effect DIV ~> EXN { lift_wp = lift_div_exn }
```

NOTE: BE WARNED, CODE IN THE [`EXN`](#EXN) EFFECT IS ONLY CHECKED FOR
PARTIAL CORRECTNESS

#### Ex

A variant of [`Exn`](#Exn) with trivial pre- and postconditions

```fstar
effect Ex (a: Type) = Exn a True (fun v -> True)
```

> The [ALL_h] effect template for computations that may diverge,
> raise exceptions or fatal errors, and uses a generic state.
>
> Note, this effect is poorly named, particularly as F* has since
> gained many more user-defined effect. We no longer have an effect
> that includes all others.
>
> We might rename this in the future to something like [StExnDiv_h].
>
> We layer state on top of exceptions, meaning that raising an
> exception does not discard the state.
>
> As with [STATE_h], [ALL_h] is not a computation type, though its
> instantiation with a specific type of [heap] (in FStar.All) is.

#### all_pre_h

[`all_pre_h`](#all_pre_h) is a predicate on the initial state

```fstar
let all_pre_h (h: Type) = h -> GTot Type0
```

#### all_post_h'

Postconditions relate [`result`](#result)s to final `heap`s refined by a precondition

```fstar
let all_post_h' (h a pre: Type) = result a -> _: h{pre} -> GTot Type0
```

#### all_post_h

A variant of [`all_post_h'`](#all_post_h') without the precondition refinement

```fstar
let all_post_h (h a: Type) = all_post_h' h a True
```

#### all_wp_h

WP predicate transformers for the `All_h` effect template

```fstar
let all_wp_h (h a: Type) = all_post_h h a -> Tot (all_pre_h h)
```

#### all_return

Returning a value `x` normally promotes it to the `V x` result
without touching the `heap`

```fstar
unfold
let all_return (heap a: Type) (x: a) (p: all_post_h heap a) = p (V x)
```

#### all_bind_wp

Sequential composition for [`ALL_h`](#ALL_h) is like [`EXN`](#EXN): case analysis of
the exceptional result before "running" the continuation

```fstar
unfold
let all_bind_wp
      (heap: Type)
      (r1: range)
      (a b: Type)
      (wp1: all_wp_h heap a)
      (wp2: (a -> GTot (all_wp_h heap b)))
      (p: all_post_h heap b)
      (h0: heap)
    : GTot Type0 =
  wp1 (fun ra h1 ->
        (match ra with
          | V v -> wp2 v p h1
          | E e -> p (E e) h1
          | Err msg -> p (Err msg) h1))
    h0
```

#### all_if_then_else

Case analysis in [`ALL_h`](#ALL_h)

```fstar
unfold
let all_if_then_else
      (heap a p: Type)
      (wp_then wp_else: all_wp_h heap a)
      (post: all_post_h heap a)
      (h0: heap)
     = l_ITE p (wp_then post h0) (wp_else post h0)
```

#### all_ite_wp

Naming postcondition for better sharing in [`ALL_h`](#ALL_h)

```fstar
unfold
let all_ite_wp (heap a: Type) (wp: all_wp_h heap a) (post: all_post_h heap a) (h0: heap) =
  forall (k: all_post_h heap a).
    (forall (x: result a) (h: heap). {:pattern (guard_free (k x h))} post x h ==> k x h) ==> wp k h0
```

#### all_stronger

Subsumption in [`ALL_h`](#ALL_h)

```fstar
unfold
let all_stronger (heap a: Type) (wp1 wp2: all_wp_h heap a) =
  (forall (p: all_post_h heap a) (h: heap). wp1 p h ==> wp2 p h)
```

#### all_close_wp

Closing a binder in the scope of an [`ALL_h`](#ALL_h) wp

```fstar
unfold
let all_close_wp
      (heap a b: Type)
      (wp: (b -> GTot (all_wp_h heap a)))
      (p: all_post_h heap a)
      (h: heap)
     = (forall (b: b). wp b p h)
```

#### all_trivial

Applying an [`ALL_h`](#ALL_h) wp to a trivial postcondition

```fstar
unfold
let all_trivial (heap a: Type) (wp: all_wp_h heap a) = (forall (h0: heap). wp (fun r h1 -> True) h0)
```

#### ALL_h

Introducing the [`ALL_h`](#ALL_h) effect template

```fstar
new_effect {
  ALL_h (heap: Type) : a: Type -> wp: all_wp_h heap a -> Effect
  with
    return_wp = all_return heap
  ; bind_wp = all_bind_wp heap
  ; if_then_else = all_if_then_else heap
  ; ite_wp = all_ite_wp heap
  ; stronger = all_stronger heap
  ; close_wp = all_close_wp heap
  ; trivial = all_trivial heap
}
```

#### inversion

Controlling inversions of inductive type

```fstar
let inversion (a: Type) = True
```

Given a value of an inductive type `v:t`, where `t = A | B`, the SMT
solver can only prove that `v=A \/ v=B` by _inverting_ `t`. This
inversion is controlled by the `ifuel` setting, which usually limits
the recursion depth of the number of such inversions that the solver
can perform.

The [`inversion`](#inversion) predicate below is a way to circumvent the
`ifuel`-based restrictions on inversion depth. In particular, if the
`inversion t` is available in the SMT solver's context, it is free to
invert `t` infinitely, regardless of the `ifuel` setting.

Be careful using this, since it explicitly subverts the `ifuel`
setting. If used unwisely, this can lead to very poor SMT solver
performance.

#### allow_inversion

To introduce `inversion t` in the SMT solver's context, call
`allow_inverson t`.

```fstar
let allow_inversion (a: Type) : Pure unit (requires True) (ensures (fun x -> inversion a)) = ()
```

#### invertOption

Since the `option` type is so common, we always allow inverting
options, regardless of `ifuel`

```fstar
let invertOption (a: Type)
    : Lemma (requires True) (ensures (forall (x: option a). None? x \/ Some? x)) [SMTPat (option a)] =
  allow_inversion (option a)
```

#### either

Values of type `a` or type `b`

```fstar
type either a b =
  | Inl : v: a -> either a b
  | Inr : v: b -> either a b
```

#### dfst

Projections for the components of a dependent pair

```fstar
val dfst: #a: Type -> #b: (a -> GTot Type) -> dtuple2 a b -> Tot a
let dfst #a #b t = Mkdtuple2?._1 t
```

```fstar
val dsnd (#a: Type) (#b: (a -> GTot Type)) (t: dtuple2 a b) : Tot (b (Mkdtuple2?._1 t))
let dsnd #a #b t = Mkdtuple2?._2 t
```

#### dtuple3

Dependent triples, with sugar `x:a & y:b x & c x y`

```fstar
unopteq
type dtuple3 (a: Type) (b: (a -> GTot Type)) (c: (x: a -> b x -> GTot Type)) =
  | Mkdtuple3 : _1: a -> _2: b _1 -> _3: c _1 _2 -> dtuple3 a b c
```

#### dtuple4

Dependent quadruples, with sugar `x:a & y:b x & z:c x y & d x y z`

```fstar
unopteq
type dtuple4
  (a: Type) (b: (x: a -> GTot Type)) (c: (x: a -> b x -> GTot Type))
  (d: (x: a -> y: b x -> z: c x y -> GTot Type))
  = | Mkdtuple4 : _1: a -> _2: b _1 -> _3: c _1 _2 -> _4: d _1 _2 _3 -> dtuple4 a b c d
```

#### ignore

Explicitly discarding a value

```fstar
let ignore (#a: Type) (x: a) : Tot unit = ()
```

#### rec

In a context where `false` is provable, you can prove that any
type `a` is inhabited.

```fstar
irreducible
let rec false_elim (#a: Type) (u: unit{False}) : Tot a = false_elim ()
```

There are many proofs of this fact in F*. Here, we build an
infinitely looping function, since the termination check succeeds
in a `False` context.

> Attributes:
>
> An attribute is any F* term.
>
> Attributes are desugared and checked for being well-scoped. But,
> they are not type-checked.
>
> It is associated with a definition using the [[@attribute]]
> notation, just preceding the definition.

#### __internal_ocaml_attributes

We collect several internal ocaml attributes into a single
inductive type.

```fstar
type __internal_ocaml_attributes =
  | PpxDerivingShow
  | PpxDerivingShowConstant of string (* Generate [@@ deriving show ] on the resulting OCaml type *)
  | PpxDerivingYoJson (* Similar, but for constant printers. *)
  | CInline (* Generate [@@ deriving yojson ] on the resulting OCaml type *)
```

This may be unnecessary. In the future, we are likely to flatten
this definition into several definitions of abstract top-level
names.

An example:

 ```fstar
`@ CInline ` let f x = UInt32.(x +%^ 1)
  ```

is extracted to C by KReMLin to a C definition tagged with the
`inline` qualifier.

KreMLin-only: generates a C "inline" attribute on the resulting
    * function declaration.
KreMLin-only: forces KreMLin to inline the function at call-site; this is
    * deprecated and the recommended way is now to use F*'s
    * [inline_for_extraction], which now also works for stateful functions.
KreMLin-only: instructs KreMLin to heap-allocate any value of this
    * data-type; this requires running with a conservative GC as the
    * allocations are not freed.
KreMLin-only: attach a comment to the declaration. Note that using F*-doc
    * syntax automatically fills in this attribute.
KreMLin-only: verbatim C code to be prepended to the declaration.
    * Multiple attributes are valid and accumulate, separated by newlines.
KreMLin-only: indicates that the parameter with that name is to be marked
    * as C const.  This will be checked by the C compiler, not by KreMLin or F*.
    *
    * This is deprecated and doesn't work as intended. Use
    * LowStar.ConstBuffer.fst instead!
KreMLin-only: for types that compile to struct types (records and
    * inductives), indicate that the header file should only contain a forward
    * declaration, which in turn forces the client to only ever use this type
    * through a pointer.
KreMLin-only: for a top-level `let v = e`, compile as a macro

```fstar
| Substitute
| Gc
| Comment of string
| CPrologue of string
| CEpilogue of string
| CConst of string (* Ibid. *)
| CCConv of string
| CAbstractStruct (* A calling convention for C, one of stdcall, cdecl, fastcall *)
| CIfDef
| CMacro (* KreMLin-only: on a given `val foo`, compile if foo with #ifdef. *)
```

#### inline_let:unit

The `inline_let` attribute on a local let-binding, instructs the
extraction pipeline to inline the definition. This may be both to
avoid generating unnecessary intermediate variables, and also to
enable further partial evaluation. Note, use this with care, since
inlining all lets can lead to an exponential blowup in code
size.

```fstar
irreducible
let inline_let:unit = ()
```

#### rename_let

The [`rename_let`](#rename_let) attribute support a form of metaprogramming for
the names of let-bound variables used in extracted code.

```fstar
irreducible
let rename_let (new_name: string) : unit = ()
```

This is useful, particularly in conjunction with partial
evaluation, to ensure that names reflect their usage context.

See examples/micro-benchmarks/Renaming*.fst

#### plugin

The [`plugin`](#plugin) attribute is used in conjunction with native
compilation of F* components, accelerating their reduction
relative to the default strategy of just interpreting them.

```fstar
irreducible
let plugin (x: int) : unit = ()
```

See examples/native_tactics for several examples.

#### tcnorm:unit

An attribute to mark things that the typechecker should *first*
elaborate and typecheck, but unfold before verification.

```fstar
irreducible
let tcnorm:unit = ()
```

#### must_erase_for_extraction:unit

We erase all ghost functions and unit-returning pure functions to
`()` at extraction. This creates a small issue with abstract
types. Consider a module that defines an abstract type `t` whose
(internal) definition is `unit` and also defines `f: int -> t`. `f`
would be erased to be just `()` inside the module, while the
client calls to `f` would not, since `t` is abstract. To get
around this, when extracting interfaces, if we encounter an
abstract type, we tag it with this attribute, so that
extraction can treat it specially.

```fstar
irreducible
let must_erase_for_extraction:unit = ()
```

Note, since the use of cross-module inlining (the `--cmi` option),
this attribute is no longer necessary. We retain it for legacy,
but will remove it in the future.

#### dm4f_bind_range:unit

This attribute is used with the Dijkstra Monads for Free
construction to track position information in generated VCs

```fstar
let dm4f_bind_range:unit = ()
```

#### expect_failure

When attached a top-level definition, the typechecker will succeed
if and only if checking the definition results in an error. The
error number list is actually OPTIONAL. If present, it will be
checked that the definition raises exactly those errors in the
specified multiplicity, but order does not matter.

```fstar
irreducible
let expect_failure (errs: list int) : unit = ()
```

#### expect_lax_failure

When --lax is present, with the previous attribute since some
definitions only fail when verification is turned on. With this
attribute, one can ensure that a definition fails while lax-checking
too. Same semantics as above, but lax mode will be turned on for the
definition.

```fstar
irreducible
let expect_lax_failure (errs: list int) : unit = ()
```

#### tcdecltime:unit

Print the time it took to typecheck a top-level definition

```fstar
irreducible
let tcdecltime:unit = ()
```

#### assume_strictly_positive:unit

**THIS ATTRIBUTE IS AN ESCAPE HATCH AND CAN BREAK SOUNDNESS**

```fstar
irreducible
let assume_strictly_positive:unit = ()
```

**USE WITH CARE**

The positivity check for inductive types stops at abstraction
boundaries. This results in spurious errors about positivity,
e.g., when defining types like `type t = ref (option t)` By adding
this attribute to a declaration of a top-level name positivity
checks on applications of that name are admitted.  See, for
instance, FStar.Monotonic.Heap.mref We plan to decorate binders of
abstract types with polarities to allow us to check positivity
across abstraction boundaries and will eventually remove this
attribute.

#### unifier_hint_injective:unit

This attribute is to be used as a hint for the unifier.  A
function-typed symbol `t` marked with this attribute will be treated
as being injective in all its arguments by the unifier.  That is,
given a problem `t a1..an =?= t b1..bn` the unifier will solve it by
proving `ai =?= bi` for all `i`, without trying to unfold the
definition of `t`.

```fstar
irreducible
let unifier_hint_injective:unit = ()
```

#### strict_on_arguments

This attribute is used to control the evaluation order
and unfolding strategy for certain definitions.

```fstar
irreducible
let strict_on_arguments (x: list int) : unit = ()
```

 In particular, given
    ```fstar
`@(strict_on_arguments `1;2`)`
let f x0 (x1:list x0) (x1:option x0) = e
    ```

An application `f e0 e1 e2` is reduced by the normalizer by:

    1. evaluating `e0 ~>* v0, e1 ~>* v1, e2 ~>* v2`

    2 a.
       If, according to the positional arguments `1;2`,
       if v1 and v2 have constant head symbols
             (e.g., v1 = Cons _ _ _, and v2 = None _)
      then `f` is unfolded to `e` and reduced as
        e`v0/x0``v1/x1``v2/x2`

    2 b.

     Otherwise, `f` is not unfolded and the term is `f e0 e1 e2`
     reduces to `f v0 v1 v2`.

#### erasable:unit

This attribute can be added to an inductive type definition,
indicating that it should be erased on extraction to `unit`.

```fstar
irreducible
let erasable:unit = ()
```

However, any pattern matching on the inductive type results
in a `Ghost` effect, ensuring that computationally relevant
code cannot rely on the values of the erasable type.

See examples/micro-benchmarks/Erasable.fst, for examples.  Also
see https://github.com/FStarLang/FStar/issues/1844

> Controlling normalization

#### normalize_term

In any invocation of the F* normalizer, every occurrence of
`normalize_term e` is reduced to the full normal for of `e`.

```fstar
abstract
let normalize_term (#a: Type) (x: a) : a = x
```

#### normalize

In any invocation of the F* normalizer, every occurrence of
`normalize e` is reduced to the full normal for of `e`.

```fstar
abstract
let normalize (a: Type0) : Type0 = a
```

#### norm_step

Value of [`norm_step`](#norm_step) are used to enable specific normalization
steps, controlling how the normalizer reduces terms.

```fstar
abstract noeq
type norm_step =
  | Simpl // Logical simplification, e.g., [P /\ True ~> P]
  | Weak // Weak reduction: Do not reduce under binders
  | HNF // Head normal form
  | Primops // Reduce primitive operators, e.g., [1 + 1 ~> 2]
  | Delta // Unfold all non-recursive definitions
  | Zeta // Unroll recursive calls
  | Iota // Reduce case analysis (i.e., match)
  | NBE // Use normalization-by-evaluation, instead of interpretation (experimental)
  | Reify // Reify effectful definitions into their representations
  | UnfoldOnly : list string -> norm_step // Unlike Delta, unfold definitions for only the given
```

We wrap the inductive type with helpers (below), so we don't
expose the actual inductive

names, each string is a fully qualified name
like `A.M.f`
idem

```fstar
| UnfoldFully : list string -> norm_step
| UnfoldAttr : list string -> norm_step // Unfold definitions marked with the given attributes
```

#### simplify:norm_step

Logical simplification, e.g., `P /\ True ~> P`

```fstar
abstract
let simplify:norm_step = Simpl
```

#### weak:norm_step

Weak reduction: Do not reduce under binders

```fstar
abstract
let weak:norm_step = Weak
```

#### hnf:norm_step

Head normal form

```fstar
abstract
let hnf:norm_step = HNF
```

#### primops:norm_step

Reduce primitive operators, e.g., `1 + 1 ~> 2`

```fstar
abstract
let primops:norm_step = Primops
```

#### delta:norm_step

Unfold all non-recursive definitions

```fstar
abstract
let delta:norm_step = Delta
```

#### zeta:norm_step

Unroll recursive calls

```fstar
abstract
let zeta:norm_step = Zeta
```

#### iota:norm_step

Reduce case analysis (i.e., match)

```fstar
abstract
let iota:norm_step = Iota
```

#### nbe:norm_step

Use normalization-by-evaluation, instead of interpretation (experimental)

```fstar
abstract
let nbe:norm_step = NBE
```

#### reify_:norm_step

Reify effectful definitions into their representations

```fstar
abstract
let reify_:norm_step = Reify
```

#### delta_only

Unlike `delta`, unfold definitions for only the names in the given
list. Each string is a fully qualified name like `A.M.f`

```fstar
abstract
let delta_only (s: list string) : norm_step = UnfoldOnly s
```

#### delta_fully

Unfold definitions for only the names in the given list, but
unfold each definition encountered after unfolding as well.

```fstar
abstract
let delta_fully (s: list string) : norm_step = UnfoldFully s
```

For example, given

  ```fstar
let f0 = 0
let f1 = f0 + 1
  ```

`norm `delta_only ``%f1`` f1` will reduce to `f0 + 1`.
`norm `delta_fully ``%f1`` f1` will reduce to `0 + 1`.

Each string is a fully qualified name like `A.M.f`, typically
constructed using a quotation, as in the example above.

#### delta_attr

Rather than mention a symbol to unfold by name, it can be
convenient to tag a collection of related symbols with a common
attribute and then to ask the normalizer to reduce them all.

```fstar
abstract
let delta_attr (s: list string) : norm_step = UnfoldAttr s
```

 For example, given:

   ```fstar
irreducible let my_attr = ()

`@my_attr`
let f0 = 0

`@my_attr`
let f1 = f0 + 1
   ```

```fstarnorm [delta_attr [`%my_attr]] f1```

will reduce to `0 + 1`.

#### norm

`norm s e` requests normalization of `e` with the reduction steps
`s`.

```fstar
abstract
let norm (s: list norm_step) (#a: Type) (x: a) : a = x
```

#### assert_norm

`assert_norm p` reduces `p` as much as possible and then asks the
SMT solver to prove the reduct, concluding `p`

```fstar
abstract
val assert_norm (p: Type) : Pure unit (requires (normalize p)) (ensures (fun _ -> p))
let assert_norm p = ()
```

#### normalize_term_spec

Sometimes it is convenient to introduce an equation between a term
and its normal form in the context.

```fstar
let normalize_term_spec (#a: Type) (x: a) : Lemma (normalize_term #a x == x) = ()
```

#### normalize_spec

Like [`normalize_term_spec`](#normalize_term_spec), but specialized to `Type0`

```fstar
let normalize_spec (a: Type0) : Lemma (normalize a == a) = ()
```

#### norm_spec

Like [`normalize_term_spec`](#normalize_term_spec), but with specific normalization steps

```fstar
let norm_spec (s: list norm_step) (#a: Type) (x: a) : Lemma (norm s #a x == x) = ()
```

#### reveal_opaque

Use the following to expose an `"opaque_to_smt"` definition to the
solver as: `reveal_opaque (`%defn) defn`

```fstar
let reveal_opaque (s: string) = norm_spec [delta_only [s]]
```

#### singleton

Pure and ghost inner let bindings are now always inlined during
the wp computation, if: the return type is not unit and the head
symbol is not marked irreducible.

```fstar
irreducible
let singleton (#a: Type) (x: a) : (y: a{y == x}) = x
```

To circumvent this behavior, singleton can be used.
See the example usage in ulib/FStar.Algebra.Monoid.fst.

#### with_type

`with_type t e` is just an identity function, but it receives
special treatment in the SMT encoding, where in addition to being
an identity function, we have an SMT axiom:
`forall t e.{:pattern (with_type t e)} has_type (with_type t e) t`

```fstar
let with_type (#t: Type) (e: t) = e
```
