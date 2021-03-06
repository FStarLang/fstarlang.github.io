# FStar.Classical

```FStar
module FStar.Classical
```

> This module contains the standard primitives to manipulate proof goals containing classical logic.
> The proof goals manipulated are values of type `Type` or `Type0`. One can go from a goal of type
> `Type` to `Type0` by "squashing" it into an F* value of type unit having a refinmnent corresponding
> to the original goal.
>
> To produce a value of type `squash a`, the general method is to let-bind a unit value and annotate
> it with the type `squash a`, for instance:
>
> ```FStar
> let pf : squash (1 <> 0) = () in ...
> ```
>
> The F* typechecker will then proceed to proved the squashed property by typechecking the squashed
> value. To apply most of the lemmas here, you will have to let-bind or create auxiliary lemmas
> matching what the function expects to make F*'s unification mechanism work

## Witnesses

#### give_witness

Demonstrate the existence of a type from a value of that type.

```FStar
val give_witness (#a:Type) (_:a) : Lemma (ensures a)
```

Example:
```FStar
let x : n:nat{n <> 0} = 1 in
give_witness x
```

#### give_witness_from_squash

Demonstrate the existence of a type from a squashed value. See [`give_witness`](#give_witness).

```FStar
val give_witness_from_squash (#a:Type) (_:squash a) : Lemma (ensures a)
```

Example:
```FStar
let pf : squash(1+1 = 2) = () in
give_witness pf
```

#### get_equality

Produce equality as a `Type` if provable from context.

```FStar
val get_equality
  (#t:Type)
  (a b: t)
  : Pure (a == b)
    (requires (a == b))
    (ensures (fun _ -> True))
```

#### get_forall

Produce a `forall` property as a `Type` if provable from context.

```FStar
val get_forall
  (#a:Type)
  (p: a -> GTot Type0)
  : Pure (forall (x: a). p x)
    (requires (forall (x: a). p x))
    (ensures (fun _ -> True))
```

#### impl_to_arrow

Get an arrow from an implication. Converse is [`arrow_to_impl`](#arrow_to_impl).

```FStar
val impl_to_arrow (#a:Type0) (#b:Type0) (_:(a ==> b)) (_:squash a) :GTot (squash b)
```

#### arrow_to_impl

Get an implication from an arrow. Converse is [`impl_to_arrow`](#impl_to_arrow).

```FStar
val arrow_to_impl (#a:Type0) (#b:Type0) (_:(squash a -> GTot (squash b))) : GTot (a ==> b)
```

Example:
```FStar
arrow_to_impl #(foo) #(bar) (fun _ ->
  // proof of "bar", but now we have "foo" in context
)
```
can be used to prove `foo ==> bar`.

## Universal quantification

#### gtot_to_lemma

Introduce a property `p x` from a `GTot` function.

```FStar
val gtot_to_lemma (#a:Type) (#p:(a -> GTot Type)) ($_:(x:a -> GTot (p x))) (x:a) : Lemma (p x)
```

#### lemma_to_squash_gtot

Produce a squashed property as a `Type` from a lemma.

```FStar
val lemma_to_squash_gtot
  (#a:Type)
  (#p:(a -> GTot Type))
  ($_:(x:a -> Lemma (p x)))
  (x:a)
  : GTot (squash (p x))
```

> The following values are all variations on a same theme: proving a proposition `p` true for all `x` of type `a`.

#### forall_intro_gtot

Produce `forall` property as a `Type` from a `GTot` function. See [`lemma_forall_intro_gtot`](#lemma_forall_intro_gtot).

```FStar
val forall_intro_gtot
  (#a:Type)
  (#p:(a -> GTot Type))
  ($_:(x:a -> GTot (p x)))
  : Tot (squash (forall (x:a). p x))
```

#### lemma_forall_intro_gtot

Introduce a `forall` property into context from a `GTot` function.

```FStar
val lemma_forall_intro_gtot
  (#a:Type)
  (#p:(a -> GTot Type))
  ($_:(x:a -> GTot (p x)))
  : Lemma (forall (x:a). p x)
```

#### forall_intro_squash_gtot

Produce a squashed `forall` property as a `Type` from a `GTot` function. See `forall_intro_squash_gtot_join`.

```FStar
val forall_intro_squash_gtot
  (#a:Type)
  (#p:(a -> GTot Type))
  ($_:(x:a -> GTot (squash (p x))))
  : Tot (squash (forall (x:a). p x))
```

Produce a `forall` property as a `Type` from a `GTot` function.

This one seems more generally useful than the one above

```FStar
val forall_intro_squash_gtot_join
  (#a:Type)
  (#p:(a -> GTot Type))
  ($_:(x:a -> GTot (squash (p x))))
  : Tot (forall (x:a). p x)
```

#### forall_intro

Introduce a `forall` property into context from a lemma. See relevant useful [`move_requires`](#move_requires) to make this even more useful.

```FStar
val forall_intro (#a:Type) (#p:(a -> GTot Type)) ($_:(x:a -> Lemma (p x))) : Lemma (forall (x:a). p x)
```

Example:
```FStar
let aux x : Lemma (p x) =
    // proof of `p x`
in
forall_intro aux // and now we have `forall x. p x`
```

Example:
```FStar
let aux x : Lemma (requires (p x)) (ensures (q x)) =
    // proof of `q x` under assumption of `q x`
in
forall_intro (move_requires aux) // and now we have `forall x. p x ==> q x`
```

#### forall_intro_with_pat

Introduce a `forall` property with a pattern. See [`forall_intro`](#forall_intro).

```FStar
val forall_intro_with_pat (#a:Type) (#c: (x:a -> Type)) (#p:(x:a -> GTot Type0))
  ($pat: (x:a -> Tot (c x)))
  ($_: (x:a -> Lemma (p x)))
  : Lemma (forall (x:a).{:pattern (pat x)} p x)
```

#### forall_intro_sub

Introduce a `forall` property. Equivalent to [`forall_intro`](#forall_intro) except for lack of exact unification requirement `$`.

```FStar
val forall_intro_sub (#a:Type) (#p:(a -> GTot Type)) (_:(x:a -> Lemma (p x))) : Lemma (forall (x:a). p x)
```

#### forall_intro_2

Introduce a `forall` property over 2 variables. Similar to [`forall_intro`](#forall_intro).

```FStar
val forall_intro_2
  (#a:Type)
  (#b:(a -> Type))
  (#p:(x:a -> b x -> GTot Type0))
  ($_: (x:a -> y:b x -> Lemma (p x y)))
  : Lemma (forall (x:a) (y:b x). p x y)
```

Example: A useful way to use it with a lemma that has a non-trivial `requires` clause:
```FStar
let aux x y : Lemma (requires (p x y)) (ensures (q x y)) =
    // proof of `q x y` under assumption of `p x y`
in
let aux x = move_requires (aux x) in // notice only 1 argument (last argument is pointfree)
forall_intro aux // and now we have `forall x. p x y ==> q x y`
```

#### forall_intro_2_with_pat

[`forall_intro_2`](#forall_intro_2) with pattern.

```FStar
val forall_intro_2_with_pat
  (#a:Type)
  (#b:(a -> Type))
  (#c: (x:a -> y:b x -> Type))
  (#p:(x:a -> b x -> GTot Type0))
  ($pat: (x:a -> y:b x -> Tot (c x y)))
  ($_: (x:a -> y:b x -> Lemma (p x y)))
  : Lemma (forall (x:a) (y:b x).{:pattern (pat x y)} p x y)
```

#### forall_intro_3

[`forall_intro`](#forall_intro) for 3 variables.

```FStar
val forall_intro_3
  (#a:Type)
  (#b:(a -> Type))
  (#c:(x:a -> y:b x -> Type))
  (#p:(x:a -> y:b x -> z:c x y -> Type0))
  ($_: (x:a -> y:b x -> z:c x y -> Lemma (p x y z)))
  : Lemma (forall (x:a) (y:b x) (z:c x y). p x y z)
```

Example: Similar to [`forall_intro_2`](#forall_intro_2), we can use it for non-trivial `requires` clauses:
```FStar
let aux x y z : Lemma (requires (p x y z)) (ensures (q x y z)) =
    // proof of `q x y z` under assumption of `p x y z`
in
let aux x y = move_requires (aux x y) in
// notice only 2 arguments (last argument is pointfree)
forall_intro aux // and now we have `forall x. p x y z ==> q x y z`
```

#### forall_intro_3_with_pat

[`forall_intro_3`](#forall_intro_3) with pattern.

```FStar
val forall_intro_3_with_pat
  (#a:Type)
  (#b:(a -> Type))
  (#c: (x:a -> y:b x -> Type))
  (#d: (x:a -> y:b x -> z:c x y -> Type))
  (#p:(x:a -> y:b x -> z:c x y -> GTot Type0))
  ($pat: (x:a -> y:b x -> z:c x y -> Tot (d x y z)))
  ($_: (x:a -> y:b x -> z:c x y -> Lemma (p x y z)))
  : Lemma (forall (x:a) (y:b x) (z:c x y).{:pattern (pat x y z)} p x y z)
```

#### forall_intro_4

[`forall_intro`](#forall_intro) for 4 variables.

```FStar
val forall_intro_4
  (#a:Type)
  (#b:(a -> Type))
  (#c:(x:a -> y:b x -> Type))
  (#d:(x:a -> y:b x -> z:c x y -> Type))
  (#p:(x:a -> y:b x -> z:c x y -> w:d x y z -> Type0))
  ($_: (x:a -> y:b x -> z:c x y -> w:d x y z -> Lemma (p x y z w)))
  : Lemma (forall (x:a) (y:b x) (z:c x y) (w:d x y z). p x y z w)
```

## Existential quantification

#### exists_intro

Introduce `exists x. p x`, given `p` and a `witness`.

```FStar
val exists_intro (#a:Type) (p:(a -> Type)) (witness:a)
  : Lemma (requires (p witness)) (ensures (exists (x:a). p x))
```

#### forall_to_exists

Given a lemma `x:_ -> (p x ==> r)`, show that `(exists x. p x) ==> r`.

```FStar
val forall_to_exists (#a:Type) (#p:(a -> Type)) (#r:Type) ($_:(x:a -> Lemma (p x ==> r)))
  : Lemma ((exists (x:a). p x) ==> r)
```

#### forall_to_exists_2

[`forall_to_exists`](#forall_to_exists) for two variables.

```FStar
val forall_to_exists_2 (#a:Type) (#p:(a -> Type)) (#b:Type) (#q:(b -> Type)) (#r:Type)
  ($f:(x:a -> y:b -> Lemma ((p x /\ q y) ==> r)))
  : Lemma (((exists (x:a). p x) /\ (exists (y:b). q y)) ==> r)
```

#### exists_elim

Introduce a (scoped) witness of an existential.

```FStar
val exists_elim (goal:Type) (#a:Type) (#p:(a -> Type)) (_:squash (exists (x:a). p x))
  (_:(x:a{p x} -> GTot (squash goal))) : Lemma goal
```

Example:
```FStar
// if `exists x. p x` is in context, and we are proving `goal`
exists_elim goal (fun (x:_{p x}) ->
  // we now have a witness `x` in context here that we can use to prove `goal`
)
```

## Implications

> The two next functions introduce implications in the context. Since they expect `Type0`, you have to provide them squashed values. For instance:
>
> ```FStar
> let aux (_ : squash p) : Lemma q = ... in
> impl_intro aux
> ```

#### impl_intro_gtot

Introduce an implication using a `GTot` function. [`arrow_to_impl`](#arrow_to_impl) without explicit squash.

```FStar
val impl_intro_gtot (#p:Type0) (#q:Type0) ($_:p -> GTot q) : GTot (p ==> q)
```

#### impl_intro

Introduce an implication using a lemma.

```FStar
val impl_intro (#p:Type0) (#q:Type0) ($_: p -> Lemma q) : Lemma (p ==> q)
```

#### move_requires

Convert a requires/ensures lemma into an implication lemma.

```FStar
val move_requires
  (#a:Type)
  (#p:a -> Type)
  (#q:a -> Type)
  ($_:(x:a -> Lemma (requires (p x)) (ensures (q x)))) (x:a)
  : Lemma (p x ==> q x)
```

Note: Works only on lemmas with a single argument, but can be made
to work with lemmas with more arguments by using the following
"trick":

If we have ```FStar
   val foo x y z : Lemma
       (requires (p x y z))
       (ensures (q x y z))
``` and want ```FStar
   val bar x y z : Lemma
       (p x y z ==> q x y z)
``` then we can simply use ```FStar
   let bar x y z =
       move_requires (foo x y) z
```

#### impl_intro_gen

A generative version of [`impl_intro`](#impl_intro).

```FStar
val impl_intro_gen (#p:Type0) (#q:squash p -> Tot Type0) (_:squash p -> Lemma (q ()))
  : Lemma (p ==> q ())
```

#### forall_impl_intro

Both [`impl_intro`](#impl_intro) and [`forall_intro`](#forall_intro) at once.

```FStar
val forall_impl_intro
  (#a:Type)
  (#p:(a -> GTot Type))
  (#q:(a -> GTot Type))
  ($_:(x:a -> (squash(p x)) -> Lemma (q x)))
  : Lemma (forall x. p x ==> q x)
```

#### ghost_lemma

Given a `Ghost unit` function with pre/post conditions, convert it into a lemma with `forall` and implication.

```FStar
val ghost_lemma (#a:Type) (#p:(a -> GTot Type0)) (#q:(a -> unit -> GTot Type0))
  ($_:(x:a -> Ghost unit (p x) (q x)))
  : Lemma (forall (x:a). p x ==> q x ())
```

## Disjunctions

#### or_elim

Eliminate a disjunction. Useful for splitting proof of goal under two assumptions separately.

```FStar
val or_elim (#l #r:Type0) (#goal:(squash (l \/ r) -> Tot Type0))
  (hl:squash l -> Lemma (goal ()))
  (hr:squash r -> Lemma (goal ()))
  : Lemma ((l \/ r) ==> goal ())
```

Example:
```FStar
// assuming we want to prove `goal` under `l \/ r`.
let goal (_ : squash (l \/ r)) = ... in
or_elim #l #r #goal
        (fun _ ->
             // prove `goal` assuming `l`
        )
        (fun _ ->
             // prove `goal` assuming `r`
        )
// and now we've proven `goal` under `l \/ r`.
```

Example:
```FStar
// assuming we want to prove `goal`.
or_elim #_ #_ #(fun () -> goal)
        (fun (_:squash p) ->
             // prove `goal` assuming `p`
        )
        (fun (_:squash (~p)) ->
             // prove `goal` assuming `~p`
        )
// and now we've proven `goal`.
```

#### excluded_middle

Introduce `p \/ ~p` -- a classic of classical logic.

```FStar
val excluded_middle (p:Type) :Lemma (requires (True)) (ensures (p \/ ~p))
```
