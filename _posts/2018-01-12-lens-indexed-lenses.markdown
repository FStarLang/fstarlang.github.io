---
layout: post
title:  "Lens-indexed lenses"
date:   2018-01-12 00:43:00 -0900
comments: true
categories: general
author: Nikhil Swamy
---

In many functional programming languages, *lenses* are an increasingly
popular, highly composable, way of structuring bidirectional data
access, i.e., operations to both read and functionally update parts of
a composite object. There are many introductory tutorials about lenses
on the web: one that I found to be particularly gentle is by [Gabriel
Gonzalez](http://www.haskellforall.com/2012/01/haskell-for-mainstream-programmers_28.html). I'll
borrow some of his ideas to introduce lenses briefly here, although,
of course, I'll work in F\* rather than Haskell.

Doing it in F\* raises a couple of interesting challenges. First,
programming with mutable references and destructive updates is common
in F\*: so, unlike some other lens libraries, ours must support
mutation. Second, like everything else in F\*, our lens library
focuses on verification: we need a way to specify and prove properties
about lenses in a way that does not compromise the inherent
composability of lenses---composability being their primary appeal. My
solution, the *lens-indexed lens*, is analogous to the [monad-indexed
monad](https://www.fstar-lang.org/papers/mumon/paper.pdf), a structure
at the core of the design of F\* itself.

## Updating nested records: Clumsy, even with primitive syntax

Consider the following simple representation of a circle:

```
// A simple 2d point defined as a pair of integers
type point = {
  x:int;
  y:int;
}

// A circle is a point and a radius
type circle = {
  center: point;
  radius: nat
}
```

Using the record notation to define our types gives us some primitive
syntax to access the fields of a `circle` and `point`. But, despite
the primitive support, it's not very convenient to use. Here's some
code to move the circle in the `x`-direction: 

```
let move_x (delta:int) (c:circle) = 
    { c with center = {c.center with x = c.center.x + delta} }
```

Not pretty. But, by default, that's basically what it looks like in
most ML-like languages, including OCaml, Haskell etc. We'd much prefer
to write something like `c.center.x <- c.center.x + delta`. Lenses are
a clever way of designing a library of abstract "getters" and
"setters" that allow you to do just that.

## Pure lenses for composable, bidirectional access to data structures

A `lens a b` is pair of a getter and a setter: given an `a`-typed
value `v`, a `lens a b` allows you to

1. `get` a `b`-typed component out of `v`

2. create another `a`-typed value by updating the same `b`-typed
   component in `v`

```
// A `lens a b` focuses on the `b` component of `a`
// It provides a `get` to access the component
// And a `put` to update and `a` by updating its `b` component
type lens a b = {
  get: a -> b;
  put: b -> a -> a
}
```

For instance, given a `point`, we can define two lenses, `x` and `y`,
to read and write each of its fields, and lenses `center` and `radius`
to focus on each of the fields of a circle.

```
let x : lens point int = {
    get = (fun p -> p.x);
    put = (fun x' p -> {p with x=x'})
}
let y : lens point int = {
    get = (fun p -> p.y);
    put = (fun y' p -> {p with y=y'})
}
let center : lens circle point = {
    get = (fun c -> c.center);
    put = (fun p c -> {c with center=p}}
}
let radius : lens circle int = {
    get = (fun c -> c.radius);
    put = (fun r c -> {c with radius=r}}
}
```

This four definitions are rather boring: one could imagine
automatically generating them with a bit of meta-programming (maybe
we'll have a future post about that).

But, now comes the fun part. Lenses are easily composable: `l |. m`:
composes lenses, building an "access path" that extends the focus of
`l` with `m`.  (Note `#a`, `#b` and `#c` below bind implicit type
arguments.)

```
let ( |. ) #a #b #c (m:lens a b) (l:lens b c) : lens a c = {
  get = (fun x -> l.get (m.get x));
  put = (fun x y -> m.put (l.put x (m.get y)) y)
}
```

We can now define:

```
let move_x (delta:int) (c:circle) = 
    (center |. x).put ((center |. x).get c + delta) c
```

That may not look like much of an improvement, but even with F\*'s
poor support for custom operators, it's easy to re-define a couple of
common infix operators to make it better.

```
// `x.(|l|)`: accesses the l-focused component
let ( .(||) ) #a #b (x:a) (l:lens a b) : b = l.get x

// `x.(|l|) <- v`: updates the l-focused component of x with v
let ( .(||)<- ) #a #b (x:a) (l:lens a b) (v:b) : a = l.put v x

```

This lets us write:

```
let move_x (delta:int) (c:circle) = 
    c.(| center |. x |) <- c.(| center |. x |) + delta
```

which is pretty close to what we were aiming for.

## Lenses on mutable data

Just to be clear, despite appearances, 
`c.(| center |. x |) <- c.(| center |. x |) + delta` does not actually
mutate `c`. It creates a new circle that differs from `c` in the `x`
field of its `center`, leaving the original `c` unchanged.

That's nice, but we would also like a way to access and update in
place the mutable fields of a record. In a language like OCaml, an
object's fields may contains mutable references to heap-allocated
values. In such a setting, it's easy to define a lens like:

```
let deref : lens (ref a) a = {
    get = (fun r -> !r);
    put = (fun v r -> r := v)
}
```

But, this won't do in F\*: for starters, the `get` and `put` fields of
a `lens` are expected to be pure, total functions and the fields of
`deref` are certainly not pure: they read or write to the heap. F\*,
like Haskell, forces us to confess to our impurities.

If we were in Haskell, we could define the type of a stateful lens (in
F\* pseudo-syntax) like so:

```
type st_lens a b = {
     st_get : a -> ST b;
     st_put:  b -> a -> ST a
}
```
 
And we could give `deref` the type `st_lens (ref a) a`. But, this still
won't do in F\*. With verification in mind, stateful computations must

1. be accompanied by a precise specification, and

2. whatever specification we give a stateful lens, it needs to be
stable under composition: the composition of stateful lenses needs to
also be a stateful lens (e.g., we should be able to define a double
dereference to read an write an `a` from/to a `ref (ref a)`, by
composing lens from `ref (ref a)` to a `ref a` and again from a `ref
a` to an `a`).


## A precise specification for the `deref` lens

Let's look again at the `get` and `put` of the `deref` lens.

```
let get (r:ref a) = !r
let put (v:a) (r:ref a) = r := v
```

These two functions are the most primitive operations available on
references and, of course, we can give them precise specifications in
F\*.

```
val get (r:ref a) 
    : ST a
    (requires (fun h -> True))
    (ensures  (fun h0 x h1 -> h0==h1 /\ x == sel h0 r))

val put (v:a) (r:ref a)
    : ST unit 
    (requires (fun h -> True))
    (ensures  (fun h0 () h1 -> h1 == upd h0 r v))
```

Here `ST a (requires pre) (ensures post)` is the type of a stateful
computation whose pre-condition on the input heap is `pre`, and whose
post-condition `post` relates the initial heap `h0` to the result and
the final heap `h1`.

## Viewing the spec of a stateful lens as a pure lens

The specification of `get` describes the return value by getting it
from the initial heap `h0` and the reference `r`; the spec of `put`
describes the final heap `h1` by putting a new value into the initial
heap `h0`. Viewed differently, the specification of `get` and `put` is
itself a lens, a lens between a pair of `heap * ref a` and an
`a`. Let's call such a lens an `hlens`.

```
let hlens a b = lens (heap * a) b
let ref_hlens #a : hlens (ref a) a = {
    get = (fun (h,r) -> sel h r);
    put = (fun v (h, r) -> upd h r v)
}
```

We can then specify stateful lenses that perform destructive updates
based on their underlying `hlenses`.

```
// st_lens l: a stateful lens between a and b
type st_lens #a #b (l:hlens a b) = {
   st_get : (x:a
         -> ST b
            (requires (fun h -> True))
            (ensures  (fun h0 x h1 -> h0==h1 /\ y == l.get (h0, x))));

   st_put : (y:b 
         -> x:a 
         -> ST a
            (requires (fun h -> True))
            (ensures  (fun h0 x' h1 -> h1, x' == l.put y (h0, x)))
}
```

Given an `l:hlens a b`, an `st_lens l` is a stateful lens between `a`
and `b` that can perform destructive updates and whose behavior is
fully specified by `l`.

And we can finally specify the `deref` stateful lens:

```
let deref : st_lens ref_hlens = {
    st_get = (fun r -> !r);
    st_put = (fun v r -> r := v)
}
```

## Composing stateful lenses

Happily, stateful lenses compose nicely: the composition of an
`st_lens l` and an `st_lens m` is fully specified by `l |. m`, the
composition of `l` and `m`.

```
let ( |.. ) #a #b #c (#l:hlens a b) (#m:hlens b c)
                     (sl:st_lens l) (sm:st_lens m)
    : st_lens (l |. m) = {
      st_get = (fun (x:a) -> sm.st_get (sl.st_get x));
      st_put = (fun (z:c) (x:a) -> sl.st_put (sm.st_put z (sl.st_get x)) x)
}
```

And any pure lens `l` is easily lifted to a stateful lens whose
specification is the trivial lifting of `l` itself to an `hlens`.

```
let as_hlens #a #b (l:lens a b) : hlens a b = {
    get = (fun (h, x) -> x.(|l|));
    put = (fun y (h, x) -> h, (x.(|l|) <- y));
}

let as_stlens #a #b (l:lens a b) : stlens (as_hlens l) = {
    st_get = (fun (x:a) -> x.(|l|));
    st_put = (fun (y:b) (x:a) -> x.(|l|) <- y)
}
```

These liftings of pure lenses to stateful lenses are convenient to
fold in as part of the lens composition, lifting pure lenses as they
are composed with stateful lenses, either on the left or the right.

```
let ( |^. ) #a #b #c (m:lens a b) (#l:hlens b c) (sl:stlens l) =
    (as_stlens m) |.. sl

let ( |.^ ) #a #b #c (#l:hlens a b) (sl:stlens l) (m:lens b c) =
    sl |.. as_stlens m
```

We can also define some shorthands, `x.[sl]` and `x.[sl] <- v`, to
apply a stateful lens `sl` to access or mutate an object `x`.

```
let ( .[]   ) #a #b (#l:hlens a b) (x:a) (sl:stlens l) =
    sl.st_get x
let ( .[]<- ) #a #b (#l:hlens a b) (x:a) (sl:stlens l) (y:b) = 
    let _ = sl.st_put y x in ()
```

## Stateful lenses at work

We can now revisit our original example of circles and points, this
time defining them to support destructive updates.

```
type point = {
  x:ref int;
  y:ref int;
}
type circle = {
  center: ref point;
  radius: ref nat
}
```

These are just the types we had before, but now with mutable
references in each field. Pure lenses to access and mutate each field
are easy to define, as before.

```
let center : lens circle (ref point) = {
  get = (fun c -> c.center);
  put = (fun p c -> {c with center = p})
}
let x : lens point (ref int) = {
  get = (fun p -> p.x);
  put = (fun x p -> {p with x = x})
}
...
```

Using a combination of pure and stateful lenses, we can mutate the `x`
field of a circle's center easily.

```
let move_x delta c
   = let l = center |^. deref |.^ x |.. deref in
     c.[l] <- c.[l] + delta
```

Notice that since a lens is a first-class value, the access path from
a circle to the contents of the `x`-field of its center is a value
that can be constructed once, bound to a variable (`l`) and re-used as
needed.

Of course, we also want to be able to specify `move_x`. But, since
every stateful lens is fully specified by a pure lens, specifying
`move_x` is now pretty easy in terms of its action on the heap. Here's
the type of `move_x`:

```
val move_x (delta:int) (c:circle) : ST unit
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
             let l = center |^. deref |.^ x |.. deref in
             (h1, c) == (c.(h0, l) <- c.(h0, l) + delta)))

```

We can specify it using just the same lens that we used in its
implementation, except using the `hlens` that's the pure counterpart
of the stateful lens `l`. Since the type of a stateful lens always
mentions its corresponding `hlens`, we can easily define functions to
to specify a stateful lenses effect.


```
let ( .() )   #a #b (#l:hlens a b) (x:a) (hs:(heap * stlens l)) = l.get (fst hs, x)
let ( .()<- ) #a #b (#l:hlens a b) (x:a) (hs:(heap * stlens l)) (y:b) = l.put y (fst hs, x)
```

Without these lenses, here's the mouthful we'd have had to write
instead.

```
let move_x2 (delta:int) (c:circle) : ST unit
  (requires (fun _ -> True))
  (ensures  (fun h _ h' ->
             let rp = c.center in
             let p = sel h rp in
             let rx = p.x in
             let h1 = upd h rx (sel h rx + delta) in
             let p = sel h1 rp in
             let h2 = upd h1 rp ({p with x = rx}) in
             h' == h2))
   = c.[center |^. v |.^ x |.. v] <- (c.[center |^. v |.^ x |.. v] + delta)
```

Worse than the verbosity, it actually took me nearly half an
hour to write this specification, requiring peeling back the layers of
abstraction to figure out the exact order in which the reads and
writes were occurring!

## Takeaways

Lenses are a powerful way to structure data access and mutation. With
stateful lens-indexed lenses, we can use them to implement and specify
destructive updates of nested data structures in a compact and
composable manner.

You can see a fully detailed code listing for this blog post
[here](https://github.com/FStarLang/FStar/blob/master/examples/data_structures/StatefulLens.fst).

Lens libraries in other languages are much more extensive---I've
merely ~~scratched the surface~~ ground out the most basic lens
combinators.
