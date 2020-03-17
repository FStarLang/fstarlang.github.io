# FStar.Pervasives.Native

```fstar
module FStar.Pervasives.Native
```

This is a file from the core library, dependencies must be explicit

```fstar
open Prims
```

> This module is implicitly opened in the scope of all other modules.
>
> It provides several basic types in F* that enjoy some special
> status in extraction. For instance, the tuple type below is
> compiled to OCaml's tuple type, rather than to a F*-defined
> inductive type. See ulib/ml/FStar_Pervasives_Native.ml

#### option

`option a` represents either  `Some a`-value or a non-informative `None`.

```fstar
type option (a: Type) =
  | None : option a
  | Some : v: a -> option a
```

## Tuples

> Aside from special support in extraction, the tuple types have
> special syntax in F*.
>
> For instance, rather than [tupleN a1 ... aN],
> we usually write [a1 & ... & aN] or [a1 * ... * aN].
>
> The latter notation is more common for those coming to F* from
> OCaml or F#. However, the [*] also clashes with the multiplication
> operator on integers define in FStar.Mul. For this reason, we now
> prefer to use the [&] notation, though there are still many uses
> of [*] remaining.
>
> Tuple values are introduced using as [a1, ..., an], rather than
> [MktupleN a1 ... aN].
>
> We define tuples up to a fixed arity of 14. We have considered
> splitting this module into 14 different modules, one for each
> tuple type rather than eagerly including 14-tuples in the
> dependence graph of all programs.

#### tuple2

Pairs: `tuple2 a b` is can be written either as `a * b`, for
notation compatible with OCaml's. Or, better, as `a & b`.

```fstar
type tuple2 'a 'b = | Mktuple2 : _1: 'a -> _2: 'b -> tuple2 'a 'b
```

#### fst

The fst and snd projections on pairs are very common

```fstar
let fst (x: tuple2 'a 'b) : 'a = Mktuple2?._1 x
let snd (x: tuple2 'a 'b) : 'b = Mktuple2?._2 x
```

```fstar
type tuple3 'a 'b 'c = | Mktuple3 : _1: 'a -> _2: 'b -> _3: 'c -> tuple3 'a 'b 'c
```

```fstar
type tuple4 'a 'b 'c 'd = | Mktuple4 : _1: 'a -> _2: 'b -> _3: 'c -> _4: 'd -> tuple4 'a 'b 'c 'd
```

```fstar
type tuple5 'a 'b 'c 'd 'e =
  | Mktuple5 : _1: 'a -> _2: 'b -> _3: 'c -> _4: 'd -> _5: 'e -> tuple5 'a 'b 'c 'd 'e
```

```fstar
type tuple6 'a 'b 'c 'd 'e 'f =
  | Mktuple6 : _1: 'a -> _2: 'b -> _3: 'c -> _4: 'd -> _5: 'e -> _6: 'f -> tuple6 'a 'b 'c 'd 'e 'f
```

```fstar
type tuple7 'a 'b 'c 'd 'e 'f 'g =
  | Mktuple7 : _1: 'a -> _2: 'b -> _3: 'c -> _4: 'd -> _5: 'e -> _6: 'f -> _7: 'g
    -> tuple7 'a 'b 'c 'd 'e 'f 'g
```

```fstar
type tuple8 'a 'b 'c 'd 'e 'f 'g 'h =
  | Mktuple8 : _1: 'a -> _2: 'b -> _3: 'c -> _4: 'd -> _5: 'e -> _6: 'f -> _7: 'g -> _8: 'h
    -> tuple8 'a 'b 'c 'd 'e 'f 'g 'h
```

```fstar
type tuple9 'a 'b 'c 'd 'e 'f 'g 'h 'i =
  | Mktuple9 :
      _1: 'a ->
      _2: 'b ->
      _3: 'c ->
      _4: 'd ->
      _5: 'e ->
      _6: 'f ->
      _7: 'g ->
      _8: 'h ->
      _9: 'i
    -> tuple9 'a 'b 'c 'd 'e 'f 'g 'h 'i
```

```fstar
type tuple10 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j =
  | Mktuple10 :
      _1: 'a ->
      _2: 'b ->
      _3: 'c ->
      _4: 'd ->
      _5: 'e ->
      _6: 'f ->
      _7: 'g ->
      _8: 'h ->
      _9: 'i ->
      _10: 'j
    -> tuple10 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j
```

```fstar
type tuple11 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k =
  | Mktuple11 :
      _1: 'a ->
      _2: 'b ->
      _3: 'c ->
      _4: 'd ->
      _5: 'e ->
      _6: 'f ->
      _7: 'g ->
      _8: 'h ->
      _9: 'i ->
      _10: 'j ->
      _11: 'k
    -> tuple11 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k
```

```fstar
type tuple12 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l =
  | Mktuple12 :
      _1: 'a ->
      _2: 'b ->
      _3: 'c ->
      _4: 'd ->
      _5: 'e ->
      _6: 'f ->
      _7: 'g ->
      _8: 'h ->
      _9: 'i ->
      _10: 'j ->
      _11: 'k ->
      _12: 'l
    -> tuple12 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l
```

```fstar
type tuple13 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm =
  | Mktuple13 :
      _1: 'a ->
      _2: 'b ->
      _3: 'c ->
      _4: 'd ->
      _5: 'e ->
      _6: 'f ->
      _7: 'g ->
      _8: 'h ->
      _9: 'i ->
      _10: 'j ->
      _11: 'k ->
      _12: 'l ->
      _13: 'm
    -> tuple13 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm
```

```fstar
type tuple14 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n =
  | Mktuple14 :
      _1: 'a ->
      _2: 'b ->
      _3: 'c ->
      _4: 'd ->
      _5: 'e ->
      _6: 'f ->
      _7: 'g ->
      _8: 'h ->
      _9: 'i ->
      _10: 'j ->
      _11: 'k ->
      _12: 'l ->
      _13: 'm ->
      _14: 'n
    -> tuple14 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n
```
