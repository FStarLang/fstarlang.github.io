# FStar.Squash

```fstar
module FStar.Squash
```

> The module provides an interface to work with [squash] types, F*'s
> representation for classical, proof-irrelevant propositions.
>
> This is inspired in part by:
> Quotient Types: A Modular Approach. Aleksey Nogin, TPHOLs 2002.
> http://www.nuprl.org/documents/Nogin/QuotientTypes_02.pdf
>
> Broadly, [squash] is a monad, support the usual [return] and
> [bind] operations.
>
> Additionally, it supports a [push_squash] operation that relates
> arrow types and [squash].

#### return_squash

A proof of `a` can be forgotten to create a squashed proof of `a`

```fstar
val return_squash (#a: Type) (x: a) : Tot (squash a)
```

#### bind_squash

Sequential composition of squashed proofs

```fstar
val bind_squash (#a #b: Type) (x: squash a) (f: (a -> GTot (squash b))) : Tot (squash b)
```

#### push_squash

The `push` operation, together with [`bind_squash`](#bind_squash), allow deriving
some of the other operations, notably [`squash_double_arrow`](#squash_double_arrow). We
rarely use the [`push_squash`](#push_squash) operation directly.

```fstar
val push_squash (#a: Type) (#b: (a -> Type)) (f: (x: a -> Tot (squash (b x))))
    : Tot (squash (x: a -> GTot (b x)))
```

One reading of `push f` is that for a function `f` that builds a
proof-irrelevant prooof of `b x` for all `x:a`, there exists a
proof-irrelevant proof of `forall (x:a). b x`.

Note: since `f` is not itself squashed, `push_squash f` is not
equal to `f`.

> The pre- and postconditions of of [Pure] are equivalent to
> squashed arguments and results.

#### get_proof

`get_proof p`, in a context requiring `p` is equivalent to a proof
of `squash p`

```fstar
val get_proof (p: Type) : Pure (squash p) (requires p) (ensures (fun _ -> True))
```

#### give_proof

`give_proof x`, for `x:squash p` is a equivalent to ensuring
`p`.

```fstar
val give_proof (#p: Type) (x: squash p) : Pure unit (requires True) (ensures (fun _ -> p))
```

#### proof_irrelevance

All proofs of `squash p` are equal

```fstar
val proof_irrelevance (p: Type) (x y: squash p) : Tot (squash (x == y))
```

#### squash_double_arrow

Squashing the proof of the co-domain of squashed universal
quantifier is redundant---[`squash_double_arrow`](#squash_double_arrow) allows removing
it.

```fstar
val squash_double_arrow (#a: Type) (#p: (a -> Type)) ($f: (squash (x: a -> GTot (squash (p x)))))
    : GTot (squash (x: a -> GTot (p x)))
```

#### push_sum

The analog of [`push_squash`](#push_squash) for sums (existential quantification

```fstar
val push_sum (#a: Type) (#b: (a -> Type)) ($p: (dtuple2 a (fun (x: a) -> squash (b x))))
    : Tot (squash (dtuple2 a b))
```

#### squash_double_sum

The analog of [`squash_double_arrow`](#squash_double_arrow) for sums (existential quantification)

```fstar
val squash_double_sum
      (#a: Type)
      (#b: (a -> Type))
      ($p: (squash (dtuple2 a (fun (x: a) -> squash (b x)))))
    : Tot (squash (dtuple2 a b))
```

#### map_squash

`squash` is functorial; a ghost function can be mapped over a squash

```fstar
val map_squash (#a #b: Type) (x: squash a) (f: (a -> GTot b)) : Tot (squash b)
```

#### join_squash

`squash` is a monad: double squashing is redundant and can be removed.

```fstar
val join_squash (#a: Type) (x: squash (squash a)) : Tot (squash a)
```
