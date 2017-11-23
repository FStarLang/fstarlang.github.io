---
layout: post
title:  "printf*"
date:   2017-11-22 23:04:00 -0900
comments: true
categories: general
author: Nikhil Swamy
---

It must have been around 2002 when I first read a paper by Lennart
Augustsson about a language called
[Cayenne](https://dl.acm.org/citation.cfm?doid=289423.289451). It was
the first time I had come across dependent types. Lennart's first
example motivating the need for (and the power of) dependent types is
`printf`: a function used by legions of programmers that is, in an
essential way, very dependently type. Having worked since then on many
programming languages with various forms of dependent types, now, 15
years later, a language that I contribute to has a proper, dependently
typed `printf`. Well, a `sprintf`, but Cayenne's example was also a
`sprintf`. This post is about explaining how `sprintf` works in F*.

## What is `sprintf`?

Some variant of `sprintf` appears in the standard library of many
programming languages---it allows for a string to be formatted and
assembled from a number of programmer-provided values in a convenient
way. A basic usage is like this:

```
   let format_date (month:string) (day:nat) (year:nat) =
       sprintf "%s %d, %d" month day year
```    

Where, `format_data "Nov." 22 2017` returns the string `"Nov. 22, 2017"`.

Or:

```
   let format_date (day:string) (month:string) (day:nat) (year:nat) =
       sprintf "%s, %s %d, %d" day month day year
```

The curious thing here is that `sprintf`'s first argument is a "format
string", and the number and types of its remaining arguments
**depends** on the format string: i.e., `sprintf` is the
quintessential dependently typed function.

## A sketch of `sprintf` in F\*

Here's one type for a simplified version of `sprintf` in F\*.

```
val sprintf: s:string{valid_format_string s} -> sprintf_type s
```

Given a first argument `s`, a `valid_format_string`, the return value
has a type `sprintf_type s` that is a function of the format string
`s`.

Defining `valid_format_string s` is relatively straightforward, e.g.,
if one wanted to only allow `%d` and `%s` as format specifiers (with
`%%` as an escape sequence for printing "%" itself), one could do it
like this:

```
let rec valid_format_string = function
    | [] -> true
    | '%'::'d'::s 
    | '%'::'s'::s 
    | '%'::'%'::s -> valid_format_string s    
    | '%'::_ -> false
    | _::s -> valid_format_string s
```

`sprintf_type s` is a little more unusual: it is a function that
computes a type from a format string `s`. Here's one version of it:

```
let rec sprintf_type (s:string{valid_format_string s}) =
    match s with
    | [] -> string
    | '%'::'d'::s -> (int -> sprintf_type s)
    | '%'::'s'::s -> (string -> sprintf_type s)
    | '%'::'%'::s -> sprintf_type_chars s
    | _::s -> sprintf_type s
```

Look at that closely: in the first case, if the format string is
empty, `sprintf ""` just returns a string. If the format string begins
with `"%d"`, then sprintf expects one more argument, an int, followed
by whatever arguments are needed by the rest of the format string, and
so on.

Note: I cut a corner there, treating a `string` as a list of
characters, whereas in F\* you have to explicitly coerce a string to a
list of characters. You can see the whole program, corners restored,
at the end of this post.

## That was simple! Why did it take so long for F\* to get `sprintf`?

The version of `sprintf` provided in F\*'s standard library
(`FStar.Printf.sprintf`) is somewhat more complex than the simple
example we've just seen. For one, it supports many more format
specifiers than just `%d` and `%s`. But, that's just a detail. More
essentially, in order for callers of `sprintf` to be checked
efficiently, the type-checker has to **compute** the recursive
function `sprintf_type s` at type-checking time.

This kind of type-level computation is a distinctive feature of many
dependently typed languages, a feature that F\* acquired in full
generality about 2 years ago. Unlike other dependently typed
languages, in addition to type-level computation, the F\* type-checker
also makes use of algebraic and logical reasoning via an SMT
solver. Balancing these features has required quite a lot of care:
e.g., compute too much in the type-checker and the SMT solver is faced
with reasoning about enormous, partially reduced terms; compute too
little and the SMT solver has to do a lot of computation, which is not
its strong point.

For `sprintf`, we don't want to rely on SMT reasoning at all, since
everything can be checked simply using type-level computation. For
this, F\* requires a hint in the type of `sprintf`:

```
val sprintf : s:string{normalize (valid_format_string s)}
           -> normalize (sprintf_type s)
```

Notice the additional calls to `normalize`, which signals to F\* to
fully reduce `valid_format_string s` and `sprintf_type s` before
resorting to SMT reasoning.

## Additional material

See [the actual
library](https://github.com/FStarLang/FStar/blob/master/ulib/FStar.Printf.fst)
(based on a version that Catalin Hritcu first wrote) for more details
about how this works, including how we compile away uses of `sprintf`
to a bunch of string concatenations.

Here's a small standalone version. Compare it to the version in
Cayenne ... it's pretty similar, but it took (well, at least it took
me) 15 years to get there! : )

```
module SimplePrintf
open FStar.Char
open FStar.String

let rec valid_format_chars = function
    | [] -> true
    | '%'::'d'::s 
    | '%'::'s'::s 
    | '%'::'%'::s -> valid_format_chars s    
    | '%'::_ -> false
    | _::s -> valid_format_chars s

let valid_format_string s =
    valid_format_chars (list_of_string s)

let rec sprintf_type_chars (s:list char) =
    match s with
    | [] -> string
    | '%'::'d'::s -> (int -> sprintf_type_chars s)
    | '%'::'s'::s -> (string -> sprintf_type_chars s)
    | '%'::'%'::s -> sprintf_type_chars s
    | _::s -> sprintf_type_chars s

let sprintf_type s = sprintf_type_chars (list_of_string s)

let rec sprintf_chars 
        (s:list char{normalize (valid_format_chars s)})
        (res:string)
    : normalize (sprintf_type_chars s)
    = match s with
      | [] -> res
      | '%'::'d'::s -> fun (x:int) -> sprintf_chars s (res ^ string_of_int x)
      | '%'::'s'::s -> fun (x:string) -> sprintf_chars s (res ^ x)
      | '%'::'%'::s -> sprintf_chars s (res ^ "%")
      | x::s -> sprintf_chars s (res ^ string_of_char x)

let sprintf (s:string{normalize (valid_format_string s)})
   : normalize (sprintf_type s)
   = sprintf_chars (list_of_string s) ""
```
