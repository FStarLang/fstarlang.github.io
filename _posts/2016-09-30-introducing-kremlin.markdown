---
layout: post
title:  "Introducing KreMlin"
date:   2016-09-30 19:27:00 +0100
comments: true
categories: general
author: Jonathan Protzenko
---

The work we do these days on F\* is often in service of 
[Project Everest](https://project-everest.github.io/). The goal of Everest is
to verify _and_ deploy a drop-in replacement for the HTTPS stack, the protocol
using which you are probably reading this page, securely (hopefully). So far, 
we've been focusing most of our efforts in Everest on [TLS](https://tlswg.github.io/tls13-spec/), 
the protocol at the heart of HTTPS.

Right now, I'm stuck in the
Eurostar back from our week-long meeting in Cambridge, UK, so it feels like a
good time to write down some thoughts about KreMLin, a new compiler backend that we're
using in Everest, that
several of us have been working on over the summer, at MSR and INRIA.

As a reminder, Everest sets out to verify _and_ deploy secure cryptographic protocols, starting with TLS 1.3.
**Deploy** is the salient part: in order to see people adopt our code, we not
only need to write and prove our TLS library, but also to

- make sure it delivers a level of performance acceptable for browser vendors,
  and
- package it in a form that's palatable for a hardcode Windows developer that
  started writing C before I was born.

A TLS library can, roughly speaking, be broken down into two parts: the
protocol layer that performs the handshake ("libssl") and the cryptographic
layer that actually encrypts the data to be transmitted ("libcrypto"). The
handshake connects to the server, says hi, agrees on which algorithms to use,
and agrees on some cryptographic parameters. Once parameters have been setup,
the cryptographic layer is responsible for encrypting the stream of data.

Experience shows that the performance of a TLS library most often boils down to
the performance of the underlying cryptography. The handshake is network-bound,
but when transmitting a big file, encryption needs to be fast. This means that
for Everest, we need super efficient cryptography. Fortunately, many smart
people have spent a lot of time and energy writing super-neat C implementations
that squeeze the last bit of performance out of your compiler. However, we wish
to write and verify our programs in F\*, not C.

This is where KreMLin comes in. The workflow is as follows: one takes a neatly
optimized cryptographic routine, then translates it into F\* syntax ("shallow
embedding"); using KreMLin, one extracts it back to C, but gets a verified
version that pretty much looks like the original. For instance, here's a bit of
F\* that implements the main entry point of Chacha20.

```
let rec counter_mode key iv counter len plaintext ciphertext =
  if len =^ 0ul then ()
  else if len <^ blocklen
  then (* encrypt final partial block *)
    begin
      let cipher = sub ciphertext  0ul len in
      let plain  = sub plaintext   0ul len in
      prf cipher key iv counter len;
      xor_bytes_inplace cipher plain len
    end
  else (* encrypt full block *)
    begin
      let cipher = sub ciphertext  0ul blocklen in
      let plain  = sub plaintext   0ul blocklen in
      prf cipher key iv counter blocklen;
      xor_bytes_inplace cipher plain blocklen;
      let len = len -^ blocklen in
      let ciphertext = sub ciphertext blocklen len in
      let plaintext  = sub plaintext  blocklen len in
      counter_mode key iv (counter +^ 1ul) len plaintext ciphertext
    end
```

One goes great lengths to prove the following properties of this piece of F\*
code.

- **Memory safety.** We model stack allocation in F\* using a new `Stack` effect;
  one may only allocate local mutable variables, or buffers on the stack. Every
  buffer operation needs to prove that the buffer is still live, and that the
  index is within bounds. For instance, in the code above, the calls to `sub`
  take a pointer _into_ one of these buffers, and verification happens behind the
  scenes.
- **Functional correctness.** We have written in this style a bignum library,
  some elliptic curve operations, stream ciphers and mac algorithms, as well as
  an AEAD construction. For the math part, for instance, the optimized curve
  operations are shown to implement the correct mathematical operations.
- **Cryptographic properties.** By using a technique called "idealization", one
  can prove two versions of the same code: one that relies on cryptographic
  assumptions, such as "this function can be replaced by a function
  that returns random bytes"; and one that actually uses real cryptography
  instead of `Random.bytes()`. The code branches on an `ideal` boolean; for
  cryptographic proof purposes, we consider the `ideal` case; for extraction
  purposes, we only consider the other, "real" case.

F\* already performs erasure and extraction for its OCaml backend; the tool I
wrote, **KreMLin**, takes it from there and performs further rewritings and
transformations so that the code ends up in a limited, first-order, monomorphic
subset of F\* called Low\*. If code falls within the Low\* subset, then KreMLin
knows how to translate it to C. Here's what comes out of the tool after
extraction:

```
void Crypto_Symmetric_Chacha20_counter_mode(
  uint8_t *key,
  uint8_t *iv,
  uint32_t counter,
  uint32_t len,
  uint8_t *plaintext,
  uint8_t *ciphertext
)
{
  if (len == UINT32_C(0))
  {

  }
  else if (len < Crypto_Symmetric_Chacha20_blocklen)
  {
    uint8_t *cipher = ciphertext + UINT32_C(0);
    uint8_t *plain = plaintext + UINT32_C(0);
    Crypto_Symmetric_Chacha20_prf(cipher, key, iv, counter, len);
    Buffer_Utils_xor_bytes_inplace(cipher, plain, len);
  }
  else
  {
    uint8_t *cipher = ciphertext + UINT32_C(0);
    uint8_t *plain = plaintext + UINT32_C(0);
    Crypto_Symmetric_Chacha20_prf(cipher, key, iv, counter, Crypto_Symmetric_Chacha20_blocklen);
    Buffer_Utils_xor_bytes_inplace(cipher, plain, Crypto_Symmetric_Chacha20_blocklen);
    uint32_t len0 = len - Crypto_Symmetric_Chacha20_blocklen;
    uint8_t *ciphertext0 = ciphertext + Crypto_Symmetric_Chacha20_blocklen;
    uint8_t *plaintext0 = plaintext + Crypto_Symmetric_Chacha20_blocklen;
    Crypto_Symmetric_Chacha20_counter_mode(key,
      iv,
      counter + UINT32_C(1),
      len0,
      plaintext0,
      ciphertext0);
  }
}
```

One can see that the tool goes great length to generate beautiful C: names and
control-flow are preserved, and everything is pretty-printed. This is to tackle
the second concern I mentioned initially: there is no hope of getting a browser
vendor to integrate code written in F\*, which would be considered in that
setting "not a real language". In constract, by offering an extracted C version
of our library, we have reasonable hope that reviewers can skim the code,
convince themselves that it's legit, and take us a little bit more seriously.

We worked out a simulation between Low\* and a simplified version of C we dubbed
"C\*"; this grounds our translation in some theoretical basis. The simulation
covers trace preservation: if the program does not have side channels in the
first place, then the translation from Low\* to C\* does not introduce any new
side channels. The tool is unverified; we plan to extend the formalism to cover
more of the transformations performed by the tool; in the long run, I would like
to write KreMLin in F\* and certify it, but that seems non-trivial.

We have adopted that style for an entire body of cryptographic code (> 10,000
lines of F*, including whitespace and comments), and obtain competitive
performance. Right now, the tool and formalism deal with one specific flavor
of code that performs stack-based allocation only. However, we are extending it
right now to deal with other patterns of allocation, such as allocation on the
heap.

KreMLin is currently written in OCaml; I re-used a fair number of tricks from my
earlier Mezzo project to make writing transformation passes on the internal AST
easier. These including monomorphization, inlining, hoisting and rewritings to
go from an expression language to a statement language, and some tricks to go
from the ML scoping rules to the C ones.

KreMLin is [open-source](https://github.com/FStarLang/kremlin/); we have an
[ML'16 abstract](https://jonathan.protzenko.fr/papers/ml16.pdf) if you're
curious, as well as some
[slides](https://jonathan.protzenko.fr/papers/talk-ml16.pdf).
