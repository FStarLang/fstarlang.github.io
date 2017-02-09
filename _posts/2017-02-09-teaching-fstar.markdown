---
layout: post
title:  "Teaching F*"
date:   2017-02-09 22:40:00 +0100
comments: true
categories: general
author: Markulf Kohlweiss, Karthik Bhargavan, Catalin Hritcu, and Jonathan Protzenko
---

Having to teach F* provides strong motivation to dust off the cobwebs
and tidy away long forgotten bread crumbs hidden deep down in
remote directories to make the language easier to
install and use. It is thus no coincidence that major releases have
been aligned with some of us going back to school after a long
summer of coding to step out there and present the newest features of
the language to a crowd of rowdy students.

The latest two occasions:

* a [Summer School on Computer Aided Analysis of Cryptographic
  Protocols](https://www.cs.bris.ac.uk/cryptoschool/) in Bucharest,
  Romania, 13-14 September 2016 in which we had two days to teach
  [Verifying Cryptographic Protocol Implementations with
  F*](http://prosecco.gforge.inria.fr/personal/hritcu/teaching/bucharest-school-2016/).

  Who would have thought that F\* can be used to introduce students of
  varying backgrounds to functional programming. This lead to the
  [Gentle introduction for F*](
  http://prosecco.gforge.inria.fr/personal/hritcu/teaching/mpri-jan2017/slides/out/01/slides01.html#/sec-a-gentle-introduction-to-f-).

  This was the first time we used the [universes
  version of F\*](https://github.com/FStarLang/FStar/releases/tag/V0.9.4.0) for teaching and we thus had to updated the [F* tutorial](
  https://fstar-lang.org/tutorial/). We also played with docker builds to provide students with a preconfigured interactive mode, but most students stuck to the tutorial.

* a MPRI course on [Cryptographic protocols: formal and computational
  proofs](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-30)
  in which we could spend more time teaching [Program Verification with
  F*](http://prosecco.gforge.inria.fr/personal/hritcu/teaching/mpri-jan2017/).

  We for the first time taught low-Level stateful
  programming with hyperStack. Warning, this is so new that it's not
  yet covered by the tutorial.

It is no coincidence that both courses had a decidedly cryptographic
focus given that F\* is the language of choice of
the [Everest project](https://project-everest.github.io/).

What features would you like to see included in future research
schools? And what do you think are the biggest stumbling blocks when
learning and teaching a hot-off-the-press research language like F\*?
