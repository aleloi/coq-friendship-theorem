<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Friendship Theorem in Coq

[![coqdoc][coqdoc-shield]][coqdoc-link]



[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://aleloi.github.io/coq-friendship-theorem/toc.html


This project contains a Coq proof of the Friendship Theorem in graph
theory, following Proofs from THE BOOK, 4th ed., Aigner
et. al. pp. 257-259, 2010.

## Meta

- Author(s):
  - Alex Loiko (initial)
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.15 or later
- Additional dependencies:
  - `coq-mathcomp-algebra`.
  - [CoqHammer](https://github.com/lukaszcz/coqhammer) for `sauto`.
  - `coq-mathcomp-field` for the existance of an algebraically closed
field `algC` with characteristic 0.
  - [MathComp](https://math-comp.github.io) for most of the proof
  - [Dune](https://dune.build) 2.5 or later
- Coq namespace: `Friendship`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Friendship Theorem in Coq
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-friendship-theorem
```

To instead build and install manually, do:

``` shell
git clone https://github.com/aleloi/coq-friendship-theorem.git
cd coq-friendship-theorem
dune build
dune install
```


## Documentation 

[This proof by Elizabeth
Walker](https://math.mit.edu/~apost/courses/18.204-2016/18.204_Elizabeth_Walker_final_paper.pdf)
is the same as the one in `Proofs from THE BOOK`. I followed it as
close as I could, but had to deviate a bit. E.g. MathComp doesn't
prove that symmetric matrices are diagonalizable over
algebraically closed fields. Instead I explicitly diagonalize the
$A^2$ matrix by constructing a basis change matrix. Then I prove
that whenever the characteristic polynomial of $A^2$ over `algC`
is $\prod_\mu (z-\mu)$, the characteristic polynomial of $A$ must
be $\prod_\mu (z-\pm\sqrt{\mu})$.

The theorem formulation is currently
``` coq
(* 
	T is a finite nonempty set of people some of which are friends. 
	No one is friends with themselves (irreflexivity), and if x is 
	friends with y, then y is friends with x (symmetry). If every 
	pair of people have exactly one common friend, there exists one
	person that is friends with everyone else.
*)
Theorem Friendship
  (T: finType) (T_nonempty: [set: T] != set0)
  (F : rel T) (Fsym: symmetric F) (Firr: irreflexive F) :
  (forall (u v: T), u != v -> #|[set w | F u w & F v w]| == 1) ->
  {u : T | forall v : T, u != v -> F u v}.
```

The proof is mainly split up between
[theories/combinatorics.v](theories/combinatorics.v) for the graph
theory and [theories/adj2_matrix.v](theories/adj2_matrix.v) for
the linear algebra. The proof is roughly 2 parts combinatorics and
graph theory, 1 part linear algebra, and 3 parts more or less
general lemmas of matrices, characteristic polynomials and such.

As far as I know, this is the 79th [formalized Coq theorem](https://madiot.fr/coq100/) of the ["top 100" mathematical theorems](http://www.cs.ru.nl/~freek/100/) .

```
$ wc theories/*v
  401  2009 14280 theories/adj2_matrix.v
   53   216  1383 theories/bigops.v
  852  4093 26067 theories/combinatorics.v
  237  1111  7391 theories/divisibility.v
   24   154   740 theories/friendship_theorem.v
   70   300  1967 theories/matrix_casts.v
  132   644  4510 theories/matrix_lemmas.v
  343  1499 11162 theories/square_char_poly.v
 2112 10026 67500 total
```
