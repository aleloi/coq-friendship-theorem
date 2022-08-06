This repository contains a proof of the [Friendship Theorem](https://math.mit.edu/~apost/courses/18.204-2016/18.204_Elizabeth_Walker_final_paper.pdf) in Coq with the [Mathematical Components](https://math-comp.github.io/) library.

The formulation is currently
``` coq
Theorem Friendship
  (T: finType) (T_nonempty: [set: T] != set0)
  (F (* friendship relation *): rel T) (Fsym: symmetric F) (Firr: irreflexive F) :

  (* u!= v have exactly 1 common friend *)
  (forall (u v: T), u != v -> #|[set w | F u w & F v w]| == 1) ->
  {u : T | forall v : T, u != v -> F u v}.
```

I followed the proof in the linked article, which in turn follows that
in *Proofs from THE BOOK*. The theorem formulation is in
[theories/friendship_theorem.v](theories/friendship_theorem.v). The
proof is mainly split up between
[theories/combinatorics.v](theories/combinatorics.v) for the graph
theory and [theories/adj2_matrix.v](theories/adj2_matrix.v) for the
linear algebra. The proof is roughly 2 parts combinatorics and graph
theory, 1 part linear algebra, and 3 parts more or less general lemmas
of matrices, characteristic polynomials and such.

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

## Dependencies
* coq-hammer-tactics for `sauto`.
* coq-mathcomp-algebra
* coq-mathcomp-field for the existance of an algebraically closed field `algC` with characteristic 0
* coq-mathcomp-ssreflect


## TODOS 
* Build systems:
  * How do set up a build system with declared dependencies ? 
	* I've seen other packages depending on an exact version of Coq; I
      want to do this for Coq and math-comp.
	* Should I depend on 'hammer'? I haven't been able to use it (OOM
      because of too many imported modules and too low memory), and I
      think the setup has manual steps.
	* How does coqdoc work (and how do I set it up)? I can't find any
      generated documentation anywhere. Also, shouldn't it install
      something in `~/.opam/default/lib/coq/user-contrib`? Currently
      `make` prints `SKIP theories/adj_matrix_props.v since it has no`
      `logical path`.
  * Read the docs about 
	* [building](https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile)
	* [documenting](https://coq.inria.fr/refman/using/tools/coqdoc.html)
	* [packaging](https://coq.inria.fr/opam-packaging.html)
	* This [SO post](https://stackoverflow.com/questions/53822753/coqide-error-with-exporting-modules-in-the-same-library) about importing 
	* This [README](https://github.com/coq-community/manifesto/wiki/Recommended-Project-Structure) lists all guidelines in one place.

