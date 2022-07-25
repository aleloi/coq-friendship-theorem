My ambition is to prove the [Friendship Theorem](https://math.mit.edu/~apost/courses/18.204-2016/18.204_Elizabeth_Walker_final_paper.pdf) in Coq with the [Mathematical Components](https://math-comp.github.io/) library.


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
* The proof:
  * Relate the characteristic polynomial of `sqrt(A)` given that of `A`. I think this can only be done in algebraically closed fields (or maybe fields where `x^2 = a` is always solvable for `x`). The other direction (polynomial for `A^2` from that of `A`) should always hold (and be easier to prove?). Write a pen-and-paper version and go from there.
  * Once I have the `A` charpoly, I have to figure out how to go from identities in a field to identities in `nat`. Pen-and-paper version of this too?
  * Start on the combinatorial part; I have no idea of what `finset`
    or `graph` lemmas I need, and which ones exist..
