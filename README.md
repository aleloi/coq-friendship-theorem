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
	* This [SO post](https://stackoverflow.com/questions/53822753/coqide-error-with-exporting-modules-in-the-same-library) about importing 
	* This [README](https://github.com/coq-community/manifesto/wiki/Recommended-Project-Structure) lists all guidelines in one place.

* The proof:
  * Type out the proof that `no_hub` and `k=2` implies `False`.
  * Learn about finite set quantifiers and reflections to Prop
    quantifiers; do the proof that `no_hub -> False` implies `hub`
    (maybe it's easier to reformulate from `sig` types to `exists`?)
  * Matrices: Maybe just redo/rewrite the proofs for `A *m A` and
    change the matrix dims? Otherwise, I think it's enough that
    `castmx A *m castmx A = castmx (A *m A)` and `castmx A + castmx B
    = castmx (A + B)`. Maybe something about `cast_ord` being a
    bijection, so the sums in the product don't change?
  
