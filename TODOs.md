### Build systems and packaging
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

### The proof
* Try to rewrite a part so that it uses `math-comp` `ring` or `fiend`
  tactics. I went though the beginning of `adj2_matrix.v` , but
  couldn't find any pure ring/field goals; everything contained
  matrices or promotion of nats/bools to rings.
* Try `itauto`.
* Make a small hint database of common simplifications for `sauto` and
  try use that to simplify rewriting steps.
	  * Watch the `sauto` doc videos; am I using it wrong?
* There is something called `Tactician`. Does it work?
* (Large and open-ended): get better att the ssreflect tactic language
  by e.g. reading library proofs and rewrite tedious steps to be more
  'vertical'.
* Ask math-comp whether they accept PRs for `simmx_charpoly, det_block`.

### Documentation
* Try generating docs and see what they would look like. [coq-community/manifesto](https://github.com/coq-community/manifesto/wiki/Recommended-Project-Structure) has instructions for how to make it look nice.
* *Write* the documentation.

### Other
* I ran in a few sauto/hammer failures that should be
  reported. E.g. when external hammer provers OOM, they take down
  coqtop, and can't be started again before rebooting (they probably
  leave something in `/tmp` that is not cleaned up).
