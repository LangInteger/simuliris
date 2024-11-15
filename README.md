# Simuliris Coq development

This repository contains the Coq development of Simuliris, additionally including the Tree Borrows Optimization Program Logic, and also some Tree Borrows optimizations not proven via Simuliris.

## Prerequisites

This version is known to compile with:

 - Coq 8.20.0
 - A development version of [Iris](https://gitlab.mpi-sws.org/iris/iris)
 - A recent version of [Coq-Equations](https://github.com/mattam82/Coq-Equations)

## Building from source

When building from source, we recommend to use opam (2.0.0 or newer) for
installing the dependencies.  This requires the following two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

Then run `make` to build everything.

## Structure
Our fork of simuliris in particular includes the upstream version, which proves things about Simuliris, or about data races (in weak memory model), which is part of this archive file but not relevant for the paper.
The Tree Borrows development lives in `theories/tree_borrows` and has its own `README.md`, please consult that.


The project follows the following structure below the `theories` folder:
- `logic` and `base_logic` contain libraries for defining fixpoints as well as general ghost state constructions.
- `simulation` contains the language-generic parts of the framework, in particular the definition of the simulation relation and the general adequacy proof.
    * `language.v` contains our generic language interface.
    * `slsls.v` defines the simulation relation, weakest preconditions for source and target, and general rules for them.
    * `lifting.v` contains general lifting lemmas as well as the definition of the generic "source-safety" judgment for exploiting UB.
    * `closed_sim.v` contains the definition of the closed simulation (removing the call case) used in the adequacy proof.
    * `behavior.v` defines our notion of behavioral refinement and whole-program refinement.
    * `fairness.v` defines our notion of fairness and proves it equivalent to alternative definitions that are crucial for the fairness proof.
    * `fairness_adequacy.v` proves that the simulation relation is fair termination-preserving.
    * `adequacy.v` plugs this all together and shows that Simuliris's simulation in separation logic implies a meta-level simulation, and then derives our general adequacy statement.
    * `gen_log_rel.v` defines a language-generic version of our logical relation on open terms.
- `simulang` contains the definition of SimuLang and program logics and examples for it. It's not the focus of this paper.
- `stacked_borrows` contains the definition of Stacked Borrows and program logics and examples for it. It's not the focus of this paper.
- `tree_borrows` contains the Tree Borrows development. See the `README.md` in that folder for more details.

## More information

See the `README.md` in `theories/tree_borrows`
