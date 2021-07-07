# Simuliris Coq development
This repository contains the Coq development of Simuliris.

## Setup 
This project is known to build with [Coq 8.13.2](https://coq.inria.fr/).
It depends on recent development versions of [std++](https://gitlab.mpi-sws.org/iris/stdpp) and [Iris](https://gitlab.mpi-sws.org/iris/iris), as well as [coq-equations](https://github.com/mattam82/Coq-Equations).


We recommend using [opam](https://opam.ocaml.org/) (version >= 2.0, tested on 2.0.8) for the installation.

Please execute the following instructions in the folder containing this README, replacing `N` with the number of jobs you'd like to use for compilation.
```
opam switch create simuliris 4.11.1
opam switch link simuliris .
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
make -jN builddep
make -jN

```

**TODO**: replace with instructions for using the local clones.

## Structure
The project follows the following structure below the `theories` folder:
- `logic` and `base_logic` contain libraries for defining fixpoints as well as general ghost state constructions.
- `simulation` contains the language-generic parts of the framework, in particular the definition of the simulation relation and the general adequacy proof.
    * `language.v` contains our generic language interface.
    * `slsls.v` defines the simulation relation, weakest preconditions for source and target, and general rules for them.
    * `lifting.v` contains general lifting lemmas as well as the definition of the generic "source-safety" judgment for exploiting UB.
    * `global_sim.v` contains the definition of the global simulation (removing the call case) used in the adequacy proof.
    * `behavior.v` defines our notion of behavioral refinement.
    * `fairness.v` defines our notion of fairness and proves it equivalent to a more traditional characterization.
    * `fairness_adequacy.v` proves that the simulation relation is fair termination-preserving.
    * `adequacy.v` plugs this all together and shows that Simuliris's simulation in separation logic implies a meta-level simulation, and then derives our general adequacy statement.
    * `gen_log_rel.v` defines a language-generic version of our logical relation on open terms.
- `simulang` contains the definition of SimuLang and our program logics and examples for it.
   We have defined two program logics for SimuLang: a "simple" one without support for exploiting non-atomics, and a version extended with support for exploiting non-atomics.
    * `lang.v` contains the definition of SimuLang and its operational semantics, as well as its instantiation of the language interface.
    * `logical_heap.v` contains the ghost state for the heap.
    * `heapbij.v` contains the heap bijection ghost state that is used for both program logics.
    * `globalbij.v` contains support for global variables.
    * `primitive_laws.v` instantiates the simulation relation with SimuLang. It is parametric over an additional invariant on the state and proves basic proof rules for SimuLang. 
    * `gen_val_rel.v` defines a generic value relation for SimuLang that is used by both program logics, but parametric over the notion of relatedness for locations.
    * `log_rel_structural.v`, `gen_refl.v`, and `pure_refl.v` contain conditions on the logical relation as well as general reflexivity proofs used by both program logics.
    * `simple_inv` contains the simple program logic, with no support for exploiting non-atomics.
        + `inv.v` contains the invariant on the state (mainly the bijection, which does not allow to take out ownership) and basic laws.
        + `refl.v` contains the reflexivity theorem.
        + `adequacy.v` derives the proof of contextual refinement.
        + `examples` contains examples using this logic, see below for a list.
    * `na_inv` contains the non-atomic program logic, with added support for exploiting non-atomics.
        + `na_locs.v` contains the pure invariants and reasoning about dataraces.
        + `inv.v` contains the invariant on the state (allowing to take out ownership from the bijection), basic laws, and rules for exploiting non-atomic accesses.
        + `refl.v` contains the reflexivity theorem.
        + `adequacy.v` derives the proof of contextual refinement.
        + `readonly_refl.v` contains a reflexivity theorem for read-only expressions which allows to thread through ownership of exploited locations.
        + `examples` contains examples using this logic, see below for a list.
- `stacked_borrows` contains the port of the Stacked Borrows language and optimizations to Simuliris.
    * `lang_base.v`, `expr_semantics.v`, `bor_semantics.v`, and `lang.v` contain the language definition.
    * `logical_state.v` defines the invariants and instantiates the simulation relation.
    * `steps_refl.v` and `steps_opt.v` prove the main execution lemmas.
    * `behavior.v` defines the notion of contextual refinement and expression well-formedness.
    * `adequacy.v` contains the resulting adequacy proof.
    * `examples` contains example optimizations, see below.

## Examples and case studies
We have conducted a number of case studies and examples for the simple SimuLang logic, the non-atomic SimuLang logic, and the Stacked Borrows logic.

### Simple SimuLang logic
These examples can be found in `theories/simulang/simple_inv/examples/`.

TODO

### Non-atomic SimuLang logic
These examples can be found in `theories/simulang/na_inv/examples/`.

TODO

### Stacked Borrows logic
These examples can be found in `theories/stacked_borrows/examples`

TODO

## Theorems and definitions referenced in the paper

TODO
