# Tree Borrows

Forked and adapted from the sibling folder `../stacked_borrows` with the same structure.

* `tree.v`, `locations.v` contain preliminary definitions.
* `lang_base.v`, `expr_semantics.v`, `bor_semantics.v`, and `lang.v` contain the language definition.
* `tree_lemmas.v`, `bor_lemmas.v` and `steps_wf.v` contain basic lemmas to help with the manipulation of trees.
* [WIP] `logical_state.v` defines the invariants and instantiates the simulation relation.
* [WIP] `steps_refl.v` and `steps_opt.v` prove the main execution lemmas.
* [WIP] `behavior.v` defines the notion of contextual refinement and expression well-formedness.
* [WIP] `adequacy.v` contains the resulting adequacy proof.
* [WIP] `examples` contains example optimizations.

In addition, `disjoint.v` provides proofs of simple reorderings (swapping adjacent operations in
a sequential setting) directly against the operational semantics.
