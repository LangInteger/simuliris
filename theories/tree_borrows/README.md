# Tree Borrows

Forked and adapted from the sibling folder `../stacked_borrows` with the same structure.

* `tree.v`, `locations.v` contain preliminary definitions.
* `lang_base.v`, `expr_semantics.v`, `bor_semantics.v`, and `lang.v` contain the language definition.
* `tree_lemmas.v`, `bor_lemmas.v`, `steps_wf.v` and `steps_preserve.v` contain basic lemmas to help with the manipulation of trees.
* `defs.v` defines well-formedness invariants for trees.
* `logical_state.v` defines the invariants and instantiates the simulation relation,
  using among others a notion of when trees are similar in `trees_equal/`.
* `steps_refl.v` and `steps_opt.v` prove the main execution lemmas.
* `behavior.v` defines the notion of contextual refinement and expression well-formedness.
* `adequacy.v` contains the resulting adequacy proof.
* `examples/` contains example optimizations, further subdivided into
  - `unprotected/` optimizations, which are program transformations that can be applied even in the absence of protectors,
  - `protected/` optimizations, which require a protector to hold,
  - `impossible/` optimizations used to hold under Stacked Borrows,
    but we know of counter-examples under Tree Borrows.

In addition, `read_read_reorder/` provides proofs of simple reorderings
(swapping adjacent operations in a sequential setting)
directly against the operational semantics.
It is subdivided into
 * `refinement_def.v`: definition of a bisimulation relation for a sequential setting.
 * `low_level.v`: lemmas against the operational semantics.
 * `refinement.v`: actual proof of bisimulation between two programs in which adjacent reads have been swapped.
