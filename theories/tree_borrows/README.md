# Tree Borrows

Forked and adapted from the sibling folder `../stacked_borrows` with the same structure.

## Structure

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
 * `equivalence_def.v`: definition of a simple notion of program equivalence for a sequential setting.
 * `low_level.v`: lemmas against the operational semantics.
 * `read_reorder.v`: actual proof of equivalence between two programs in which adjacent reads have been swapped. (Example 18)

## Correspondence with Section 5

Section 5 has three examples, one for deleting reads, one for deleting writes, and one for reordering reads.

### Paragraph 1: Deleting Reads (Example 16)

This example corresponds to the one in  `examples/unprotected/shared_delete_read_escaped.v`.
The Coq example is very close to the one in the paper.
The only difference is that `f` has an extra argument in Coq, which corresponds to the implicit environment that closures have in Rust.

### Paragraph 2: Deleting Writes (Optimizing with Protectors) (Example 17)

This example corresponds to the one in `examples/protected/mutable_reorder_write_up_activated_paper.v`.
This Coq example corresponds very closely to the one in the paper.
The only difference is that `f` and `g` have an extra argument in Coq, which corresponds to the implicit environment that closures have in Rust.

### Paragraph 4: Reordering Reads (Example 18)

This is proven in `read_read_reorder`, particularly in `read_reorder.v`.
These proofs do not use the `simuliris` library, but instead they do a much simpler equivalence proof directly against the operational semantics.
This is because these proofs only hold for a non-concurrent language.
We suspect that they also hold in a concurrent setting, but this would require data race reasoning, and thus we have not proven that.

Specifically, the simple notion of "equivalence after a few steps" is in `equivalence_def.v`.
The proof that the two reads can be reordered is in `read_reorder.v`.
The file `low_level.v` contains low-level lemmas used in `read_reorder.v`

### Other Examples From The Paper
Example 1 is similar to the one shown in `examples/unprotected/mutable_delete_read.v`.
The one shown in Coq has two places where arbitrary unknown functions are called, and Example 1 is just a special case of that, if one instantiates these unknown functions correctly.

We have not shown Example 14, but two examples similar to it:
* `examples/unprotected/shared_delete_read_escaped_coinductive.v` demonstrates reasoning in a loop.
  But note that this does not insert a read if there is none. Also, the tag is not protected.
* `examples/protected/shared_insert_read.v` demonstrates that reads can be inserted on protected tags.


