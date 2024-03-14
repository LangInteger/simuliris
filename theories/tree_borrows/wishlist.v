From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_retag steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors.
From iris.prelude Require Import options.



Lemma trees_contain_trees_lookup tr ev1 ev2 blk tg :
  wf_trees tr ev1 ev2 →
  trees_contain tg tr blk → ∃ it, trees_lookup tr blk tg it.
Proof.
Admitted.

Lemma trees_contain_trees_lookup_2 it tr blk tg :
  trees_lookup tr blk tg it → trees_contain tg tr blk.
Proof.
Admitted.

Lemma apply_trees_access_lookup_same_tag cids ev1 ev2 trs kind blk off1 sz offi t trs':
  apply_within_trees (memory_access kind cids t (off1, sz)) blk trs = Some trs' →
  wf_trees trs ev1 ev2 →
  off1 ≤ offi < off1 + sz →
  ∃ itold itnew, trees_lookup trs blk t itold ∧ trees_lookup trs' blk t itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 apply_access_perm kind This (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Admitted.

Axiom trees_rel_dec : trees → block → tag → tag → rel_pos.

Lemma apply_trees_access_lookup_general cids ev1 ev2 trs kind blk off1 sz offi acc_tg lu_tg trs' itold :
  apply_within_trees (memory_access kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs ev1 ev2 →
  off1 ≤ offi < off1 + sz →
  trees_lookup trs blk lu_tg itold →
  ∃       itnew, trees_lookup trs' blk lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 apply_access_perm kind (trees_rel_dec trs blk acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Admitted.
