(** Abstraction layer for trees.
    The goal of this file is that lemmas that appear here expose as few internal details
    as possible. In particular they should all refer to [trees] in their signature (NOT [tree]). 

    At least that was the plan. Turns out sometimes you need the single-tree lemmas.*)
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors trees_equal.
From iris.prelude Require Import options.

(***** not part of the API *****)
Lemma trees_at_block_projection trs tr blk P :
  trees_at_block P trs blk ->
  trs !! blk = Some tr ->
  P tr.
Proof.
  rewrite /trees_contain /trees_at_block.
  destruct (trs !! blk); [|tauto].
  intros Ex Eq. injection Eq; intros; subst. assumption.
Qed.
(***** not part of the API *****)

Lemma trees_contain_trees_lookup_1 trs blk tg :
  wf_trees trs →
  trees_contain tg trs blk → ∃ it, trees_lookup trs blk tg it.
Proof.
  intros (wf&_).
  rewrite /trees_contain /trees_lookup /trees_at_block.
  specialize (wf blk).
  destruct (trs !! blk) as [tr|]; [|tauto].
  intros Ex.
  specialize (wf tr ltac:(reflexivity) tg Ex) as Unq.
  destruct (unique_lookup _ _ Unq) as (it & Det).
  exists it, tr. done.
Qed.

Lemma trees_contain_trees_lookup_2 it trs blk tg :
  trees_lookup trs blk tg it → trees_contain tg trs blk.
Proof.
  rewrite /trees_lookup /trees_contain /trees_at_block.
  destruct (trs !! blk); [|intro H; destruct H as [?[??]]; discriminate].
  intro H. destruct H as [?[Eqt Lookup]].
  injection Eqt; intros; subst.
  apply Lookup.
Qed.

Definition trees_rel_dec (trs : trees) blk tg tg' :=
  match trs !! blk with
  | None => Child This
  | Some tr => rel_dec tr tg tg'
  end.

Lemma trees_rel_dec_refl trs blk tg :
  trees_rel_dec trs blk tg tg = Child This.
Proof.
  rewrite /trees_rel_dec.
  destruct (trs !! blk); [|reflexivity].
  apply rel_dec_refl.
Qed.

Lemma trees_equal_allows_same_access C tr1 tr2 blk kind acc_tg range :
  (* _even_ nicer preconditions would be nice, but these are already somewhat eeh "optimistic" *)
  trees_equal C tr1 tr2 →
  wf_trees tr1 →
  wf_trees tr2 →
  trees_contain acc_tg tr1 blk →
  is_Some (apply_within_trees (memory_access kind C acc_tg range) blk tr1) → 
  is_Some (apply_within_trees (memory_access kind C acc_tg range) blk tr2).
Proof.
  intros Heq Hwf1 Hwf2 Hcont [x (trr1&H1&(trr1'&H2&[= <-])%bind_Some)%bind_Some].
  specialize (Heq blk).
  rewrite H1 in Heq. inversion Heq as [? trr2 Heqr q H2'|]; simplify_eq.
  eapply mk_is_Some, tree_equal_allows_same_access in H2 as (trr2'&Htrr2').
  * eexists. rewrite /apply_within_trees -H2' /= Htrr2' /= //.
  * intros tg. eapply wf_tree_tree_unique. eapply Hwf1, H1.
  * apply Heqr.
  * eapply wf_tree_tree_unique. 1: eapply Hwf1, H1.
    rewrite /trees_contain /trees_at_block H1 // in Hcont.
Qed.


Lemma trees_equal_preserved_by_access
  {C blk tr1 tr2 tr1' tr2' kind acc_tg range}
  :
  wf_trees tr1 →
  wf_trees tr2 →
  trees_equal C tr1 tr2 ->
  trees_contain acc_tg tr1 blk ->
  apply_within_trees (memory_access kind C acc_tg range) blk tr1 = Some tr1' ->
  apply_within_trees (memory_access kind C acc_tg range) blk tr2 = Some tr2' ->
  trees_equal C tr1' tr2'.
Proof.
  intros (Hwf1&_) (Hwf2&_) Heq Hcont.
  intros ((tr1blk & tr1blk' & Hlutr1 & Hlutr1' & Hacc1) & Htr1nblk)%apply_within_trees_lookup.
  intros ((tr2blk & tr2blk' & Hlutr2 & Hlutr2' & Hacc2) & Htr2nblk)%apply_within_trees_lookup.
  intros blk'. destruct (decide (blk = blk')) as [<- | Hne];
    last rewrite -Htr1nblk // -Htr2nblk //.
  rewrite Hlutr1' Hlutr2'. econstructor.
  specialize (Heq blk).
  rewrite Hlutr1 Hlutr2 in Heq.
  inversion Heq as [x1 x2 Heq1|]; subst x1 x2. (* yikes *)
  eapply tree_equal_preserved_by_memory_access.
  3, 5, 6: done.
  3: rewrite /trees_contain /trees_at_block Hlutr1 // in Hcont.
  all: eapply wf_tree_tree_unique; 
    (match goal with [ H : each_tree_wf _ |- _] => by eapply H end).
Qed.

Lemma apply_trees_access_lookup_general b offi cids trs kind blk off1 sz acc_tg lu_tg trs' itold :
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  off1 ≤ offi < off1 + sz →
  trees_lookup trs blk lu_tg itold →
  ∃       itnew, trees_lookup trs' blk lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 maybe_non_children_only b (apply_access_perm kind) (trees_rel_dec trs blk acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App (wf&_) InBounds Lookup.
  rewrite /apply_within_trees in App.
  rewrite bind_Some in App.
  destruct App as [tr [trSome Acc]].
  rewrite bind_Some in Acc.
  destruct Acc as [tr' [Acc Out]].
  injection Out; intros; subst; clear Out.
  assert (tree_contains lu_tg tr) as Ex. {
    eapply trees_at_block_projection; [|eassumption].
    eapply trees_contain_trees_lookup_2.
    eassumption.
  }
  assert (tree_item_determined lu_tg itold tr) as Det. {
    destruct Lookup as [trbis [trsLookup trLookup]].
    assert (trbis = tr) by congruence. subst.
    apply trLookup.
  }
  destruct (apply_access_spec_per_node Ex Det Acc) as [it' [itAcc [Ex' Det']]].
  exists it'.
  split; [|split; [|split]].
  - exists tr'. split; [apply lookup_insert|]. split; assumption.
  - eapply item_apply_access_preserves_metadata.
    symmetry. eassumption.
  - eapply item_apply_access_preserves_metadata.
    symmetry. eassumption.
  - rewrite /item_apply_access in itAcc.
    symmetry in itAcc. rewrite bind_Some in itAcc.
    destruct itAcc as [perms' [perms'Spec Same]].
    injection Same; intros; subst; clear Same.
    pose proof (mem_apply_range'_spec _ _ offi _ _ perms'Spec) as ThisLocation.
    destruct (decide _); [|unfold range'_contains in *; simpl in *; lia].
    destruct ThisLocation as [perm [permSome permAcc]].
    simpl.
    rewrite /trees_rel_dec trSome.
    assert (itag itold = lu_tg). { eapply tree_determined_specifies_tag; [|eassumption]; assumption. }
    subst.
    rewrite permAcc.
    rewrite /item_lookup /= permSome //=.
Qed.

Lemma apply_trees_access_lookup_outside blki offi cids trs kind blk off1 sz acc_tg lu_tg trs' itold b :
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  ¬ (blki = blk ∧ off1 ≤ offi < off1 + sz) →
  trees_lookup trs blki lu_tg itold →
  ∃       itnew, trees_lookup trs' blki lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 permold = permnew.
Proof.
  intros App (wf&_) OutOfBounds Lookup.
  rewrite /apply_within_trees in App.
  rewrite bind_Some in App.
  destruct App as [tr [trSome Acc]].
  rewrite bind_Some in Acc.
  destruct Acc as [tr' [Acc Out]].
  injection Out; intros; subst; clear Out.
  destruct (decide (blk = blki)) as [->|Hne]; last first.
  { destruct Lookup as (it & Hit1 & Hit2). exists itold. split_and!; try done.
    exists it; split; last done.
    by rewrite lookup_insert_ne. }
  assert (tree_contains lu_tg tr) as Ex. {
    eapply trees_at_block_projection; [|eassumption].
    eapply trees_contain_trees_lookup_2.
    eassumption.
  }
  assert (tree_item_determined lu_tg itold tr) as Det. {
    destruct Lookup as [trbis [trsLookup trLookup]].
    assert (trbis = tr) by congruence. subst.
    apply trLookup.
  }
  destruct (apply_access_spec_per_node Ex Det Acc) as [itnew [itAcc [Ex' Det']]].
  rewrite /item_apply_access in itAcc. symmetry in itAcc.
  apply bind_Some in itAcc as (permsnew&Hpermsnew&[= Hitnew]).
  exists itnew. split.
  { exists tr'. split; first by rewrite lookup_insert. done. }
  subst itnew. simpl. split_and!; try done.
  rewrite /item_lookup; simpl. f_equal.
  eapply (mem_apply_range'_spec _ _ offi) in Hpermsnew.
  destruct (decide (range'_contains _ _)) as [Hinrange|_]; last done.
  exfalso. eapply OutOfBounds. split; first done. apply Hinrange.
Qed.


Lemma apply_trees_access_lookup_same_tag cids trs kind blk off1 sz offi tg trs' b:
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs  →
  off1 ≤ offi < off1 + sz →
  trees_contain tg trs blk →
  ∃ itold itnew, trees_lookup trs blk tg itold ∧ trees_lookup trs' blk tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 maybe_non_children_only b (apply_access_perm kind) (Child This) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App wf InRange Ex.
  destruct (trees_contain_trees_lookup_1 _ _ _ wf Ex) as [itold Lookup].
  destruct (apply_trees_access_lookup_general _ _ _ _ _ _ _ _ _ _ _ _ App wf InRange Lookup) as [itnew newSpec].
  exists itold, itnew.
  rewrite trees_rel_dec_refl in newSpec.
  split; first assumption.
  apply newSpec.
Qed.

Lemma tree_lookup_IsTag tr tg it : tree_lookup tr tg it → IsTag tg it.
Proof.
  intros (H1 & H2).
  eapply exists_node_eqv_existential in H1 as (it2 & Hit2 & Histag).
  eapply every_node_eqv_universal in H2; last done.
  by rewrite -H2.
Qed.

Lemma tree_lookup_unique tr tg it1 it2 : tree_lookup tr tg it1 → tree_lookup tr tg it2 → it1 = it2.
Proof.
  intros Hlu (H1 & H2).
  eapply every_node_eqv_universal in H2; first apply H2.
  1: by eapply tree_lookup_IsTag.
  eapply exists_determined_exists; first done.
  apply Hlu.
Qed.

Lemma apply_trees_access_lookup_general_rev offi cids trs kind blk off1 sz acc_tg lu_tg trs' itnew b :
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  off1 ≤ offi < off1 + sz →
  trees_lookup trs' blk lu_tg itnew →
  ∃       itold, trees_lookup trs blk lu_tg itold ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 maybe_non_children_only b (apply_access_perm kind) (trees_rel_dec trs blk acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App WFold InBounds Lookup.
  assert (wf_trees trs') as WFnew.
  { eapply apply_within_trees_wf; try done. eapply memory_access_tag_count. }
  pose proof App as (trold&Htrold&(trnew&Htrnew&[= <-])%bind_Some)%bind_Some.
  destruct Lookup as (tr'&Htr'&Hlookup).
  rewrite lookup_insert in Htr'. injection Htr' as <-.
  pose proof Hlookup as (Hunq&_).
  eapply wf_tree_tree_unique in Hunq; last eapply WFnew, lookup_insert.
  rewrite /tree_unique in Hunq. erewrite <-memory_access_tag_count in Hunq; last done.
  pose proof (unique_exists Hunq) as Hcont.
  apply unique_lookup in Hunq as (itold&Hdet).
  eapply (apply_trees_access_lookup_general _ offi) in App.
  2: done. 3: by eexists. 2: lia.
  destruct App as (itnew' & (trnew' & Htrnew' & Hitnew') & Hperms).
  assert (trnew' = trnew) as ->.
  { rewrite lookup_insert in Htrnew'. congruence. }
  assert (itnew' = itnew) as -> by by eapply tree_lookup_unique.
  exists itold. split; last done.
  by exists trold.
Qed.

Lemma apply_trees_access_lookup_outside_rev blki offi cids trs kind blk off1 sz acc_tg lu_tg trs' itnew b:
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  ¬ (blki = blk ∧ off1 ≤ offi < off1 + sz) →
  trees_lookup trs' blki lu_tg itnew →
  ∃       itold, trees_lookup trs blki lu_tg itold ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 permold = permnew.
Proof.
  intros App wf OutOfBounds Lookup.
  assert (wf_trees trs') as wf'.
  { eapply apply_within_trees_wf; try done.
    intros ????. by eapply memory_access_tag_count. }
  pose proof App as App2.
  rewrite /apply_within_trees in App.
  rewrite bind_Some in App.
  destruct App as [tr [trSome Acc]].
  rewrite bind_Some in Acc.
  destruct Acc as [tr' [Acc Out]].
  injection Out; intros; subst; clear Out.
  destruct (decide (blk = blki)) as [->|Hne]; last first.
  { destruct Lookup as (it & Hit1 & Hit2). exists itnew. split_and!; try done.
    exists it; split; last done.
    by rewrite lookup_insert_ne in Hit1. }
  assert (tree_contains lu_tg tr') as Ex. {
    eapply trees_at_block_projection.
    1: eapply trees_contain_trees_lookup_2; eassumption.
    by eapply lookup_insert.
  }
  assert (tree_item_determined lu_tg itnew tr') as NewDet. {
    destruct Lookup as (? & Heq & Hlu). rewrite lookup_insert in Heq.
    injection Heq as <-. apply Hlu.
  }
  assert (tree_unique lu_tg tr) as UnqPre.
  { eapply wf_tree_tree_unique in Ex. 2: eapply wf', lookup_insert.
    rewrite /tree_unique. erewrite tree_apply_access_same_count.
    1: apply Ex.
    apply Acc. }
  pose proof UnqPre as (itold & Hdetold)%unique_lookup.
  assert (trees_lookup trs blki lu_tg itold) as Hluold.
  { exists tr; split; first done. split; last done. by eapply unique_exists. }
  pose proof Hluold as Hluold2.
  eapply apply_trees_access_lookup_outside in Hluold as (itnew' & Hlu2 & HH2).
  2: apply App2.
  - exists itold; split; first done.
    enough (itnew' = itnew) as <- by eapply HH2.
    eapply (tree_lookup_unique tr' lu_tg).
    + destruct Hlu2 as (? & Hx & Hy).
      rewrite lookup_insert in Hx. congruence.
    + destruct Lookup as (? & Hx & Hy).
      rewrite lookup_insert in Hx. congruence.
  - done.
  - apply OutOfBounds.
Qed.

(* Reverse lifting to single trees.
   This is a roundabout of proving these, but we started with the lemmas above and this way there is the least refactoring effort. *)


Lemma wf_tree_wf_singleton tr : wf_tree tr → wf_trees (singletonM xH tr).
Proof.
  split.
  - intros blk ? (<-&<-)%lookup_singleton_Some. done.
  - intros ???? tg (<-&<-)%lookup_singleton_Some (<-&<-)%lookup_singleton_Some. done.
Qed.

Lemma tree_access_lookup_general offi cids tr kind off1 sz acc_tg lu_tg tr' itold b :
  memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz) tr = Some tr' →
  wf_tree tr →
  off1 ≤ offi < off1 + sz →
  tree_lookup tr lu_tg itold →
  ∃       itnew, tree_lookup tr' lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 maybe_non_children_only b (apply_access_perm kind) (rel_dec tr acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App WFold InBounds Lookup.
  odestruct (apply_trees_access_lookup_general _ _ _ _ _ xH) as (it&H1&H2&H3&H4).
  2: by eapply wf_tree_wf_singleton.
  - rewrite /apply_within_trees lookup_singleton /=. erewrite App. rewrite /= insert_singleton. done.
  - done.
  - exists tr. split; first by eapply lookup_singleton. done.
  - exists it. split_and; try done.
    destruct H1 as (tr1'&H1&H1'). rewrite lookup_singleton in H1. injection H1 as <-. done.
Qed.

Lemma tree_access_lookup_outside offi cids tr kind off1 sz acc_tg lu_tg tr' itold b :
  memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz) tr = Some tr' →
  wf_tree tr →
  ¬ (off1 ≤ offi < off1 + sz) →
  tree_lookup tr lu_tg itold →
  ∃       itnew, tree_lookup tr' lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 permold = permnew.
Proof.
  intros App WFold InBounds Lookup.
  odestruct (apply_trees_access_lookup_outside xH offi _ _ _ xH) as (it&H1&H2&H3&H4).
  2: by eapply wf_tree_wf_singleton.
  - rewrite /apply_within_trees lookup_singleton /=. erewrite App. rewrite /= insert_singleton. done.
  - intros (H1&H2). done.
  - exists tr. split; first by eapply lookup_singleton. done.
  - exists it. split_and; try done.
    destruct H1 as (tr''&H1&H1'). rewrite lookup_singleton in H1. injection H1 as <-. done.
Qed.

Lemma tree_access_lookup_general_rev offi cids tr kind off1 sz acc_tg lu_tg tr' itnew b :
  memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz) tr = Some tr' →
  wf_tree tr →
  off1 ≤ offi < off1 + sz →
  tree_lookup tr' lu_tg itnew →
  ∃       itold, tree_lookup tr lu_tg itold ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 maybe_non_children_only b (apply_access_perm kind) (rel_dec tr acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App WFold InBounds Lookup.
  odestruct (apply_trees_access_lookup_general_rev _ _ _ _ xH) as (it&H1&H2&H3&H4).
  2: by eapply wf_tree_wf_singleton.
  - rewrite /apply_within_trees lookup_singleton /=. erewrite App. rewrite /= insert_singleton. done.
  - done.
  - exists tr'. split; first by eapply lookup_singleton. done.
  - exists it. split_and; try done.
    destruct H1 as (tr''&H1&H1'). rewrite lookup_singleton in H1. injection H1 as <-. done.
Qed.

Lemma tree_access_lookup_outside_rev offi cids tr kind off1 sz acc_tg lu_tg tr' itnew b :
  memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz) tr = Some tr' →
  wf_tree tr →
  ¬ (off1 ≤ offi < off1 + sz) →
  tree_lookup tr' lu_tg itnew →
  ∃       itold, tree_lookup tr lu_tg itold ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 permold = permnew.
Proof.
  intros App WFold InBounds Lookup.
  odestruct (apply_trees_access_lookup_outside_rev xH offi _ _ _ xH) as (it&H1&H2&H3&H4).
  2: by eapply wf_tree_wf_singleton.
  - rewrite /apply_within_trees lookup_singleton /=. erewrite App. rewrite /= insert_singleton. done.
  - intros (H1&H2). done.
  - exists tr'. split; first by eapply lookup_singleton. done.
  - exists it. split_and; try done.
    destruct H1 as (tr''&H1&H1'). rewrite lookup_singleton in H1. injection H1 as <-. done.
Qed.


(* Some more facts about trees. These could be refactored, maybe? *)

Lemma apply_access_perm_read_not_disabled b rel isprot itmo itmn :
  maybe_non_children_only b (apply_access_perm AccessRead) rel isprot itmo = Some itmn →
  perm itmo = Disabled →
  perm itmn = Disabled.
Proof.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  - intros (pin&H1&(pp&H2&[= <-])%bind_Some)%bind_Some Hdis.
    simpl in Hdis,H1,H2|-*.
    repeat (case_match; simplify_eq; try done).
  - congruence.
Qed.

Lemma apply_access_perm_read_frozen b rel isprot itmo itmn :
  maybe_non_children_only b (apply_access_perm AccessRead) rel isprot itmo = Some itmn →
  perm itmo = Frozen →
  perm itmn = Frozen.
Proof.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  - intros (pin&H1&(pp&H2&[= <-])%bind_Some)%bind_Some Hdis.
    simpl in Hdis,H1,H2|-*.
    repeat (case_match; simplify_eq; try done).
  - congruence.
Qed.

Lemma apply_access_perm_read_conflicted b rel isprot itmo itmn im :
  maybe_non_children_only b (apply_access_perm AccessRead) rel isprot itmo = Some itmn →
  perm itmo = Reserved im ResConflicted →
  perm itmn = Reserved im ResConflicted.
Proof.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  - intros (pin&H1&(pp&H2&[= <-])%bind_Some)%bind_Some Hdis.
    simpl in Hdis,H1,H2|-*.
    repeat (case_match; simplify_eq; try done).
  - congruence.
Qed.

Lemma apply_access_perm_read_reserved_backwards b rel isprot itmo itmn im acc :
  maybe_non_children_only b (apply_access_perm AccessRead) rel isprot itmo = Some itmn →
  perm itmn = Reserved im acc → ∃ acc,
  perm itmo = Reserved im acc.
Proof.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  - intros (pin&H1&(pp&H2&[= <-])%bind_Some)%bind_Some Hdis.
    simpl in Hdis,H1,H2|-*.
    repeat (case_match; simplify_eq; try done; try by eexists).
  - intros [= ->] ->. by eexists.
Qed.

Lemma apply_access_perm_read_initialized b rel isprot itmo itmn :
  maybe_non_children_only b (apply_access_perm AccessRead) rel isprot itmo = Some itmn →
  initialized itmo = PermInit →
  initialized itmn = PermInit.
Proof.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq.
  - intros (pin&H1&(pp&H2&[= <-])%bind_Some)%bind_Some Hdis.
    simpl in Hdis,H1,H2|-*.
    repeat (case_match; simplify_eq; try done).
  - congruence.
Qed.

Lemma rel_dec_concat_cousin tr t1 t2 t3 :
  wf_tree tr →
  tree_unique t1 tr →
  tree_unique t2 tr →
  tree_unique t3 tr →
  ∀ b,
  rel_dec tr t1 t2 = Foreign Cousin →
  rel_dec tr t2 t3 = Foreign (Parent b) → 
  rel_dec tr t1 t3 = Foreign Cousin.
Proof.
  intros Hwf Hu1 Hu2 Hu3 b.
  eapply unique_exists in Hu1 as Hc1.
  eapply unique_exists in Hu2 as Hc2.
  eapply unique_exists in Hu3 as Hc3.
  intros H1 H2.
  rewrite /rel_dec in H2|-*.
  rewrite !(decide_bool_decide (ImmediateParentChildIn _ _ _)) in H2|-*. repeat destruct decide; try done.
  1-2: rewrite /rel_dec in H1; repeat destruct decide; try done; exfalso; eauto using ParentChild_transitive.
  exfalso. eapply cousins_have_disjoint_children in H1; first done.
  1-3: eapply Hwf. 1: exact Hc3. 1-2: done. all: done.
Qed.

Lemma rel_dec_concat_parent tr t1 t2 t3 :
  wf_tree tr →
  tree_unique t1 tr →
  tree_unique t2 tr →
  tree_unique t3 tr →
  ∀ b1 b2,
  rel_dec tr t1 t2 = Foreign (Parent b1) →
  rel_dec tr t2 t3 = Foreign (Parent b2) → 
  ∃ b3,
  rel_dec tr t1 t3 = Foreign (Parent b3).
Proof.
  intros Hwf Hu1 Hu2 Hu3 b1 b2.
  eapply unique_exists in Hu1 as Hc1.
  eapply unique_exists in Hu2 as Hc2.
  eapply unique_exists in Hu3 as Hc3.
  rewrite /rel_dec.
  repeat destruct decide; try done.
  all: try by (exfalso; eauto using ParentChild_transitive).
  all: intros _ _; eexists; try done.
Qed.

Lemma rel_dec_concat_foreign tr t1 t2 t3 :
  wf_tree tr →
  tree_unique t1 tr →
  tree_unique t2 tr →
  tree_unique t3 tr →
  ∀ p1 b2,
  rel_dec tr t1 t2 = Foreign p1 →
  rel_dec tr t2 t3 = Foreign (Parent b2) → 
  ∃ p2,
  rel_dec tr t1 t3 = Foreign p2.
Proof.
  intros H0 H1 H2 H3 [p1|] b2 H4 H5.
  - edestruct (rel_dec_concat_parent tr t1 t2 t3) as (bb&Hbb); try done.
    by eexists.
  - exists Cousin. eapply rel_dec_concat_cousin; last done; done.
Qed.

Lemma rel_dec_parent_parent_is_parent tr ttop tmid tbot d1 d2 fp :
  wf_tree tr → tree_contains ttop tr → tree_contains tmid tr → tree_contains tbot tr →
  rel_dec tr ttop tbot = Foreign (Parent d1) →
  rel_dec tr tmid tbot = Foreign (Parent d2) →
  rel_dec tr ttop tmid = Foreign fp →
  ∃ d3, fp = Parent d3.
Proof.
  intros Hwf Hu1 Hu2 Hu3. unfold rel_dec at 1 2.
  destruct (decide (ParentChildIn tbot ttop tr)) as [HPC1|HPC1]; try done.
  destruct (decide (ParentChildIn ttop tbot tr)) as [HPC2|HPC2]; try done. intros _.
  destruct (decide (ParentChildIn tbot tmid tr)) as [HPC3|HPC3]; try done.
  destruct (decide (ParentChildIn tmid tbot tr)) as [HPC4|HPC4]; try done. intros _.
  intros Hfgn. destruct fp; first by eexists.
  eapply cousins_have_disjoint_children in Hfgn. 5-6: done. 1: done. all: by eapply Hwf.
Qed.
