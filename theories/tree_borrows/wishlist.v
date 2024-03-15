(** Abstraction layer for trees.
    The goal of this file is that lemmas that appear here expose as few internal details
    as possible. In particular they should all refer to [trees] in their signature (NOT [tree]). *)
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

Lemma trees_contain_trees_lookup_1 trs ev1 ev2 blk tg :
  wf_trees trs ev1 ev2 →
  trees_contain tg trs blk → ∃ it, trees_lookup trs blk tg it.
Proof.
  intros wf.
  rewrite /trees_contain /trees_lookup /trees_at_block.
  specialize (wf blk).
  destruct (trs !! blk) as [tr|]; [|tauto].
  intros Ex.
  destruct (wf tr ltac:(reflexivity) tg Ex) as [it [Unq [Det _]]].
  exists it, tr.
  split; [|split].
  - reflexivity.
  - assumption.
  - assumption.
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
  rewrite /rel_dec.
  rewrite decide_True; [|left; reflexivity].
  rewrite decide_True; [|left; reflexivity].
  reflexivity.
Qed.

Lemma trees_equal_allows_same_access C tr1 tr2 blk ev1 ev2 ev3 ev4 kind acc_tg range :
  (* _even_ nicer preconditions would be nice, but these are already somewhat eeh "optimistic" *)
  trees_equal C tr1 tr2 →
  wf_trees tr1 ev1 ev2 →
  wf_trees tr2 ev3 ev4 →
  is_Some (apply_within_trees (memory_access kind C acc_tg range) blk tr1) → 
  is_Some (apply_within_trees (memory_access kind C acc_tg range) blk tr2).
Admitted.

Lemma wf_tree_tree_unique tr ev1 ev2 :
  wf_tree tr ev1 ev2 →
  ∀ tg,
  tree_contains tg tr →
  tree_unique tg tr.
Proof.
  intros Hwf tg Hcont.
  by destruct (Hwf tg Hcont) as (? & H & _).
Qed.

Lemma trees_equal_preserved_by_access
  {C blk tr1 tr2 tr1' tr2' kind acc_tg range ev1 ev2 ev3 ev4}
  :
  wf_trees tr1 ev1 ev2 →
  wf_trees tr2 ev3 ev4 →
  trees_equal C tr1 tr2 ->
  trees_contain acc_tg tr1 blk ->
  apply_within_trees (memory_access kind C acc_tg range) blk tr1 = Some tr1' ->
  apply_within_trees (memory_access kind C acc_tg range) blk tr2 = Some tr2' ->
  trees_equal C tr1' tr2'.
Proof.
  intros Hwf1 Hwf2 Heq Hcont.
  intros ((tr1blk & tr1blk' & Hlutr1 & Hlutr1' & Hacc1) & Htr1nblk)%apply_within_trees_lookup.
  intros ((tr2blk & tr2blk' & Hlutr2 & Hlutr2' & Hacc2) & Htr2nblk)%apply_within_trees_lookup.
  intros blk'. destruct (decide (blk = blk')) as [<- | Hne];
    last rewrite -Htr1nblk // -Htr2nblk //.
  rewrite Hlutr1' Hlutr2'. econstructor.
  specialize (Heq blk).
  rewrite Hlutr1 Hlutr2 in Heq.
  inversion Heq as [x1 x2 Heq1|]; subst x1 x2. (* yikes *)
  eapply tree_equal_preserved_by_access.
  3, 5, 6: done.
  3: rewrite /trees_contain /trees_at_block Hlutr1 // in Hcont.
  all: eapply wf_tree_tree_unique; (match goal with [ H : wf_trees _ _ _ |- _] => by eapply H end).
Qed.

Lemma apply_trees_access_lookup_general offi cids ev1 ev2 trs kind blk off1 sz acc_tg lu_tg trs' itold :
  apply_within_trees (memory_access kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs ev1 ev2 →
  off1 ≤ offi < off1 + sz →
  trees_lookup trs blk lu_tg itold →
  ∃       itnew, trees_lookup trs' blk lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 apply_access_perm kind (trees_rel_dec trs blk acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App wf InBounds Lookup.
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

Lemma apply_trees_access_lookup_outside blki offi cids ev1 ev2 trs kind blk off1 sz acc_tg lu_tg trs' itold :
  apply_within_trees (memory_access kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs ev1 ev2 →
  ¬ (blki = blk ∧ off1 ≤ offi < off1 + sz) →
  trees_lookup trs blki lu_tg itold →
  ∃       itnew, trees_lookup trs' blki lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 permold = permnew.
Proof.
  intros App wf OutOfBounds Lookup.
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


Lemma apply_trees_access_lookup_same_tag cids ev1 ev2 trs kind blk off1 sz offi tg trs':
  apply_within_trees (memory_access kind cids tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs ev1 ev2 →
  off1 ≤ offi < off1 + sz →
  trees_contain tg trs blk →
  ∃ itold itnew, trees_lookup trs blk tg itold ∧ trees_lookup trs' blk tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 apply_access_perm kind (Child This) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App wf InRange Ex.
  destruct (trees_contain_trees_lookup_1 _ _ _ _ _ wf Ex) as [itold Lookup].
  destruct (apply_trees_access_lookup_general _ _ _ _ _ _ _ _ _ _ _ _ _ App wf InRange Lookup) as [itnew newSpec].
  exists itold, itnew.
  rewrite trees_rel_dec_refl in newSpec.
  split; first assumption.
  apply newSpec.
Qed.


(* TODO move somewhere else *)
Lemma tag_protected_preserved_by_access tg_acc tg_prs l C c trs trs' acc blk off sz ev1 ev2 :
  wf_trees trs ev1 ev2 →
  apply_within_trees (memory_access acc C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for c trs  l tg_prs →
  tag_protected_for c trs' l tg_prs.
Proof.
  intros Hwf Hwithin Hcall (it & Hlu & Hprot & Hinit). 
  destruct (decide (l.1 = blk ∧ (off ≤ l.2 < off + sz))%Z) as [(<- & Hin)|Hout].
  - eapply apply_trees_access_lookup_general in Hlu as (itnew & Hlunew & Heqinit & Heqprot & Hacc); [|done..].
    exists itnew. split; first done.
    split; first by rewrite -Heqprot.
    intros Hperminit.
    assert (protector_is_active (iprot itnew) C) as Hactive.
    { exists c. rewrite -Heqprot. done. }
    apply bind_Some in Hacc as (perm1 & Hacc & (perm2 & Htrigger & [= Heqperm])%bind_Some).
    rewrite -Heqperm /= in Hperminit |- *.
    rewrite (bool_decide_eq_true_2 _ Hactive) /= in Hacc, Htrigger.
    rewrite /apply_access_perm_inner in Hacc.
    destruct (initialized (item_lookup it l.2));
      [ specialize (Hinit eq_refl) | injection Htrigger as -> ].
    all: destruct trees_rel_dec eqn:Hreldec; destruct acc; destruct (perm (item_lookup it l.2)) as [[] []| | |] eqn:Hpermold; simplify_eq; try done;
         repeat (simplify_eq; try done; destruct bool_decide; (try simpl in Htrigger); simplify_eq; try done).
  - eapply apply_trees_access_lookup_outside in Hlu as (itnew & Hlunew & Heqinit & Heqprot & Hacc); [|done..].
    exists itnew. split; first done.
    split; first by rewrite -Heqprot.
    by rewrite -Hacc.
Qed.




















