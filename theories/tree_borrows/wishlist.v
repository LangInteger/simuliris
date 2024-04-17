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

(* TODO move somewhere else *)
Lemma tag_protected_preserved_by_access tg_acc tg_prs l C c trs trs' acc blk off sz b :
  wf_trees trs →
  apply_within_trees (memory_access_maybe_nonchildren_only b acc C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for c trs  l tg_prs →
  tag_protected_for c trs' l tg_prs.
Proof.
  intros Hwf Hwithin Hcall (it & Hlu & Hprot & Hstrong & Hinit).
  destruct (decide (l.1 = blk ∧ (off ≤ l.2 < off + sz))%Z) as [(<- & Hin)|Hout].
  - eapply apply_trees_access_lookup_general in Hlu as (itnew & Hlunew & Heqinit & Heqprot & Hacc); [|done..].
    exists itnew. split; first done. rewrite -Heqprot.
    do 2 (split; first done).
    intros Hperminit.
    assert (protector_is_active (iprot itnew) C) as Hactive.
    { exists c. rewrite -Heqprot. done. }
    edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq].
    2: { erewrite Heq in Hacc. injection Hacc as Hacc. rewrite -Hacc.
         eapply Hinit. rewrite Hacc. done. }
    rewrite Heq in Hacc.
    apply bind_Some in Hacc as (perm1 & Hacc & (perm2 & Htrigger & [= Heqperm])%bind_Some).
    rewrite -Heqperm /= in Hperminit |- *.
    rewrite (bool_decide_eq_true_2 _ Hactive) /= in Hacc, Htrigger.
    rewrite /apply_access_perm_inner in Hacc.
    destruct (initialized (item_lookup it l.2));
      [ specialize (Hinit eq_refl) | injection Htrigger as -> ].
    all: destruct trees_rel_dec eqn:Hreldec; destruct acc; destruct (perm (item_lookup it l.2)) as [[] []| | |] eqn:Hpermold; simplify_eq; try done;
         repeat (simplify_eq; try done; (try simpl in Htrigger); simplify_eq; try done).
  - eapply apply_trees_access_lookup_outside in Hlu as (itnew & Hlunew & Heqinit & Heqprot & Hacc); [|done..].
    exists itnew. split; first done. rewrite -Heqprot.
    do 2 (split; first done).
    by rewrite -Hacc.
Qed.

(* TODO move somewhere else *)
Lemma tag_protected_preserved_by_delete tg_acc tg_prs l C c trs trs' blk off sz :
  wf_trees trs →
  apply_within_trees (memory_deallocate C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for c trs l tg_prs →
  tag_protected_for c (delete blk trs') l tg_prs.
Proof.
  intros Hwf Hwithin Hcall Hpreprot.
  rewrite apply_within_trees_bind in Hwithin.
  pose proof Hwithin as (postread&Hread&Hdealloc)%bind_Some.
  eapply tag_protected_preserved_by_access in Hread as (it & (tr & Htr & Hlu) & Hprot & Hstrong & Hinit); [|done..].
  destruct (decide (l.1 = blk)) as [<-|Hout].
  - exfalso.
    rewrite /apply_within_trees Htr /= in Hdealloc.
    pose proof Hdealloc as (okcheck&Hcheck%mk_is_Some&[= <-])%bind_Some. clear Hdealloc.
    rewrite join_success_condition every_node_map every_node_eqv_universal /= in Hcheck.
    pose proof (tree_lookup_correct_tag Hlu) as <-.
    ospecialize (Hcheck it _); first by eapply tree_lookup_to_exists_node.
    eapply is_Some_if_neg in Hcheck.
    rewrite (bool_decide_eq_true_2 _ Hstrong) /=bool_decide_eq_false in Hcheck.
    eapply Hcheck.
    exists c. done.
  - exists it. split; last done. exists tr. split; last done.
    rewrite lookup_delete_ne //.
    pose proof Hdealloc as (?&_&(?&_&[= <-])%bind_Some)%bind_Some.
    by rewrite lookup_insert_ne.
Qed.

Lemma loc_controlled_access_outside l tk sc cids σ σ' kind blk off1 sz acc_tg lu_tg b Mcall :
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ !! l = shp σ' !! l →
  scs σ = scs σ' →
  state_wf σ →
  ¬ (l.1 = blk ∧ off1 ≤ l.2 < off1 + sz) →
  loc_controlled Mcall l lu_tg tk sc σ →
  loc_controlled Mcall l lu_tg tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hnin Hlc.
  rewrite /loc_controlled.
  destruct tk as [|act|] eqn:Heq; simpl.
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_outside_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done. by rewrite Heq3.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold & Htrold & Hluold).
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew & Htrnew & Hlunew).
      exists it, trnew. do 2 (split; first done).
      split; first by rewrite -Heq3.
      split; first by rewrite -Heq3.
      intros itnew' t' Hit'.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_outside_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      specialize (Hothers _ _ Hitoldlu').
      assert (rel_dec trnew lu_tg t' = rel_dec trold lu_tg t') as Hreldec.
      { destruct (decide (l.1 = blk)) as [<- | Hne].
        - rewrite /apply_within_trees Hx /= in Happly.
          apply bind_Some in Happly as (newtr & H1 & [= H2]).
          rewrite -H2 lookup_insert in Htrnew.
          erewrite (access_same_rel_dec H1). congruence.
        - apply bind_Some in Happly as (itwrong & Hwrong & (y & Hy & [= Hacc])%bind_Some).
          rewrite -Hacc lookup_insert_ne // Hx in Htrnew. congruence. }
      rewrite rel_dec_flip2 in Hothers. rewrite rel_dec_flip2.
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2). rewrite -Hperm2. apply Hothers.
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_outside_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done. by rewrite Heq3 Heq2 Heq_scs.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold & Htrold & Hluold). rewrite /bor_state_own /= in Hownold.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hstuff).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew & Htrnew & Hlunew).
      exists it, trnew. do 2 (split; first done).
      destruct Hstuff as (Hsame & Hothers).
      split_and!; first by rewrite -Heq3.
      split_and!; first by rewrite -Heq3 -Heq2 -Heq_scs.
      intros itnew' t' Hit'.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_outside_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      specialize (Hothers _ _ Hitoldlu').
      assert (rel_dec trnew lu_tg t' = rel_dec trold lu_tg t') as Hreldec.
      { destruct (decide (l.1 = blk)) as [<- | Hne].
        - rewrite /apply_within_trees Hx /= in Happly.
          apply bind_Some in Happly as (newtr & H1 & [= H2]).
          rewrite -H2 lookup_insert in Htrnew.
          erewrite (access_same_rel_dec H1). congruence.
        - apply bind_Some in Happly as (itwrong & Hwrong & (y & Hy & [= Hacc])%bind_Some).
          rewrite -Hacc lookup_insert_ne // Hx in Htrnew. congruence. }
      rewrite rel_dec_flip2 in Hothers. rewrite rel_dec_flip2.
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2). rewrite -Hperm2. apply Hothers.
  - destruct Hlc as (Hownold & Hscold); first done.
    split; last by rewrite -Heq_shp.
    destruct Hownold as (itold & trold & Hluold & Htrold & Hisinit & Hsame & Hothers).
    assert (trees_lookup σ.(strs) l.1 lu_tg itold) as Hsluold by by exists trold.
    eapply apply_trees_access_lookup_outside in Hsluold; [|eapply Happly|eapply Hwf|done].
    destruct Hsluold as (itnew & (trnew & Htrnew & Hlunew) & (Hinitold & Hprotold & Hpermold)).
    exists itnew, trnew. do 2 (split; first done).
    split; first by rewrite -Hpermold.
    split; first by rewrite -Hpermold.
    intros it' t' Hluit'.
    assert (wf_tree trnew) as Hwfnew.
    { destruct (decide (l.1 = blk)) as [<-|Hne].
      - rewrite /apply_within_trees Htrold /= in Happly.
        eapply bind_Some in Happly as (? & H1 & [= H2]).
        rewrite -H2 lookup_insert in Htrnew.
        injection Htrnew as ->. eapply memory_access_wf; last done.
        destruct Hwf as [_ Hwf _ _]. by eapply Hwf.
      - eapply bind_Some in Happly as (? & H1 & (? & H2 & [= H3])%bind_Some).
        rewrite -H3 lookup_insert_ne // in Htrnew.
        destruct Hwf as [_ Hwf _ _]. by eapply Hwf.
    }
    assert (tree_unique t' trnew) as Hunq.
    { eapply wf_tree_tree_unique. 2: apply Hluit'. done. }
    assert (tree_unique t' trold) as Hunqold.
    { destruct (decide (l.1 = blk)) as [<-|Hne].
      - rewrite /apply_within_trees Htrold /= in Happly.
        eapply bind_Some in Happly as (? & H1 & [= H2]).
        rewrite -H2 lookup_insert in Htrnew.
        injection Htrnew as ->. rewrite /tree_unique.
        by erewrite tree_apply_access_same_count.
      - eapply bind_Some in Happly as (? & H1 & (? & H2 & [= H3])%bind_Some).
        rewrite -H3 lookup_insert_ne // Htrold in Htrnew. congruence.
    }
    eapply unique_exists in Hunqold as Hextold.
    eapply unique_lookup in Hunqold as (it & Hitdet).
    eapply Hothers. done.
Qed.

(* not generalized to maybe_nonchildren_only since this one is specific *)
Lemma loc_controlled_write_becomes_active l sc cids σ σ' blk off1 sz tg vls scold tkkold Mcall:
  apply_within_trees (memory_access AccessWrite cids tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  (write_mem (blk, off1) vls (shp σ)) = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  length vls = sz →
  trees_contain tg (strs σ) blk →
  list_to_heaplet vls off1 !! l.2 = Some sc →
  loc_controlled Mcall l tg (tk_unq tkkold) scold σ →
  (* we also prove that it's usable *)
  loc_controlled Mcall l tg (tk_unq tk_act) sc σ' ∧ bor_state_pre l tg (tk_unq tk_act) σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Hcontain Hsc Hold.
  assert (shp σ' !! l = Some sc) as Hheap.
  { rewrite -Heq_shp /=.
    destruct (write_mem_lookup_case (blk, off1) vls (shp σ) l) as [(i&Hil&->&HH)|(Hwrong&_)].
    2: { eapply list_to_heaplet_lookup_Some in Hsc. exfalso.
         eapply (Hwrong (Z.to_nat (l.2 - off1))); first lia.
         eapply injective_projections; first done.
         simpl. lia. }
    rewrite HH. rewrite list_to_heaplet_nth // in Hsc. }
  assert (wf_trees σ.(strs)) as Hwf_pre by eapply Hwf.
  assert (wf_trees σ'.(strs)) as Hwf_post.
  { eapply apply_within_trees_wf; try done.
    eapply memory_access_tag_count. }
  pose proof Happly as Happlys.
  eapply bind_Some in Happly as (trold & Htrold & (trnew&Haccess&[= Hstrs])%bind_Some).
  rewrite /trees_contain /trees_at_block Htrold in Hcontain.
  eapply wf_tree_tree_unique in Hcontain as Hunique; last by eapply Hwf_pre.
  eapply unique_lookup in Hunique as (itold & Hdet).
  assert (tree_lookup trold tg itold) as Hitold by done.
  assert (off1 ≤ l.2 < off1 + sz) as Hinbound.
  { subst sz. by eapply list_to_heaplet_lookup_Some. }
  eapply apply_trees_access_lookup_general in Happlys as Happlyself.
  2: done. 3: by exists trold. 2: eassumption.
  destruct Happlyself as (itnew & Hlunew & _ & _ & Happlyself).
  assert (perm (item_lookup itnew l.2) = Active ∧ initialized (item_lookup itnew l.2) = PermInit ∧ bor_state_pre l tg (tk_unq tkkold) σ) as (Hactive&Hisinit&Hpre2).
  { eapply bind_Some in Happlyself as (prm&Hperm1&(pv&Hperm2&[= <-])%bind_Some).
    simpl in Hperm1,Hperm2|-*. rewrite trees_rel_dec_refl /= in Hperm1|-*.
    rewrite most_init_comm.
    pose (ppo := item_lookup itold l.2). fold ppo.
    enough (pv = Active ∧ (initialized ppo = PermInit → perm (ppo) ≠ Disabled) ∧ (initialized ppo = PermInit → perm ppo = Frozen → protector_is_active (iprot itold) (scs σ))) as (H1&H2).
    { split; first done. simpl. rewrite /bor_state_pre_unq. split; first done.
      eexists. split; last apply H2.
      eexists; by subst blk. } subst ppo.
    repeat case_match; simplify_eq; done. }
  split; last first.
  { exists itnew. split; first by rewrite Hblk. by rewrite Hactive. }
  intros _. split; last done.
  rewrite -Hstrs /trees_lookup lookup_insert in Hlunew.
  destruct Hlunew as (?&[= <-]&Hlunew).
  exists itnew, trnew.
  split; first done.
  split; first rewrite -Hstrs Hblk lookup_insert //.
  split; first done.
  split; first by rewrite Hactive.
  destruct (Hold Hpre2) as ((it'&tr'&Htr'&Hlu'&_&_&Holdothers)&_).
  assert (tr' = trold) as ->.
  { rewrite Hblk Htrold in Hlu'. congruence. }
  intros itmod tmod Hlumod.
  eapply apply_trees_access_lookup_general_rev in Happlys.
  2: done. 2: eassumption. 2: { exists trnew; split; last done. rewrite -Hstrs lookup_insert //. }
  destruct Happlys as (itold' & (tr'&Htr''&Hluold) & _ & _ & Hperm).
  assert (tr' = trold) as ->.
  { rewrite Htrold in Htr''. congruence. }
  specialize (Holdothers _ _ Hluold).
  rewrite /trees_rel_dec Htrold /= /apply_access_perm /= /apply_access_perm_inner in Hperm.
  erewrite <-access_same_rel_dec; last done. clear Happlyself.
  rewrite rel_dec_flip2 in Holdothers|-*.
  eapply bind_Some in Hperm as (prm&Hperm1&(pv&Hperm2&[= <-])%bind_Some).
  rewrite /= in Hperm1,Hperm2|-*.
  destruct rel_dec as [[[]|]|[|]], (perm (item_lookup itold' l.2)) as [[] []| | |], (initialized (item_lookup itold' l.2)) as [];
    repeat (simpl; try simpl in Hperm1; try simpl in Holdothers; simplify_eq; try done; try simpl in Hperm2; destruct bool_decide).
Qed.

Lemma loc_controlled_write_invalidates_others l sc σ σ' blk off1 sz tg_acc tg_lu vls tk Mcall A:
  apply_within_trees (memory_access AccessWrite σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  (write_mem (blk, off1) vls (shp σ)) = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  tg_acc ≠ tg_lu →
  trees_contain tg_acc σ.(strs) blk →
  loc_controlled Mcall l tg_lu tk sc σ →
  bor_state_pre l tg_lu tk σ' →
  A. (* false *)
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Htgne Htgin Hcontrol Hpre.
  subst blk. exfalso.
  pose proof Happly as (trold&Htrold&(trnew&Haccess&[= Hstrs])%bind_Some)%bind_Some.
  assert (strs σ' !! l.1 = Some trnew) as Htrnew.
  { by rewrite -Hstrs lookup_insert. }
  destruct tk as [|tkk|].
  - destruct Hpre as (itnew&(trnew'&Htrnew'&Hitnew)&Hnondis).
    assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
    eapply apply_trees_access_lookup_general_rev in Happly as Hitrev.
    2: apply Hwf. 2: eassumption. 2: exists trnew; split; first done; last exact Hitnew.
    destruct Hitrev as (itold & (trold' & Htrold' & Hitold) & Hinitit & Hprotit & Hpermit).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    destruct Hcontrol as (Hcontrol&_).
    { exists itold. split; first by eexists.
      intros Hdis. eapply Hnondis.
      pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
      rewrite -Hx3. rewrite !Hdis in Hx1. simpl.
      assert (x1 = x2) as ->. 1: destruct (initialized _), bool_decide; simplify_eq; try done; destruct x1; by simplify_eq.
      clear Hx2.
      rewrite /apply_access_perm_inner in Hx1. destruct trees_rel_dec; by simplify_eq. }
    destruct Hcontrol as (itold' & trold' & Hitold' & Htrold' & Hisinit & Hfrozen & Hothers).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    assert (itold' = itold) as -> by by eapply tree_lookup_unique. clear Hitold'.
    (* old perm is frozen, it can not have survived the write *)
    pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
    rewrite Hfrozen /= in Hx1. destruct (trees_rel_dec (strs σ) l.1 tg_acc tg_lu); try done.
    pose proof Hx1 as [= <-].
    assert (x2 = Disabled) as -> by (destruct (initialized _), bool_decide; simplify_eq; done).
    rewrite -Hx3 in Hnondis. done.
  - destruct Hpre as (itnew&(trnew'&Htrnew'&Hitnew)&Hnondis & Hfreezeprot). 
    assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
    eapply apply_trees_access_lookup_general_rev in Happly as Hitrev.
    2: apply Hwf. 2: eassumption. 2: exists trnew; split; first done; last exact Hitnew.
    destruct Hitrev as (itold & (trold' & Htrold' & Hitold) & Hinitit & Hprotit & Hpermit).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    destruct Hcontrol as (Hcontrol&_).
    { exists itold. split; first by eexists.
      pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
      rewrite /apply_access_perm_inner in Hx1.
      rewrite -Hx3 /most_init /= in Hnondis Hfreezeprot.
      rewrite bool_decide_decide in Hx1,Hx2.
      destruct trees_rel_dec as [[]|[]], (perm (item_lookup itold l.2)), (initialized (item_lookup itold l.2)) as []; simplify_eq; try done.
      all: try specialize (Hnondis eq_refl).
      all: (try destruct decide); try by simplify_eq. }
    destruct Hcontrol as (itold' & trold' & Hitold' & Htrold' & Hisinit & Hsame & Hothers).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    assert (itold' = itold) as -> by by eapply tree_lookup_unique. clear Hitold'.
    rewrite /trees_contain /trees_at_block Htrold in Htgin.
    pose proof Htgin as Hunq%wf_tree_tree_unique.
    2: by eapply (state_wf_tree_unq _ Hwf).
    pose proof Hunq as (itaccold&Hdet)%unique_lookup.
    assert (tree_lookup trold tg_acc itaccold) as Hitaccold by done.
    destruct (rel_dec trold tg_acc tg_lu) as [foreignpos|[isimm|]] eqn:Hreldec.
    + eapply apply_trees_access_lookup_general in Happly as Hitrev.
      2: apply Hwf. 2: eassumption. 2: exists trold; split; first done; last exact Hitaccold.
      destruct Hitrev as (itaccnew & (trnew' & Htrnew' & Hitaccnew) & Hinititacc & Hprotitacc & Hpermitacc).
      assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
      rewrite trees_rel_dec_refl in Hpermitacc.
      specialize (Hothers _ _ Hitaccold).
      pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some. clear Hpermit.
      pose proof Hpermitacc as (y1&Hy1&(y2&Hy2&[=Hy3])%bind_Some)%bind_Some. clear Hpermitacc.
      rewrite /apply_access_perm_inner in Hx1,Hy1.
      rewrite -!Hx3 -!Hprotit -?Heq_scs /= in Hnondis Hfreezeprot Hx1 Hx2.
      rewrite /trees_rel_dec Htrold in Hx1.
      rewrite !bool_decide_decide in Hx1,Hx2,Hy1,Hy2.
      rewrite Hreldec in Hx1,Hothers.
      destruct foreignpos as [pp|].
      all: destruct (perm (item_lookup itold l.2)) as [[][]| | |], 
                    (initialized (item_lookup itold l.2)) as []; 
             simpl in *; simplify_eq; try done.
      all: repeat (destruct decide; simplify_eq; try done).
      all: destruct (perm (item_lookup itaccold l.2)) as [[][]| | |], 
                    (initialized (item_lookup itaccold l.2)) as []; 
             simpl in *; simplify_eq; try specialize (Hnondis eq_refl); try destruct Hsame as (?&?&?); try done.
    + pose proof Hreldec as HH.
      rewrite /rel_dec in HH.
      edestruct (decide (ParentChildIn _ _ _)) as [HPC|]; last done.
      edestruct (decide (ParentChildIn _ _ _)) as [|HNPC]; first done.
      injection HH as Hisimm.
      eapply lookup_implies_contains in Hitold as Hluin.
      assert (StrictParentChildIn tg_lu tg_acc trold) as HSPC.
      { destruct HPC; last done. subst tg_lu. rewrite rel_dec_refl in Hreldec; done. }
      eapply immediate_sandwich in HSPC as (tsw&H1&H2).
      2-3: by eapply Hwf.
      eapply contains_child in Hluin as Htwin.
      2: right; by eapply Immediate_is_StrictParentChild.
      destruct (@unique_implies_lookup tsw trold) as (itsw&Hitswold).
      1: by eapply Hwf.
      eapply apply_trees_access_lookup_general in Happly as Hitrev.
      2: apply Hwf. 2: eassumption. 2: exists trold; split; first done; last exact Hitswold.
      destruct Hitrev as (itswnew & (trnew' & Htrnew' & Hitswnew) & Hinititsw & Hprotitsw & Hpermitsw).
      assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
      specialize (Hothers _ _ Hitswold).
      rewrite /trees_rel_dec Htrold in Hpermitsw.
      rewrite /rel_dec decide_True // /maybe_non_children_only /= in Hpermitsw.
      rewrite /rel_dec decide_True // /= in Hothers.
      2: right; by eapply Immediate_is_StrictParentChild.
      rewrite /rel_dec decide_False // /= in Hothers.
      2: { intros HH. eapply immediate_parent_not_child. 4: exact HH. 3: done.
           all: eapply Hwf; first done. all: done. }
      rewrite decide_True // /= in Hothers.
      pose proof Hpermitsw as (y1&Hy1&(y2&Hy2&[=Hy3])%bind_Some)%bind_Some. clear Hpermitsw.
      rewrite /apply_access_perm Hothers /= in Hy1. done.
    + eapply Htgne, rel_this_antisym. 3: done. 2: apply Hitold. done.
  - destruct Hcontrol as ((itold&trold'&Hitold&Htrold'&Hactive&Hunq)&_); first done.
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    rewrite /trees_contain /trees_at_block Htrold in Htgin.
    pose proof Htgin as Htgunq%wf_tree_tree_unique.
    2: by eapply (state_wf_tree_unq _ Hwf).
    pose proof Htgunq as (itaccold&Hdet)%unique_lookup.
    assert (tree_lookup trold tg_acc itaccold) as Hitaccold by done.
    eapply Htgne; symmetry. eapply Hunq; try done.
Qed.


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

Lemma loc_controlled_read_preserved l sc σ σ' blk off1 sz tg_acc tg_lu tk Mcall b:
  apply_within_trees (memory_access_maybe_nonchildren_only b AccessRead σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  trees_contain tg_acc σ.(strs) blk →
  loc_controlled Mcall l tg_lu tk sc σ →
  loc_controlled Mcall l tg_lu tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Htgin Hlc.
  subst blk.
  pose proof Happly as (trold&Htrold&(trnew&Haccess&[= Hstrs])%bind_Some)%bind_Some.
  assert (strs σ' !! l.1 = Some trnew) as Htrnew.
  { by rewrite -Hstrs lookup_insert. }
  rewrite /loc_controlled.
  destruct tk as [|act|] eqn:Heq; simpl.
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_general_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done.
      intros Hdis. eapply apply_access_perm_read_not_disabled in Hdis; done.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold2 & Htrold2 & Hluold).
      assert (trold2 = trold) as -> by congruence. clear Htrold2.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew2 & Htrnew2 & Hlunew).
      assert (trnew2 = trnew) as -> by congruence.
      exists it, trnew. do 2 (split; first done).
      split; first by eapply apply_access_perm_read_initialized.
      split; first by eapply apply_access_perm_read_frozen.
      intros itnew' t' Hit'.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_general_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      specialize (Hothers _ _ Hitoldlu').
      assert (rel_dec trnew t' tg_lu = rel_dec trold t' tg_lu) as Hreldec.
      { rewrite /apply_within_trees Hx /= in Happly.
        apply bind_Some in Happly as (newtr & H1 & [= H2]).
        rewrite -H2 lookup_insert in Htrnew.
        erewrite (access_same_rel_dec H1). congruence. }
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2).
      rewrite /trees_rel_dec Htrold in Hperm2.
      edestruct maybe_non_children_only_effect_or_nop as [Heqc|Heqc]; erewrite Heqc in Hperm2.
      2: by injection Hperm2 as <-.
      assert (lazy_perm_wf (item_lookup itold' l.2)) as Hwitold'.
      { eapply item_wf_lookup. pose (state_wf_tree_compat _ Hwf) as Hcompat.
        specialize (Hcompat _ _ Htrold). rewrite /tree_items_compat_nexts every_node_iff_every_lookup in Hcompat.
        1: by eapply Hcompat. eapply wf_tree_tree_item_determined. by eapply Hwf. }
      rewrite /lazy_perm_wf in Hwitold'.
      clear Heqc. rewrite /apply_access_perm /apply_access_perm_inner /= in Hperm2.
      repeat (case_match; simpl in Hperm2; simplify_eq; try rewrite <- Hperm2; try (specialize (Hwitold' eq_refl)); try done).
  - intros (it & Htrlu & Hndis & Hfrzprot).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_general_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done. split.
      1: intros HH Hdis; eapply apply_access_perm_read_not_disabled in Hdis; last done.
      1: eapply Hndis; try done; by eapply apply_access_perm_read_initialized.
      intros Hinit Hfrz. rewrite Heq2 Heq_scs. eapply Hfrzprot.
      1: erewrite apply_access_perm_read_initialized; done.
      1: erewrite apply_access_perm_read_frozen; done.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold2 & Htrold2 & Hluold).
      assert (trold2 = trold) as -> by congruence. clear Htrold2. rewrite /bor_state_own /= in Hownold.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hstuff).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew2 & Htrnew2 & Hlunew).
      assert (trnew2 = trnew) as -> by congruence.
      exists it, trnew. do 2 (split; first done).
      destruct Hstuff as (Hisinit & Hsame & Hothers).
      assert (lazy_perm_wf (item_lookup itold l.2)) as Hwfitold.
      { eapply item_wf_lookup. pose (state_wf_tree_compat _ Hwf) as Hcompat.
        specialize (Hcompat _ _ Htrold). rewrite /tree_items_compat_nexts every_node_iff_every_lookup in Hcompat.
        1: by eapply Hcompat. eapply wf_tree_tree_item_determined. by eapply Hwf. }
      rewrite /lazy_perm_wf in Hwfitold. rewrite /bor_state_post_unq.
      split; first by eapply apply_access_perm_read_initialized.
      match goal with |- (?A ∧ ?B) => assert (A ∧ match trees_rel_dec (strs σ) l.1 tg_acc tg_lu with 
          Foreign (Parent _) => act = tk_res ∨ (b = true) | Foreign _ => act = tk_res | _ => True end) as (Hfp&Hactres) end.
      { clear Hothers. rewrite -Heq2 -Heq_scs. edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqcc&Hne)|(Heqcc&He1&childkind&He2)]; erewrite Heqcc in Heq3.
        2: { injection Heq3 as <-. rewrite He2. split; first done. by right. }
        pose proof Heq3 as (x1&Hx1&(x2&Hx2&[= HH])%bind_Some)%bind_Some.
        rewrite -HH -?Heq_scs /= in Hfrzprot|-*.
        rewrite /apply_access_perm_inner in Hx1.
        repeat (case_match; simplify_eq; (try specialize (Hwfitold eq_refl)); (try (destruct Hsame; [ idtac ])); try done; try (split; [done | (try by left); by right ])).
        all: exfalso.
        all: eapply bool_decide_eq_false_1; last apply (Hfrzprot eq_refl eq_refl). all: done. }
      split; first done.
      intros itnew' t' Hit'.
      rewrite /lazy_perm_wf in Hwfitold.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_general_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      assert (lazy_perm_wf (item_lookup itold' l.2)) as Hwfitold'.
      { eapply item_wf_lookup. pose (state_wf_tree_compat _ Hwf) as Hcompat.
        specialize (Hcompat _ _ Htrold). rewrite /tree_items_compat_nexts every_node_iff_every_lookup in Hcompat.
        1: by eapply Hcompat. eapply wf_tree_tree_item_determined. by eapply Hwf. }
      rewrite /lazy_perm_wf in Hwfitold'.
      specialize (Hothers _ _ Hitoldlu').
      assert (∀ tg1 tg2, rel_dec trnew tg1 tg2 = rel_dec trold tg1 tg2) as Hreldec_strong.
      { intros tg1 tg2. rewrite /apply_within_trees Hx /= in Happly.
        apply bind_Some in Happly as (newtr & H1 & [= H2]).
        rewrite -H2 lookup_insert in Htrnew.
        erewrite (access_same_rel_dec H1). congruence. }
      assert (rel_dec trnew t' tg_lu = rel_dec trold t' tg_lu) as Hreldec.
      { eapply Hreldec_strong. }
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2).
      edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqcc&Hne)|(Heqcc&He1&childkind&He2)]; erewrite Heqcc in Hperm2.
      2: injection Hperm2 as <-; apply Hothers.
      pose proof Hperm2 as (x1&Hx1&(x2&Hx2&[= HH])%bind_Some)%bind_Some.
      rewrite -HH -?Heq_scs /= in |-*.
      rewrite /apply_access_perm_inner in Hx1. clear Heqcc. clear Hfp.
      rewrite /trees_rel_dec Htrold in Hactres HH Hx1 Hne.
      rewrite /trees_contain /trees_at_block Htrold in Htgin.
      assert (wf_tree trold) as Hwfold by by eapply Hwf.
      opose proof (rel_dec_concat_foreign _ tg_acc t' tg_lu _ _ _ _) as HtransiF.
      1-4: try done; eapply wf_tree_tree_unique; try done; by eapply lookup_implies_contains.
      repeat (case_match; simplify_eq; (try specialize (Hwfitold' eq_refl)); 
          (try edestruct (HtransiF _ _ eq_refl eq_refl) as (?&?)); simplify_eq; try done).
      all: destruct Hactres as [?|Hactres]; first done.
      all: subst b; destruct Hne as [?|Hne]; first done.
      all: erewrite Hreldec_strong in Hreldec;
           edestruct rel_dec_parent_parent_is_parent as (p&Hp); [exact Hwfold| | | | |exact Hreldec|..]; [| | | |done|]; [done|eapply Hitoldlu'|eapply Hluold|..]; [done|]; subst; exfalso; by eapply Hne.
  - destruct Hlc as (Hownold & Hscold); first done.
    split; last by rewrite -Heq_shp.
    destruct Hownold as (itold & trold' & Hluold & Htrold' & Hisinit & Hsame & Hothers).
    assert (trold' = trold) as -> by congruence.
    assert (trees_lookup σ.(strs) l.1 tg_lu itold) as Hsluold by by exists trold.
    eapply apply_trees_access_lookup_general in Hsluold; [|eapply Happly|eapply Hwf|done].
    destruct Hsluold as (itnew & (trnew' & Htrnew' & Hlunew) & (Hinitold & Hprotold & Hpermold)).
    assert (trnew' = trnew) as -> by congruence.
    assert (tg_lu = tg_acc) as <-.
    { eapply trees_contain_trees_lookup_1 in Htgin as (it&tr&Htr&HH). 2: apply Hwf.
      assert (tr = trold) as -> by congruence. by eapply Hothers. }
    exists itnew, trnew. do 2 (split; first done). split.
    { by eapply apply_access_perm_read_initialized. }
    rewrite trees_rel_dec_refl in Hpermold.
    edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqcc&Hne)|(Heqcc&He1&acckind&He2)]; erewrite Heqcc in Hpermold.
    2: done.
    rewrite /apply_access_perm Hsame /= in Hpermold.
    split.
    { repeat (case_match; simpl in *; simplify_eq; try done). all: by rewrite -Hpermold. }
    intros it' t' Hluit'.
    assert (wf_tree trnew) as Hwfnew.
    { rewrite /apply_within_trees Htrold /= in Happly.
      eapply bind_Some in Happly as (? & H1 & [= H2]).
      rewrite -H2 lookup_insert in Htrnew.
      injection Htrnew as ->. eapply memory_access_wf; last done.
      destruct Hwf as [_ Hwf _ _]. by eapply Hwf.
    }
    assert (tree_unique t' trnew) as Hunq.
    { eapply wf_tree_tree_unique. 2: apply Hluit'. done. }
    assert (tree_unique t' trold) as Hunqold.
    { rewrite /apply_within_trees Htrold /= in Happly.
      eapply bind_Some in Happly as (? & H1 & [= H2]).
      rewrite -H2 lookup_insert in Htrnew.
      injection Htrnew as ->. rewrite /tree_unique.
      by erewrite tree_apply_access_same_count.
    }
    eapply unique_exists in Hunqold as Hextold.
    eapply unique_lookup in Hunqold as (it & Hitdet).
    eapply Hothers. done.
Qed.

Lemma loc_controlled_read_preserved_everywhere l sc σ σ' blk off1 sz tg_acc tg_lu tk Mcall b:
  apply_within_trees (memory_access_maybe_nonchildren_only b AccessRead σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  trees_contain tg_acc σ.(strs) blk →
  loc_controlled Mcall l tg_lu tk sc σ →
  loc_controlled Mcall l tg_lu tk sc σ'.
Proof.
  intros Happly Hhp Hcs Hwf Hcont.
  destruct (decide ((l.1 = blk ∧ off1 ≤ l.2 < off1 + sz))) as [(Hblk&Hoff)|Hne].
  - by eapply loc_controlled_read_preserved.
  - eapply loc_controlled_access_outside; try done. by rewrite Hhp.
Qed.

Lemma protected_priv_loc_does_not_survive_access σ σ' M_tag M_hl M_call off1 sz blk tg_acc tg_lu l acc Mcall :
  apply_within_trees (memory_access acc σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  trees_contain tg_acc σ.(strs) blk →
  call_set_interp M_call σ →
  M_tag !! tg_acc = Some (tk_pub, ()) →
  priv_loc M_tag M_hl M_call tg_lu l →
  (∀ tg tk sc, M_tag !! tg = Some (tk, ()) → heaplet_lookup M_hl (tg, l) = Some sc → loc_controlled Mcall l tg tk sc σ) →
  False.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Htgin Hcs Hactually_public Hpl Hlc.
  destruct Hpl as (tk&Htk&(sc&Hsc)&Hpriv).
  eapply trees_contain_trees_lookup_1 in Htgin as (itacc&(tr&Htr&Hitacc)); last apply Hwf.
  specialize (Hlc tg_lu tk sc Htk Hsc).
  destruct Hpriv as [->|(cc&->&Hcc)].
  - destruct Hlc as ((it&tr'&Hit&Htr'&Hactive&Hunq)&_); first done.
    assert (tr' = tr) as -> by congruence.
    enough (tg_lu = tg_acc) as -> by congruence.
    eapply Hunq. done.
  - destruct Hcc as (Mcc&HMcc&Lcc&HLcc&Hlincc).
    specialize (Hcs _ _ HMcc) as (Hccact&Hcs).
    specialize (Hcs _ _ HLcc) as (Htgluvalid&Hcs).
    specialize (Hcs l Hlincc) as (itlu&(tr'&Htr'&Hitlu)&Hprot1&Hprot2&Hcs).
    assert (tr' = tr) as -> by congruence.
    destruct Hlc as (Hlc&_).
    { eexists. split; first by eexists. split; first done.
      intros _ _. by eexists. }
    destruct Hlc as (itlu'&tr'&Hitlu'&Htr''&Hisinit&Hsame&Hothers).
    assert (tr' = tr) as -> by congruence.
    assert (itlu' = itlu) as -> by by eapply tree_lookup_unique.
    subst blk.
    assert (perm (item_lookup itlu l.2) = Active) as Hisactive.
    { destruct perm as [[][]| | |]; try done; by destruct Hsame. }
    destruct (rel_dec tr tg_acc tg_lu) as [fk|[ck|]] eqn:Hreldec.
    + assert (trees_lookup σ.(strs) l.1 tg_lu itlu) as Hitluold by by eexists.
      pose Hitluold as HH.
      eapply (apply_trees_access_lookup_general false) in HH; [|eapply Happly|eapply Hwf|done].
      destruct HH as (itlunew&(trnew&Htrnew&Hitlunew)&Hinitplu&Hiprotlu&Hpermlu).
      rewrite /trees_rel_dec Htr in Hpermlu.
      assert (protector_is_active (iprot itlunew) (scs σ)) as Hisprot.
      { exists cc. rewrite -Hiprotlu //. }
      rewrite Hreldec /= /apply_access_perm /apply_access_perm_inner Hisactive /= in Hpermlu.
      rewrite bool_decide_eq_true_2 // Hisinit /= in Hpermlu.
      by destruct acc.
    + assert (StrictParentChildIn tg_lu tg_acc tr) as HSPC.
      { rewrite /rel_dec in Hreldec. destruct decide as [[->|HSPC]|?]; try done.
        rewrite decide_True in Hreldec; last by left. done. }
      assert (tree_contains tg_lu tr) as Hluin.
      1: by eapply lookup_implies_contains.
      eapply immediate_sandwich in HSPC as (tsw&Hs1&Hs2).
      2-3: by eapply Hwf.
      eapply contains_child in Hluin as Hswin.
      2: right; by eapply Immediate_is_StrictParentChild.
      assert (tree_unique tsw tr) as Hswinunq by by eapply Hwf.
      eapply unique_implies_lookup in Hswinunq as (itsw&Hitsw).
      assert (trees_lookup σ.(strs) l.1 tsw itsw) as Hitswold by by eexists.
      pose Hitswold as HH.
      eapply (apply_trees_access_lookup_general false) in HH; [|eapply Happly|eapply Hwf|done].
      destruct HH as (itswnew&(trnew&Htrnew&Hitswnew)&Hinitpsw&Hiprotsw&Hpermsw).
      specialize (Hothers _ _ Hitsw).
      rewrite /trees_rel_dec Htr // in Hpermsw.
      rewrite /= /rel_dec decide_True // in Hpermsw.
      rewrite /= /rel_dec decide_True in Hothers.
      2: right; by eapply Immediate_is_StrictParentChild.
      rewrite decide_False in Hothers.
      2: { intros HPC2. eapply immediate_parent_not_child; try done. all: by eapply Hwf. }
      rewrite decide_True // in Hothers.
      rewrite /= /apply_access_perm /apply_access_perm_inner /= !Hothers /= in Hpermsw.
      by destruct acc.
    + enough (tg_lu = tg_acc) as -> by congruence.
      symmetry.
      eapply rel_this_antisym; last done.
      all: by eapply lookup_implies_contains.
Qed.


(* not generalized to maybe_nonchildren_only since this one is specific *)
Lemma loc_controlled_write_invalidates_pub l cids σ σ' blk off1 sz tg scold Mcall (A:Prop):
  apply_within_trees (memory_access AccessWrite cids tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  state_wf σ →
  l.1 = blk →
  trees_contain tg (strs σ) blk →
  (off1 ≤ l.2 < off1 + sz) →
  loc_controlled Mcall l tg tk_pub scold σ →
  A.
Proof.
  intros Happly Hwf Hblk Hcontain Hinbound Hold.
  assert (wf_trees σ.(strs)) as Hwf_pre by eapply Hwf.
  assert (wf_trees σ'.(strs)) as Hwf_post.
  { eapply apply_within_trees_wf; try done.
    eapply memory_access_tag_count. }
  pose proof Happly as Happlys.
  eapply bind_Some in Happly as (trold & Htrold & (trnew&Haccess&[= Hstrs])%bind_Some).
  rewrite /trees_contain /trees_at_block Htrold in Hcontain.
  assert (strs σ' !! blk = Some trnew) as Htrnew.
  1: rewrite -Hstrs lookup_insert //.
  eapply wf_tree_tree_unique in Hcontain as Hunique; last by eapply Hwf_pre.
  eapply unique_lookup in Hunique as (itold & Hdet).
  assert (tree_lookup trold tg itold) as Hitold by done.
  eapply apply_trees_access_lookup_general in Happlys as Happlyself.
  2: done. 3: by exists trold. 2: eassumption.
  destruct Happlyself as (itnew & Hlunew & _ & _ & Happlyself).
  rewrite trees_rel_dec_refl /= /apply_access_perm /apply_access_perm_inner /= in Happlyself.
  destruct Hold as ((itold'&trold'&Htrold'&Hitold'&Hisinit&Hfrozen&Hothers)&_).
  { exists itold. subst blk. split; first by eexists.
    intros Hdis. rewrite Hdis in Happlyself. done. } 
  assert (trold' = trold) as -> by congruence.
  assert (itold' = itold) as -> by by eapply tree_lookup_unique.
  rewrite Hfrozen in Happlyself. done.
Qed.

Lemma loc_controlled_write_invalidates_pub' l cids σ σ' blk off1 sz tg scold Mcall :
  apply_within_trees (memory_access AccessWrite cids tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  state_wf σ →
  l.1 = blk →
  trees_contain tg (strs σ) blk →
  (off1 ≤ l.2 < off1 + sz) →
  loc_controlled Mcall l tg tk_pub scold σ →
  loc_controlled Mcall l tg tk_pub scold σ'.
Proof.
  eapply loc_controlled_write_invalidates_pub.
Qed.

Lemma loc_controlled_add_protected l tg tk sc σ σ' Mcall :
  shp σ = shp σ' →
  strs σ = strs σ' →
  state_wf σ →
  (∀ blk tg it c, trees_lookup σ.(strs) blk tg it → protector_is_for_call c it.(iprot) → call_is_active c σ.(scs) ↔ call_is_active c σ'.(scs)) →
  loc_controlled Mcall l tg tk sc σ →
  loc_controlled (<[snc σ := ∅]> Mcall) l tg tk sc σ'.
Proof.
  intros Hhp Htrs Hwf Hscs Hlc Hpre.
  assert (∀ blk tg it, trees_lookup σ.(strs) blk tg it → protector_is_active it.(iprot) σ.(scs) ↔ protector_is_active it.(iprot) σ'.(scs)) as HHscs.
  { intros blk tg' it H1; split; intros (c&H2&H3); exists c. all: split; first done. all: by eapply Hscs. }
  rewrite -Hhp.
  destruct tk as [|acc|].
  all: rewrite /loc_controlled /bor_state_pre /bor_state_own in Hlc,Hpre|-*.
  1,3: rewrite Htrs in Hlc; apply Hlc, Hpre.
  destruct Hlc as ((it&tr&Htr&Hit&Hinit&Hsame&Hothers)&Hhpc).
  - destruct Hpre as (itp&Hitp&HH).
    setoid_rewrite <- HHscs in HH. 2: by rewrite Htrs.
    exists itp. by rewrite Htrs.
  - split; last done.
    exists it, tr. rewrite -Htrs. split_and!; try done.
    split. 2: done.
    clear Hothers.
    case_match; try done.
    case_match; try done. destruct Hsame as (->&Hprot&Hcs).
    split_and!; first done.
    + setoid_rewrite <- HHscs; first done.
      by eexists.
    + destruct (iprot it) as [itprot|] eqn:Hitprot; last done.
      rewrite /prot_in_call_set /= /call_set_in' lookup_insert_ne //.
      specialize (state_wf_tree_compat _ Hwf _ _ Hit) as Hwfcompat.
      setoid_rewrite every_node_iff_every_lookup in Hwfcompat.
      2: by eapply wf_tree_tree_item_determined, Hwf.
      specialize (Hwfcompat _ _ Htr).
      opose proof (item_cid_valid _ _ _ Hwfcompat (itprot.(call)) _) as ?. 2: lia.
      rewrite Hitprot. by destruct itprot.
Qed.



Definition is_pseudo_conflicted_by_in' C (tr : tree item) (tg tg_cous : tag) (it : item) (L : gset Z) acc : Prop := 
  tree_lookup tr tg it ∧
  protector_is_active it.(iprot) C ∧
  rel_dec tr tg tg_cous = Foreign Cousin ∧
  ∃ it_cous l im,
    l ∈ L ∧
    tree_lookup tr tg_cous it_cous ∧
    (item_lookup it l).(perm) = Reserved im acc.

Definition is_pseudo_conflicted_by_in (C : call_id_set) (tr : tree item) (tg : tag) (it : item) (S : gset (tag * gset Z)) acc : Prop := 
  ∃ tg_cous L,
    (tg_cous, L) ∈ S ∧
    is_pseudo_conflicted_by_in' C tr tg tg_cous it L acc.

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

Lemma tree_read_many_pseudo_helper_2_pers C tg_acc (L : list Z) tr1 trL S
  (Hwf1 : wf_tree tr1) :
  tree_unique tg_acc tr1 →
  let fn := (λ L tr, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C tr1 tg' it S acc → acc = ResConflicted) →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C trL tg' it S acc → acc = ResConflicted).
Proof.
  intros Hunq fn Hih H. revert Hih.
  induction L as [|off L IH] in trL|-*.
  1: by intros [= ->]. simpl.
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tg' it acc (tg_cs&SL&HS&Hlu&Hisprot&Hreldec&it_cous&l&im&HlL&Hlucs&Hres).
  assert (tree_unique tg_acc tr2) as Hunq2.
  { rewrite /tree_unique. erewrite <- tree_read_many_helper_2. 1: exact Hunq. exact Hoff. }
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  destruct (decide (l = off)) as [->|Hne].
  - odestruct tree_access_lookup_general_rev as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: split; first reflexivity; lia.
    odestruct tree_access_lookup_general_rev as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: split; first reflexivity; lia.
    eapply apply_access_perm_read_reserved_backwards in H4 as HHres.
    2: done. destruct HHres as (acto & Hacto).
    enough (acto = ResConflicted).
    { subst acto. eapply apply_access_perm_read_conflicted in H4 as HHres. 2: done. rewrite Hres in HHres. congruence. }
    eapply IH.
    eexists tg_cs, SL. split; first done.
    split; first eapply H1.
    split; first by rewrite H3. split.
    { erewrite access_same_rel_dec; first done. apply HL. }
    exists itcs', off, im. do 2 (split; first done). done.
  - odestruct (tree_access_lookup_outside_rev l) as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: lia.
    odestruct (tree_access_lookup_outside_rev l) as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: lia.
    rewrite -H4 in Hres. eapply IH.
    eexists tg_cs, SL. split; first done.
    split; first eapply H1.
    split; first by rewrite H3. split.
    { erewrite access_same_rel_dec; first done. apply HL. }
    exists itcs', l, im. do 2 (split; first done). done.
Qed.


Lemma tree_read_many_pseudo_helper_2_news C tg_acc (L : list Z) tr1 trL
  (Hwf1 : wf_tree tr1) :
  tree_unique tg_acc tr1 →
  let fn := (λ L tr, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_conflicted_by_in' C trL tg' tg_acc it (list_to_set L) acc → acc = ResConflicted).
Proof.
  intros Hunq fn.
  induction L as [|off L IH] in trL|-*.
  { simpl. intros [= ->] tg it acc (?&?&?&?&?&?&HH&_). set_solver. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tg' it acc (Hlu&Hisprot&Hreldec&it_cous&l&im&HlL&Hlucs&Hres).
  assert (tree_unique tg_acc tr2) as Hunq2.
  { rewrite /tree_unique. erewrite <- tree_read_many_helper_2. 1: exact Hunq. exact Hoff. }
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  destruct (decide (l = off)) as [->|Hne].
  - odestruct tree_access_lookup_general_rev as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: split; first reflexivity; lia.
    erewrite <- access_same_rel_dec in Hreldec; last eapply HL.
    rewrite rel_dec_flip2 Hreldec /= in H4.
    odestruct tree_access_lookup_general_rev as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: split; first reflexivity; lia.
    eapply (apply_access_perm_read_reserved_backwards false) in H4 as HHres.
    2: done. destruct HHres as (acto & Hacto).
    rewrite bool_decide_true in H4; last done.
    rewrite /apply_access_perm /= Hacto /= in H4. repeat (case_match; try by simplify_eq; try simpl in H4).
    all: simpl in H4; simplify_eq; rewrite <- H4 in Hres; simpl in *; simplify_eq; done.
  - odestruct (tree_access_lookup_outside_rev l) as (it'&H1&H2&H3&H4).
    1: exact HL. 1: done. 2: exact Hlu. 1: lia.
    odestruct (tree_access_lookup_outside_rev l) as (itcs'&H1cs&H2cs&H3cs&H4cs).
    1: exact HL. 1: done. 2: exact Hlucs. 1: lia.
    rewrite -H4 in Hres. eapply IH.
    split; first exact H1.
    split; first by rewrite H3.
    split.
    { erewrite access_same_rel_dec; first done. apply HL. }
    exists itcs', l, im. split_and!; try done.
    eapply elem_of_list_to_set. eapply elem_of_list_to_set in HlL.
    eapply elem_of_cons in HlL as [->|HH]; done.
Qed.

Lemma tree_read_many_pseudo_helper_2 C tg_acc (L : list Z) tr1 trL S
  (Hwf1 : wf_tree tr1) :
  tree_unique tg_acc tr1 →
  let fn := (λ L tr, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C tr1 tg' it S acc → acc = ResConflicted) →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C trL tg' it (S ∪ {[ (tg_acc, list_to_set L) ]}) acc → acc = ResConflicted).
Proof.
  intros Hunq fn Hfn H tg' it' acc (tg_cous&LS&[HH|[= -> -> ]%elem_of_singleton]%elem_of_union&Hrst).
  - eapply tree_read_many_pseudo_helper_2_pers. 1: exact Hwf1. 1: apply Hunq. 1: apply Hfn.
    1: apply H. 1: do 2 eexists; done.
  - eapply tree_read_many_pseudo_helper_2_news. 1: exact Hwf1. 1: apply Hunq. 1: apply Hfn. 1: apply Hrst.
Qed.

Lemma tree_read_many_pseudo_helper_1 C (L : list (tag * gset Z)) tr1 trL
  (Hwf1 : wf_tree tr1) :
  (∀ tg S, (tg, S) ∈ L → tree_unique tg tr1) →
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg (l, 1%nat)) (Some tr1) (elements L)) (Some tr) E) in
  fn L tr1 = Some trL →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C tr1 tg' it ∅ acc → acc = ResConflicted) →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C trL tg' it (list_to_set L) acc → acc = ResConflicted).
Proof.
  intros Hunq fn Hfn H.
  induction L as [|(tg_acc&S) L IH] in trL,Hunq,Hfn|-*.
  1: rewrite list_to_set_nil; simpl in Hfn; injection Hfn as ->; done.
  simpl in Hfn.
  apply bind_Some in Hfn as (tr2&H1&H2).
  ospecialize (IH _ _ H1).
  { intros ???; eapply Hunq; by right. }
  rewrite list_to_set_cons union_comm_L.
  rewrite - (list_to_set_elements_L S).
  eapply tree_read_many_pseudo_helper_2. 3: exact H2. 3: done.
  1: eapply preserve_tag_count_wf. 1: apply tree_read_many_helper_1. 1: done. 1: exact H1.
  rewrite /tree_unique. erewrite <- tree_read_many_helper_1; last exact H1. eapply Hunq.
  by left.
Qed.

Lemma tree_read_many_pseudo_becomes_real C cid tr tr'
  (Hwf1 : wf_tree tr) :
  tree_read_all_protected_initialized C cid tr = Some tr' →
  (∀ tg' it acc, is_pseudo_conflicted_by_in C tr' tg' it (tree_get_all_protected_tags_initialized_locs cid tr) acc → acc = ResConflicted).
Proof.
  rewrite /tree_read_all_protected_initialized.
  pose (tree_get_all_protected_tags_initialized_locs cid tr) as L. fold L.
  intros Hfn. rewrite -(list_to_set_elements_L L).
  eapply tree_read_many_pseudo_helper_1.
  - done.
  - eintros tg S (it&Hlu%lookup_implies_contains&_)%elem_of_elements%tree_all_protected_initialized_elem_of.
    all: by eapply wf_tree_tree_unique.
  - apply Hfn.
  - intros ??? (?&?&[]%elem_of_empty&_).
Qed.

Lemma tree_read_many_preserve_protector_2 C tg_acc (L : list Z) tr1 trL
  (Hwf1 : wf_tree tr1) :
  let fn := (λ L tr, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → iprot it1 = iprot itL.
Proof.
  intros fn.
  induction L as [|off L IH] in trL|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tgl it1 itL Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  assert (∃ it, tree_lookup tr2 tgl it) as (it2&Hit2).
  { eapply lookup_implies_contains, count_gt0_exists in HitL.
    erewrite <- memory_access_tag_count in HitL; last done.
    eapply count_gt0_exists in HitL. by eapply unique_implies_lookup, wf_tree_tree_unique. }
  eapply apply_access_spec_per_node in HL as (itL'&Hacc&Hlu1&Hlu2). 2-3: by destruct Hit2.
  assert (tree_lookup trL tgl itL') as HH by done.
  pose proof (tree_lookup_unique _ _ _ _ HH HitL) as ->.
  symmetry in Hacc.
  eapply item_apply_access_preserves_metadata in Hacc as (He1&He2&He3).
  rewrite -He2. eapply IH; done.
Qed.

Lemma tree_read_many_preserve_protector_1 C (L : list (tag * gset Z)) tr1 trL
  (Hwf1 : wf_tree tr1) :
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg (l, 1%nat)) (Some tr1) (elements L)) (Some tr) E) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → iprot it1 = iprot itL.
Proof.
  intros fn.
  induction L as [|(tg_acc&S) L IH] in trL|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tgl it1 itL Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_1. 1: exact Hwf1. 1: apply Hoff. }
  assert (∃ it, tree_lookup tr2 tgl it) as (it2&Hit2).
  { eapply lookup_implies_contains, count_gt0_exists in HitL.
    erewrite <- tree_read_many_helper_2 in HitL; last done.
    eapply count_gt0_exists in HitL. by eapply unique_implies_lookup, wf_tree_tree_unique. }
  erewrite <- (tree_read_many_preserve_protector_2 _ _ _ _ _ Hwf2 HL _ it2 itL); try done.
  eapply IH. all: done.
Qed.

Lemma tree_read_many_preserve_protector C cid tr1 trL
  (Hwf1 : wf_tree tr1) :
  tree_read_all_protected_initialized C cid tr1 = Some trL →
  ∀ tgl it1 itL, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → iprot it1 = iprot itL.
Proof.
  rewrite /tree_read_all_protected_initialized.
  rewrite /set_fold /=. eapply tree_read_many_preserve_protector_1. done.
Qed.

Lemma tree_access_initialzed_equally_initialized b acc C tg_acc it_acc tr tr' off1 (sz : nat) offi :
  wf_tree tr →
  parents_more_init tr →
  tree_lookup tr tg_acc it_acc →
  (off1 ≤ offi < off1 + sz → initialized (item_lookup it_acc offi) = PermInit) →
  memory_access_maybe_nonchildren_only b acc C tg_acc (off1, sz) tr = Some tr' →
  ∀ tgl it it', tree_lookup tr tgl it → tree_lookup tr' tgl it' → initialized (item_lookup it offi) = initialized (item_lookup it' offi).
Proof.
  intros Hwf Hmoreinit Hlu Hinitacc Hacc tgl it it' Hit Hit'.
  destruct (decide (off1 ≤ offi < off1 + sz)) as [Hin|Hout]; last first.
  - eapply tree_access_lookup_outside in Hacc; [|done..|exact Hit].
    destruct Hacc as (itnew&Hitnewlu&Heq1&Heq2&Heq3).
    assert (itnew = it') as ->.
    { eapply tree_determined_unify. 1-2: eapply Hitnewlu. 1: apply Hit'. }
    by rewrite Heq3.
  - specialize (Hinitacc Hin).
    eapply tree_access_lookup_general in Hacc; [|done..|exact Hit].
    destruct Hacc as (itnew&Hitnewlu&Heq1&Heq2&Heq3).
    assert (itnew = it') as ->.
    { eapply tree_determined_unify. 1-2: eapply Hitnewlu. 1: apply Hit'. }
    edestruct maybe_non_children_only_effect_or_nop_strong as [(Heq&Haccrel)|(Heq&Hb&Himm)]; erewrite Heq in Heq3.
    2: by injection Heq3 as ->. clear Heq.
    eapply bind_Some in Heq3 as (pn&_&(pp&_&[= <-])%bind_Some).
    simpl. rewrite most_init_comm. rewrite /rel_dec in Haccrel|-*.
    destruct (decide (ParentChildIn tgl tg_acc tr)) as [HPCI|HnPCI]; last done. simpl.
    clear Haccrel.
    specialize (Hmoreinit tgl). eapply every_child_ParentChildIn in Hmoreinit; last eapply HPCI.
    2,3,5: eapply wf_tree_tree_unique; try done. 2,4: apply Hit. 2: apply Hlu.
    eapply every_node_eqv_universal in Hmoreinit.
    + eapply Hmoreinit. 2: exact Hinitacc. by eapply tree_lookup_correct_tag.
    + eapply exists_determined_exists; by eapply Hlu.
Qed.


Lemma tree_read_many_more_initialized_2 C tg_acc (L : list Z) tr1 trL
  (Hwf1 : wf_tree tr1) :
  let fn := (λ L tr, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = PermInit → initialized (item_lookup itL l) = PermInit.
Proof.
  intros fn.
  induction L as [|off L IH] in trL|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 l Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tgl it1 itL z Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  destruct (decide (z = off)) as [->|Hne].
  - eapply (tree_access_lookup_general_rev off) in HL as (it2 & Hit2 & _ & _ & Hperm). 2: done. 2: lia. 2: done.
    edestruct (maybe_non_children_only_effect_or_nop) as [Heq|Heq]; erewrite Heq in Hperm.
    2: { injection Hperm as <-. by eapply IH. }
    intros H1ini. enough (initialized (item_lookup it2 off) = PermInit) as HH. 2: by eapply IH.
    eapply bind_Some in Hperm as (x1&Hx1&(x2&Hx2&[= <-])%bind_Some). simpl. rewrite HH. done.
  - eapply (tree_access_lookup_outside_rev z) in HL as (it2 & Hit2 & _ & _ & Hperm). 2: done. 2: lia. 2: done.
    rewrite -Hperm. by eapply IH.
Qed.

Lemma tree_read_many_equally_initialized_2 C tg_acc (L : list Z) tr1 trL
  (Hwf1 : wf_tree tr1) (Hmore1 : parents_more_init tr1) :
  tree_contains tg_acc tr1 →
  (∀ z it, z ∈ L → tree_lookup tr1 tg_acc it → initialized (item_lookup it z) = PermInit) →
  let fn := (λ L tr, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = initialized (item_lookup itL l).
Proof.
  intros Hcont Hinit fn.
  induction L as [|off L IH] in trL,Hinit|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 l Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  intros tgl it1 itL z Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  assert (parents_more_init tr2) as Htr2.
  { eapply tree_read_many_more_init_helper_2. 4: exact Hoff. 1-3: done. }
  assert (tree_unique tg_acc tr1) as Hunqtr1.
  { by eapply Hwf1. }
  assert (tree_unique tg_acc tr2) as Hunqtr2.
  { rewrite /tree_unique in Hunqtr1|-*. erewrite <-tree_read_many_helper_2. 1: exact Hunqtr1. 1: exact Hoff. }
  assert (tree_unique tgl tr2) as Hunqtgl2.
  { rewrite /tree_unique. erewrite <-tree_read_many_helper_2. 2: exact Hoff. eapply Hwf1. by eapply Hit1. }
  eapply unique_implies_lookup in Hunqtgl2 as Hmid. destruct Hmid as (it2&Hit2).
  eapply unique_implies_lookup in Hunqtr2 as Hmid. destruct Hmid as (itacc2&Hitacc2).
  eapply unique_implies_lookup in Hunqtr1 as Hmid. destruct Hmid as (itacc1&Hitacc1).
  ospecialize (IH _ _ Hoff).
  { intros zz itz HzzL Hlu. eapply Hinit; last done. by right. }
  erewrite IH. 2-3: done.
  eapply tree_access_initialzed_equally_initialized. 5: exact HL. 1-2: done. 4: exact HitL. 3: exact Hit2. 1: done.
  intros H. assert (off = z) as -> by lia.
  eapply tree_read_many_more_initialized_2.
  2: exact Hoff. 1: done. 2: done. 1: done.
  eapply Hinit. 1: by left. done.
Qed.


Lemma tree_read_many_more_initialized_1 C (L : list (tag * gset Z)) tr1 trL
  (Hwf1 : wf_tree tr1) :
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg (l, 1%nat)) (Some tr1) (elements L)) (Some tr) E) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = PermInit → initialized (item_lookup itL l) = PermInit.
Proof.
  intros fn.
  induction L as [|(tg_acc&S) L IH] in trL|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 off Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  intros tgl it1 itL off Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_1. 1: exact Hwf1. 1: apply Hoff. }
  assert (∃ it, tree_lookup tr2 tgl it) as (it2&Hit2).
  { eapply lookup_implies_contains, count_gt0_exists in HitL.
    erewrite <- tree_read_many_helper_2 in HitL; last done.
    eapply count_gt0_exists in HitL. by eapply unique_implies_lookup, wf_tree_tree_unique. }
  intros Hini.
  erewrite <- (tree_read_many_more_initialized_2 _ _ _ _ _ Hwf2 HL _ it2 itL); try done.
  eapply IH. all: done.
Qed.

Lemma tree_read_many_equally_initialized_1 C (L : list (tag * gset Z)) tr1 trL
  (Hwf1 : wf_tree tr1) (Hmore1 : parents_more_init tr1) :
  (∀ tg_acc E, (tg_acc, E) ∈ L → tree_contains tg_acc tr1 ∧ (∀ z it, z ∈ E → tree_lookup tr1 tg_acc it → initialized (item_lookup it z) = PermInit)) →
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg (l, 1%nat)) (Some tr1) (elements L)) (Some tr) E) in
  fn L tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = initialized (item_lookup itL l).
Proof.
  intros Hinit fn.
  induction L as [|(tg_acc&S) L IH] in trL,Hinit|-*; simpl.
  { intros [= ->]. intros tg1 it1 it2 off Hit1 Hit2. enough (it1 = it2) by (by simplify_eq).
    by eapply tree_lookup_unique. }
  intros (tr2&Hoff&HL)%bind_Some.
  intros tgl it1 itL z Hit1 HitL.
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_1. 1: exact Hwf1. 1: apply Hoff. }
  assert (parents_more_init tr2) as Htr2.
  { eapply tree_read_many_more_init_helper_1. 4: exact Hoff. 1,3: done.
    intros ???. eapply Hinit. by right. }
  assert (tree_unique tg_acc tr1) as Hunqtr1.
  { eapply Hwf1, Hinit. by left. }
  assert (tree_unique tg_acc tr2) as Hunqtr2.
  { rewrite /tree_unique in Hunqtr1|-*. erewrite <-tree_read_many_helper_1. 1: exact Hunqtr1. 1: exact Hoff. }
  assert (tree_unique tgl tr2) as Hunqtgl2.
  { rewrite /tree_unique. erewrite <-tree_read_many_helper_1. 2: exact Hoff. eapply Hwf1. by eapply Hit1. }
  eapply unique_implies_lookup in Hunqtgl2 as Hmid. destruct Hmid as (it2&Hit2).
  eapply unique_implies_lookup in Hunqtr2 as Hmid. destruct Hmid as (itacc2&Hitacc2).
  eapply unique_implies_lookup in Hunqtr1 as Hmid. destruct Hmid as (itacc1&Hitacc1).
  ospecialize (IH _ _ Hoff).
  { intros tgE E HE. split. 1: eapply Hinit; by right. intros zz itz HzzL Hlu. eapply Hinit; last done. 1: by right. done. }
  erewrite IH. 2-3: done.
  eapply tree_read_many_equally_initialized_2. 5: exact HL. 1-2: done. 4: exact HitL. 3: exact Hit2. 1: by eapply unique_exists.
  intros zz it HS Hlu.
  eapply tree_read_many_more_initialized_1.
  2: exact Hoff. 1: done. 2: done. 1: done.
  eapply Hinit. 1: by left. 2: done. eapply elem_of_elements. done.
Qed.

Lemma tree_read_many_more_initialized C cid tr1 trL
  (Hwf1 : wf_tree tr1) :
  tree_read_all_protected_initialized C cid tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = PermInit → initialized (item_lookup itL l) = PermInit.
Proof.
  rewrite /tree_read_all_protected_initialized.
  rewrite /set_fold /=. eapply tree_read_many_more_initialized_1. done.
Qed.

Lemma tree_read_many_equally_initialized C cid tr1 trL
  (Hwf1 : wf_tree tr1) (Hmi : parents_more_init tr1) :
  tree_read_all_protected_initialized C cid tr1 = Some trL →
  ∀ tgl it1 itL l, tree_lookup tr1 tgl it1 → tree_lookup trL tgl itL → initialized (item_lookup it1 l) = initialized (item_lookup itL l).
Proof.
  rewrite /tree_read_all_protected_initialized.
  rewrite /set_fold /=. eapply tree_read_many_equally_initialized_1.
  - done.
  - done.
  - intros tg E (it&Hit&Hprot&HHit)%elem_of_elements%tree_all_protected_initialized_elem_of.
    2: by eapply Hwf1.
    split. 1: eapply Hit.
    intros z it' H%HHit Hlu'.
    enough (it = it') as ->; first done.
    eapply tree_determined_unify. 3: eapply Hlu'. 1-2: eapply Hit.
Qed.

Lemma trees_equal_remove_call C tr1' tr2' tr1 tr2 cid :
  wf_tree tr1 → wf_tree tr2 → parents_more_init tr1 → parents_more_init tr2 →
  tree_read_all_protected_initialized C cid tr1 = Some tr1' →
  tree_read_all_protected_initialized C cid tr2 = Some tr2' →
  tree_equal C tr1' tr2' →
  tree_equal (C ∖ {[ cid ]}) tr1' tr2'.
Proof.
  intros Hwf1 Hwf2 Hpmi1 Hpmi2 Hrai1 Hrai2 (He1&He2&He3).
  split_and!; try done.
  intros tg Hcont. specialize (He3 tg Hcont) as (it1 & it2 & Hlu1 & Hlu2 & Hutc).
  do 2 eexists. split_and!; try done.
  specialize (tree_read_many_pseudo_becomes_real _ _ _ _ Hwf1 Hrai1 tg it1) as Hrai1'.
  specialize (tree_read_many_pseudo_becomes_real _ _ _ _ Hwf2 Hrai2 tg it2) as Hrai2'.

  intros l. specialize (Hutc l) as (Hproteq&Hutc).
  split; first done.

  inversion Hutc as [x1 x2 Hlu|ini im confl1 confl2 (cc&Hcc&Hccact) Hpc1 Hpc2 Heqi1 Heqi2|ini im confl1 confl2 Hnprot]; simplify_eq.
  - econstructor 1.
  - destruct (decide (cc = cid)) as [<-|Hne].
    + econstructor 3. intros (cc'&Hcc'&Hccact').
      rewrite /protector_is_for_call in Hcc,Hcc'. rewrite Hcc in Hcc'. injection Hcc' as ->.
      eapply elem_of_difference in Hccact' as (_&H).
      setoid_rewrite not_elem_of_singleton in H. done.
    + econstructor 2.
      * exists cc. split; first done.
        rewrite /call_is_active. set_solver.
      * inversion Hpc1 as [|tg_cs it_cs Hreldec Hlucs (cccs&Hp1cs&Hp2cs) Hpermcs Hinitcs Heq]; first by econstructor.
        simplify_eq.
        destruct (decide (cccs = cid)) as [<-|Hnecs].
        2: econstructor 2; try done; exists cccs; split; try done.
        2: rewrite /call_is_active in Hp2cs|-*; set_solver.
        exfalso. enough (ResActivable = ResConflicted) by done.
        assert (∃ ii, tree_lookup tr1 tg_cs ii) as (it_cs1&Hlucs1).
        { eapply lookup_implies_contains, count_gt0_exists in Hlucs.
          erewrite <- tree_read_all_protected_initialized_tag_count in Hlucs; last done.
          eapply count_gt0_exists in Hlucs. by eapply unique_implies_lookup, wf_tree_tree_unique. }
        eapply Hrai1'. eexists tg_cs, (mem_enumerate_sat (λ p : lazy_permission, if initialized p then true else false) (iperm it_cs1)).
        split.
        { eapply tree_all_protected_initialized_elem_of. 1: by eapply wf_tree_tree_unique.
          exists it_cs1. split; first done. split; last by eapply mem_enumerate_initalized.
          erewrite tree_read_many_preserve_protector. 1: done. 3-4: done. 1: done. 1: done. }
        split; first done. split; first by eexists. split; first done.
        eexists it_cs, l, im. split_and!. 2: done. 2: by rewrite -Heqi1.
        eapply mem_enumerate_initalized. rewrite -Hinitcs.
        eapply tree_read_many_equally_initialized. 3: exact Hrai1. all: done.
      * inversion Hpc2 as [|tg_cs it_cs Hreldec Hlucs (cccs&Hp1cs&Hp2cs) Hpermcs Hinitcs Heq]; first by econstructor.
        simplify_eq.
        destruct (decide (cccs = cid)) as [<-|Hnecs].
        2: econstructor 2; try done; exists cccs; split; try done.
        2: rewrite /call_is_active in Hp2cs|-*; set_solver.
        exfalso. enough (ResActivable = ResConflicted) by done.
        assert (∃ ii, tree_lookup tr2 tg_cs ii) as (it_cs1&Hlucs1).
        { eapply lookup_implies_contains, count_gt0_exists in Hlucs.
          erewrite <- tree_read_all_protected_initialized_tag_count in Hlucs; last done.
          eapply count_gt0_exists in Hlucs. by eapply unique_implies_lookup, wf_tree_tree_unique. }
        eapply Hrai2'. eexists tg_cs, (mem_enumerate_sat (λ p : lazy_permission, if initialized p then true else false) (iperm it_cs1)).
        split.
        { eapply tree_all_protected_initialized_elem_of. 1: by eapply wf_tree_tree_unique.
          exists it_cs1. split; first done. split; last by eapply mem_enumerate_initalized.
          erewrite tree_read_many_preserve_protector. 1: done. 3-4: done. 1: done. 1: done. }
        split; first done. rewrite -Hproteq. split; first by eexists. split; first done.
        eexists it_cs, l, im. split_and!. 2: done. 2: by rewrite -Heqi2.
        eapply mem_enumerate_initalized. rewrite -Hinitcs.
        eapply tree_read_many_equally_initialized. 3: exact Hrai2. all: done.
  - econstructor 3.
    intros (cc&Hcc&Hccact). eapply Hnprot. eexists. split; first done. by eapply elem_of_difference in Hccact as (H1&H2).
Qed.
