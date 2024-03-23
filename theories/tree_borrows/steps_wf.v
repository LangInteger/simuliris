(** This file has been adapted from the Stacked Borrows development, available at 
https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.tree_borrows Require Import helpers.
From simuliris.tree_borrows Require Export defs steps_foreach steps_access steps_preserve bor_lemmas.
From iris.prelude Require Import options.



Lemma wf_tree_tree_unique tr :
  wf_tree tr →
  ∀ tg,
  tree_contains tg tr →
  tree_unique tg tr.
Proof.
  intros Hwf tg Hcont.
  by apply (Hwf tg Hcont).
Qed.

Lemma wf_tree_tree_item_determined tr :
  wf_tree tr →
  ∀ tg,
  tree_contains tg tr →
  ∃ it, tree_item_determined tg it tr.
Proof.
  intros Hwf tg Hcont.
  eapply unique_lookup, wf_tree_tree_unique.
  all: done.
Qed.


Lemma wf_init_state : state_wf init_state.
Proof.
  constructor; simpl; try split; try intros ?; try set_solver.
Qed.

(** Steps preserve wellformedness *)

Lemma wf_item_mono it :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (item_wf it).
Proof.
  move=> ?? Le1 ?? Le2 [WFle WFprot].
  split.
  - intros tg tgit. specialize (WFle tg tgit). lia.
  - intros cid protit. specialize (WFprot cid protit). lia.
Qed.

Lemma tree_items_compat_nexts_mono tr :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (tree_items_compat_nexts tr).
Proof.
  intros ?? Le1 ? ? Le2 WF.
  eapply every_node_eqv_universal.
  intros it Ex.
  eapply every_node_eqv_universal in WF; last done.
  eapply wf_item_mono; eauto.
Qed.

Lemma trees_compat_nexts_mono trs :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (trees_compat_nexts trs).
Proof.
  move=> ?? Le1 ? ? Le2 WF ?? /WF Hf.
  eapply tree_items_compat_nexts_mono; eassumption.
Qed.

Lemma wf_mem_tag_mono h :
  Proper ((≤)%nat ==> impl) (wf_mem_tag h).
Proof.
  move => ??? WF ?? tg Access.
  specialize (WF _ _ tg Access); simpl in WF.
  lia.
Qed.

Definition preserve_tree_compat_nexts (fn:app (tree item)) nxtp nxtp' nxtc nxtc' :=
  forall tr tr', tree_items_compat_nexts tr nxtp nxtc -> fn tr = Some tr' -> tree_items_compat_nexts tr' nxtp' nxtc'.

Definition preserve_tree_tag_count (fn:app (tree item)) :=
  forall tr tr' tg, fn tr = Some tr' -> tree_count_tg tg tr = tree_count_tg tg tr'.

Lemma preserve_tag_count_wf fn tr tr' :
  preserve_tree_tag_count fn →
  wf_tree tr →
  fn tr = Some tr' →
  wf_tree tr'.
Proof.
  intros Hf H1 Heq tg Htg%count_gt0_exists.
  erewrite <- Hf in Htg; last done.
  eapply count_gt0_exists in Htg.
  specialize (H1 _ Htg) as Hunq.
  rewrite /tree_unique in Hunq.
  by erewrite Hf in Hunq.
Qed.

Lemma preserve_tag_count_contains fn tr tr' tg :
  preserve_tree_tag_count fn →
  tree_contains tg tr →
  fn tr = Some tr' →
  tree_contains tg tr'.
Proof.
  intros Hf H1%count_gt0_exists Heq.
  eapply count_gt0_exists.
  by erewrite <- Hf.
Qed.

Lemma preserve_tag_count_contains_2 fn tr tr' tg :
  preserve_tree_tag_count fn →
  tree_contains tg tr' →
  fn tr = Some tr' →
  tree_contains tg tr.
Proof.
  intros Hf H1%count_gt0_exists Heq.
  eapply count_gt0_exists.
  by erewrite Hf.
Qed.

Lemma tree_empty_iff_count tr: 
  (exists tg, tree_count_tg tg tr ≥ 1) ↔ tr ≠ empty.
Proof.
  destruct tr as [|it cld slb].
  - split; last done. simpl.
    intros (tg & Htg). lia.
  - split; first done.
    intros _. exists (it.(itag)).
    rewrite /= bool_decide_eq_true_2 //.
    lia.
Qed.

Lemma preserve_tag_count_nonempty fn tr tr' :
  preserve_tree_tag_count fn →
  tr ≠ empty →
  fn tr = Some tr' →
  tr' ≠ empty.
Proof.
  intros Hf (tg & Htg)%tree_empty_iff_count Heq.
  eapply tree_empty_iff_count. exists tg.
  by erewrite <- Hf.
Qed.

(* Since there are a lot of layers to the model (trees -> tree -> item -> perms)
   that we mostly don't really need to reason about (e.g. tree_item_included is per-item
   and we don't need tree-wide reasoning) we start with some lemmas to turn the per-trees
   wf preservation to per-item wf preservation *)

Lemma apply_within_trees_wf trs trs' blk fn:
  apply_within_trees fn blk trs = Some trs' ->
  preserve_tree_tag_count fn ->
  wf_trees trs -> wf_trees trs'.
Proof.
  intros App WFfn (WFeach & WFglob).
  unfold apply_within_trees in App; destruct (trs !! blk) as [t|] eqn:Lookup;
  simpl in App; last done.
  apply bind_Some in App as (t2 & Ht2 & [= <-]). split.
  - intros tr' it' [(<- & <-)|(Hne1 & Hne2)]%lookup_insert_Some.
    + eapply preserve_tag_count_wf; try done.
      by eapply WFeach.
    + by eapply WFeach.
  - intros blk1 blk2 tr1 tr2 tg [(Heq1 & Heq2)|(Hne1 & Hne2)]%lookup_insert_Some [(Heq1' & Heq2')|(Hne1' & Hne2')]%lookup_insert_Some Hcont1 Hcont2;
    simplify_eq; first done.
    + eapply WFglob; try done.
      eapply preserve_tag_count_contains_2; last done; done.
    + eapply WFglob; try done.
      eapply preserve_tag_count_contains_2; last done; done.
    + by eapply WFglob.
Qed.

Lemma apply_within_trees_compat trs trs' nxtp nxtp' nxtc nxtc' blk fn:
  apply_within_trees fn blk trs = Some trs' ->
  (forall tr, tree_items_compat_nexts tr nxtp nxtc -> tree_items_compat_nexts tr nxtp' nxtc') ->
  preserve_tree_compat_nexts fn nxtp nxtp' nxtc nxtc' ->
  trees_compat_nexts trs nxtp nxtc -> trees_compat_nexts trs' nxtp' nxtc'.
Proof.
  intros App WFtrans WFfn WF.
  unfold apply_within_trees in App; destruct (trs !! blk) as [t|] eqn:Lookup; inversion App as [App0]; clear App.
  destruct (fn t) eqn:Map; inversion App0 as [E]; clear App0.
  intro blk'; destruct (decide (blk = blk')); intros tr Lookup'.
  all: inversion E; simplify_eq.
  (* Handle the insertion/deletion *)
  1: rewrite lookup_insert in Lookup'.
  2: rewrite lookup_insert_ne in Lookup'; [|done].
  all: simplify_eq.
  (* WF impl *)
  - apply (WFfn t); [|done]; apply (WF blk' _ Lookup).
  - apply (WFtrans tr); apply (WF blk' _ Lookup').
Qed.

Lemma tree_items_compat_next_not_containing tg1 tg2 tr ev :
  tree_contains tg1 tr →
  tree_items_compat_nexts tr tg2 ev →
  tg1 >= tg2 →
  False.
Proof.
  intros Hintro Hcompat Hle.
  eapply (exists_node_increasing _ (λ _, False)) in Hintro.
  1: eapply exists_node_eqv_existential in Hintro as (?&?&[]).
  eapply every_node_increasing; first exact Hcompat.
  eapply every_node_eqv_universal.
  intros n ? (H1&H2) H3%H1. lia.
Qed.

Lemma apply_within_trees_compat_both trs trs' nxtp nxtp' nxtc nxtc' blk fn:
  apply_within_trees fn blk trs = Some trs' ->
  (forall tr, tree_items_compat_nexts tr nxtp nxtc -> tree_items_compat_nexts tr nxtp' nxtc') ->
  (forall tr tr', fn tr = Some tr' -> tree_items_compat_nexts tr nxtp nxtc -> wf_tree tr ->
          tree_items_compat_nexts tr' nxtp' nxtc' /\ wf_tree tr') ->
  (forall tr tr' tg, fn tr = Some tr' -> tree_contains tg tr' -> tree_contains tg tr \/ tg >= nxtp) ->
  trees_compat_nexts trs nxtp nxtc /\
  wf_trees trs ->
  trees_compat_nexts trs' nxtp' nxtc' /\
  wf_trees trs'.
Proof.
  intros (tr&Htr&(tr'&Hfn&[= <-])%bind_Some)%bind_Some WFtrans WFfn Hnewtags (WF1 & WF2).
  split; last split.
  - intros blk1 tr1 [(->&->)|(Hne&Hin)]%lookup_insert_Some.
    + eapply WFfn; first done. 1: by eapply WF1. 1: by eapply WF2.
    + by eapply WFtrans, WF1.
  - intros blk1 tr1 [(->&->)|(Hne&Hin)]%lookup_insert_Some.
    + eapply WFfn; first done. 1: by eapply WF1. 1: by eapply WF2.
    + by eapply WF2.
  - intros blk1 blk2 tr1 tr2 tg.
    intros [(?&?)|(Hne1&Hin1)]%lookup_insert_Some [(?&?)|(Hne2&Hin2)]%lookup_insert_Some;
      simplify_eq; intros Hcont1 Hcont2.
    + done.
    + destruct (Hnewtags _ _ _ Hfn Hcont1) as [Hold|Hgt].
      1: by eapply WF2.
      exfalso; eapply tree_items_compat_next_not_containing; first exact Hcont2.
      1: by eapply WF1. done.
    + destruct (Hnewtags _ _ _ Hfn Hcont2) as [Hold|Hgt].
      1: by eapply WF2.
      exfalso; eapply tree_items_compat_next_not_containing; first exact Hcont1.
      1: by eapply WF1. done.
    + by eapply WF2.
Qed.

Lemma apply_within_trees_compat_nonempty trs1 trs2 blk fn :
  wf_non_empty trs1 →
  (∀ tr1 tr2, tr1 ≠ empty → fn tr1 = Some tr2 → tr2 ≠ empty) →
  apply_within_trees fn blk trs1 = Some trs2 →
  wf_non_empty trs2.
Proof.
  intros Hwf Hempt (tr1&H1&(tr2&H2&[= <-])%bind_Some)%bind_Some blk' tr' [(<-&<-)|(Hin&Hne)]%lookup_insert_Some.
  - eapply Hempt; last done. by eapply Hwf.
  - by eapply Hwf.
Qed.

Lemma delete_trees_preserve_nonempty trs blk :
  wf_non_empty trs ->
  wf_non_empty (delete blk trs).
Proof.
  intros WF blk' tr Delete.
  eapply WF.
  apply (proj1 (lookup_delete_Some _ _ _ _) Delete).
Qed.

Lemma apply_within_trees_bind trs blk fn1 fn2 :
  apply_within_trees (λ x, y ← fn1 x; fn2 y) blk trs =
  trs' ← apply_within_trees fn1 blk trs;
  apply_within_trees fn2 blk trs'.
Proof.
  rewrite /apply_within_trees /=.
  destruct (trs !! blk) as [tr1|] eqn:Heq; last done.
  rewrite /=. destruct (fn1 tr1) as [tr1b|]; last done.
  rewrite /= lookup_insert /=. destruct (fn2 tr1b) as [tr1c|]; last done.
  rewrite /= insert_insert //.
Qed.

Lemma apply_within_trees_same_dom (trs trs' : gmap positive (tree item)) blk fn :
  apply_within_trees fn blk trs = Some trs' ->
  dom trs = dom trs'.
Proof.
  unfold apply_within_trees.
  destruct (trs !! blk) as [t|] eqn:Lookup; rewrite !Lookup; simpl; [|intro H; inversion H].
  destruct (fn t); simpl; [|intro H; inversion H].
  intro H; injection H; clear H; intro; subst.
  rewrite dom_insert_L.
  rewrite subseteq_union_1_L; [set_solver|].
  rewrite singleton_subseteq_l.
  apply elem_of_dom.
  auto.
Qed.

Lemma extend_trees_wf trs tr blk :
  wf_trees trs →
  wf_tree tr →
  (∀ blk tr' tg, trs !! blk = Some tr' → tree_contains tg tr → tree_contains tg tr' → False) →
  wf_trees (<[blk := tr]> trs).
Proof.
  intros (WFs & Hunq) WF Hisnew. split.
  - intros blk' tr' [(-> & ->)|(Hne & Hin)]%lookup_insert_Some; first done.
    by eapply WFs.
  - intros blk1 blk2 tr1 tr2 tg.
    intros [(?&?)|(Hne1&Hin1)]%lookup_insert_Some [(?&?)|(Hne2&Hin2)]%lookup_insert_Some;
    simplify_eq; intros Hcont1 Hcont2.
    + done.
    + exfalso. by eapply Hisnew.
    + exfalso. by eapply Hisnew.
    + by eapply Hunq.
Qed.

Lemma extend_trees_compat_nexts trs tr blk snp snc :
  trees_compat_nexts trs snp snc →
  tree_items_compat_nexts tr snp snc →
  trees_compat_nexts (<[blk := tr]> trs) snp snc.
Proof.
  intros H1 H2 blk' tr' [(<-&<-)|(Hne1&Hin1)]%lookup_insert_Some; first done.
  by eapply H1.
Qed.

Lemma delete_trees_wf trs blk :
  wf_trees trs ->
  wf_trees (delete blk trs).
Proof.
  intros (Heach&Hunq); split.
  - intros blk' tr' (Hin&Hne)%lookup_delete_Some.
    by eapply Heach.
  - intros blk1 blk2 tr1 tr2 tg (_&Hin1)%lookup_delete_Some (_&Hin2)%lookup_delete_Some.
    by eapply Hunq.
Qed.

Lemma delete_trees_compat_nexts trs blk nxtp nxtc :
  trees_compat_nexts trs nxtp nxtc ->
  trees_compat_nexts (delete blk trs) nxtp nxtc.
Proof.
  intros WFs blk'.
  intros tr' (Hin&Hne)%lookup_delete_Some.
  by eapply WFs.
Qed.


(* Now we get from per-tree to per-item *)
Lemma tree_joinmap_preserve_prop tr tr' (fn:item -> option item) (P:item -> Prop) :
  (forall it it', fn it = Some it' -> P it -> P it') ->
  every_node P tr ->
  join_nodes (map_nodes fn tr) = Some tr' ->
  every_node P tr'.
Proof.
  intros Preserve All Join.
  pose (proj1 (join_success_condition _) (mk_is_Some _ _ Join)) as AllSome.
  generalize dependent tr'.
  induction tr as [|data ? IHtr1 ? IHtr2]; intros tr' JoinSome AllSome; simpl in *; [injection JoinSome; intros; simplify_eq; auto|].
  destruct AllSome as [[data' Some0] [Some1 Some2]].
  rewrite Some0 in JoinSome; simpl in JoinSome.
  destruct (proj2 (join_success_condition _) Some1) as [tr1' Some1'].
  destruct (proj2 (join_success_condition _) Some2) as [tr2' Some2'].
  rewrite Some1' in JoinSome; rewrite Some2' in JoinSome; simpl in JoinSome.
  injection JoinSome; intros; subst.
  destruct All as [All0 [All1 All2]].
  try repeat split.
  - apply (Preserve data _ Some0 All0).
  - apply (IHtr1 All1); apply Some1'.
  - apply (IHtr2 All2); apply Some2'.
Qed.

Lemma joinmap_preserve_tree_tag_count_dep fn :
  (∀ tr, preserve_item_metadata (fn tr)) →
  preserve_tree_tag_count (fun tr => join_nodes (map_nodes (fn tr) tr)).
Proof.
  intros Hfn tr.
  remember (fn tr) as fntr eqn:Heq. specialize (Hfn tr). rewrite <- Heq in Hfn.
  clear Heq.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; intros tr' tg Heq.
  1: by injection Heq as <-.
  move : Heq => /=.
  intros (itroot&Hitroot&(tr1'&Htr1'&(tr2'&Htr2&[= <-])%bind_Some)%bind_Some)%bind_Some.
  simpl; f_equal; first f_equal.
  - destruct (Hfn _ _ Hitroot) as (H1 & H2 & H3).
    rewrite !bool_decide_decide.
    destruct decide as [Heq|Heq]; rewrite H1 in Heq.
    1: rewrite decide_True //. rewrite decide_False //.
  - by eapply IHtr1.
  - by apply IHtr2.
Qed.

Lemma joinmap_preserve_tree_tag_count fn :
  preserve_item_metadata fn →
  preserve_tree_tag_count (fun tr => join_nodes (map_nodes fn tr)).
Proof.
  intros H. by eapply joinmap_preserve_tree_tag_count_dep.
Qed.

Lemma deallocate_preserve_tree_tag_count cids tg range :
  preserve_tree_tag_count (memory_deallocate cids tg range).
Proof.
  intros tr tr' Nonempty Dealloc.
  rewrite /memory_deallocate /memory_access_nonchildren_only in Dealloc.
  eapply bind_Some in Dealloc as (trm & H1 & H2).
  eapply joinmap_preserve_tree_tag_count in H1.
  2: eapply item_apply_access_preserves_metadata_dep.
  erewrite H1.
  eapply joinmap_preserve_tree_tag_count.
  2: exact H2.
  intros it1 it2 Heq; repeat destruct bool_decide; simpl in Heq; simplify_eq; done.
Qed.

Lemma create_child_preserve_nonempty cids oldtg newtg pk rk cid tr tr' :
  create_child cids oldtg newtg pk rk cid tr = Some tr' →
  tr ≠ empty →
  tr' ≠ empty.
Proof.
  intros [= <-] Hne.
  destruct tr as [|data].
  1: contradiction.
  simpl. destruct (decide (IsTag oldtg data)); intro H; inversion H.
Qed.

Lemma tree_apply_access_same_count
  {tr tr' tr0 tg fn cids acc_tg range} :
  join_nodes
    (map_nodes
       (λ it : item,
          item_apply_access fn cids (rel_dec tr0 acc_tg (itag it)) range it) tr) =
  Some tr' → tree_count_tg tg tr = tree_count_tg tg tr'.
Proof.
  intros H.
  eapply joinmap_preserve_tree_tag_count; last done.
  eapply item_apply_access_preserves_metadata_dep.
Qed.

Lemma tree_apply_access_preserve_unique
  {tr tr' tg fn cids acc_tg range} :
  tree_apply_access fn cids acc_tg range tr = Some tr' ->
  tree_unique tg tr <-> tree_unique tg tr'.
Proof.
  rewrite /tree_unique. intro Access.
  erewrite tree_apply_access_same_count; [|exact Access].
  tauto.
Qed.

Lemma tree_apply_access_wf fn tr tr' cids tg range :
  wf_tree tr ->
  tree_apply_access fn cids tg range tr = Some tr' ->
  wf_tree tr'.
Proof.
  eapply preserve_tag_count_wf.
  rewrite /tree_apply_access.
  eapply joinmap_preserve_tree_tag_count_dep.
  intros ?. eapply item_apply_access_preserves_metadata_dep.
Qed.

Lemma tree_apply_access_compat_nexts fn tr tr' cids tg range nxtp nxtc :
  tree_items_compat_nexts tr nxtp nxtc ->
  tree_apply_access fn cids tg range tr = Some tr' ->
  tree_items_compat_nexts tr' nxtp nxtc.
Proof.
  eapply tree_joinmap_preserve_prop.
  intros it1 it2 (H1&H2&H3)%item_apply_access_preserves_metadata.
  rewrite /item_wf /= H1 H2. done.
Qed.
Lemma join_map_id_is_Some_identical (P : item -> bool) tr tr' :
  join_nodes (map_nodes (fun it => if P it then None else Some it) tr) = Some tr' ->
  tr = tr'.
Proof.
  revert tr'.
  induction tr as [|data ? IHtr1 ? IHtr2]; intros tr' Success; simpl in *.
  - injection Success; tauto.
  - destruct (P data); simpl in *; [discriminate|].
    destruct (join_nodes _) as [tr1'|]; simpl in *; [|discriminate].
    destruct (join_nodes _) as [tr2'|]; simpl in *; [|discriminate].
    injection Success.
    erewrite IHtr1; [|reflexivity].
    erewrite IHtr2; [|reflexivity].
    tauto.
Qed.

Lemma memory_deallocate_wf tr tr' cids tg range :
  wf_tree tr ->
  memory_deallocate cids tg range tr = Some tr' ->
  wf_tree tr'.
Proof.
  rewrite /memory_deallocate /memory_access_nonchildren_only.
  intros Hwf (mid&H1&H2)%bind_Some.
  eapply tree_apply_access_wf in H1; last done.
  apply join_map_id_is_Some_identical in H2.
  by subst mid.
Qed.

Lemma memory_deallocate_compat_nexts tr tr' cids tg range nxtp nxtc :
  tree_items_compat_nexts tr nxtp nxtc ->
  memory_deallocate cids tg range tr = Some tr' ->
  tree_items_compat_nexts tr' nxtp nxtc.
Proof.
  intros WF Dealloc.
  rewrite /memory_deallocate /memory_access_nonchildren_only /memory_access_maybe_nonchildren_only /= in Dealloc.
  remember (tree_apply_access _ _ _ _ _) as tr''.
  destruct tr'' as [tr''|]; simpl in Dealloc; [|discriminate].
  assert (tree_items_compat_nexts tr'' nxtp nxtc) as WF''. {
    apply (tree_apply_access_compat_nexts _ _ _ _ _ _ _ _ WF ltac:(symmetry; eassumption)).
  }
  erewrite <- (join_map_id_is_Some_identical _ tr'' tr').
  - assumption.
  - exact Dealloc.
Qed.

Lemma memory_access_wf b tr tr' acc cids tg range  :
  wf_tree tr ->
  memory_access_maybe_nonchildren_only b acc cids tg range tr = Some tr' ->
  wf_tree tr'.
Proof.
  intros WF Dealloc.
  by eapply tree_apply_access_wf.
Qed.

Lemma memory_access_tag_count b acc cids tg range :
  preserve_tree_tag_count (memory_access_maybe_nonchildren_only b acc cids tg range).
Proof.
  eapply joinmap_preserve_tree_tag_count_dep.
  intros tr. eapply item_apply_access_preserves_metadata_dep.
Qed.

Lemma memory_access_compat_nexts b tr tr' acc cids tg range nxtp nxtc :
  tree_items_compat_nexts tr nxtp nxtc ->
  memory_access_maybe_nonchildren_only b acc cids tg range tr = Some tr' ->
  tree_items_compat_nexts tr' nxtp nxtc.
Proof.
  intros WF Dealloc.
  by eapply tree_apply_access_compat_nexts.
Qed.


Lemma init_mem_singleton_dom (blk:block) n sz :
  (sz > 0)%nat ->
  ({[blk]}:gset block) = set_map fst (dom (init_mem (blk, n) sz ∅)).
Proof.
  induction sz as [|sz IHsz] in n|-*; simpl; intros H.
  - inversion H.
  - rewrite dom_insert_L set_map_union_L set_map_singleton_L //=.
    destruct sz as [|sz].
    + rewrite dom_empty_L set_map_empty union_empty_r_L //.
    + rewrite /shift_loc. rewrite <- IHsz; [|lia].
      set_solver.
Qed.

Lemma same_blocks_init_extend h sz trs nxtp :
  (sz > 0)%nat ->
  same_blocks h trs ->
  same_blocks (init_mem (fresh_block h, 0) sz h)
    (extend_trees nxtp (fresh_block h) trs).
Proof.
  intros Nonzero Same.
  rewrite /same_blocks init_mem_dom dom_insert_L set_map_union_L.
  rewrite union_comm_L.
  rewrite /same_blocks in Same; rewrite Same; clear Same.
  erewrite init_mem_singleton_dom; [|eauto].
  set_solver.
Qed.

Lemma wf_init_tree t' :
  wf_tree (init_tree t').
Proof.
  intros tg H.
  cbv in H. destruct_or!; try done.
  subst tg.
  by rewrite /tree_unique /init_tree /= bool_decide_true.
Qed.

Lemma init_tree_compat_nexts c t t' :
  (t' < t)%nat ->
  tree_items_compat_nexts (init_tree t') t c.
Proof.
  intros Hok. cbv.
  repeat split.
  - intros ? ->. lia.
  - done.
Qed.

Lemma init_tree_nonempty t :
  forall tr, tr = (init_tree t) -> tr ≠ empty.
Proof.
  intros. subst.
  rewrite /init_tree //.
Qed.

Lemma init_tree_contains_only tg1 tg2 :
  tree_contains tg1 (init_tree tg2) -> tg1 = tg2.
Proof.
  intros H. cbv in H. by destruct_or!.
Qed.

Lemma alloc_step_wf (σ σ': state) e e' l bor ptr efs:
  mem_expr_step σ.(shp) e (AllocEvt l bor ptr) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (AllocEvt l bor ptr)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF. inversion BS. clear BS. simplify_eq.
  inversion IS as [x| | | | | | |]; clear IS. simpl in *; simplify_eq. constructor; simpl.
  - apply same_blocks_init_extend; [lia|].
    apply WF.
  - apply extend_trees_wf.
    * apply WF.
    * apply wf_init_tree.
    * intros blk tro tg Hin Hinit%init_tree_contains_only Hintro.
      subst tg.
      pose proof (state_wf_tree_compat _ WF _ _ Hin) as Hcompat.
      simpl in Hcompat.
      eapply tree_items_compat_next_not_containing; [done..|]; lia.
  - eapply extend_trees_compat_nexts.
    * eapply trees_compat_nexts_mono; last eapply WF.
      all: simpl; lia.
    * eapply init_tree_compat_nexts; lia. 
  - rewrite /extend_trees. intros blk tr' [(<-&<-)|(Hne1&Hin)]%lookup_insert_Some.
    2: by eapply (state_wf_non_empty _ WF).
    by eapply init_tree_nonempty.
  - apply WF.
Qed.

Lemma trees_deallocate_isSome trs cids tg blk m sz :
  is_Some (apply_within_trees (memory_deallocate cids tg (m, sz)) blk trs) ->
  exists tr, trs !! blk = Some tr /\ is_Some (memory_deallocate cids tg (m, sz) tr).
Proof.
  unfold apply_within_trees. destruct (trs !! blk) as [t|]; simpl; [|intro H; inversion H as [? H0]; inversion H0].
  intro isSome. exists t. destruct (memory_deallocate cids tg (m, sz) t) as [t'|]; simpl; [|inversion isSome as [? H0]; inversion H0].
  auto.
Qed.


Lemma free_mem_subset h blk n (sz:nat) :
  dom (free_mem (blk, n) sz h) ⊆ dom h.
Proof.
  revert n.
  induction sz; intros n; rewrite //=.
  rewrite /shift_loc //= dom_delete.
  set_solver.
Qed.

Lemma free_mem_remove_loc h blk n (sz:nat) m :
  (0 ≤ m < sz) ->
  dom (free_mem (blk, n) sz h) ## {[(blk, n + m)]}.
Proof.
  revert n m h.
  induction sz as [|? IHsz]; intros n m h [??].
  - lia.
  - rewrite //= dom_delete.
    destruct (decide (m = 0)).
    + subst. rewrite Z.add_0_r.
      set_solver.
    + eapply disjoint_difference_l2.
      rewrite /shift_loc //=.
      replace (n + m) with (n + 1 + (m - 1)) by lia.
      apply IHsz.
      lia.
Qed.

Lemma free_mem_delete h k1 k2 sz : free_mem k1 sz (delete k2 h) = delete k2 (free_mem k1 sz h).
Proof.
  induction sz as [|n IH] in h,k1|-*.
  - done.
  - rewrite /= delete_commute. f_equiv. apply IH.
Qed.

Lemma free_mem_block_dom (blk:block) n (sz:nat) h :
  (forall m : Z, is_Some (h !! (blk, n + m)) <-> 0 ≤ m < sz) ->
  set_map fst (dom (free_mem (blk, n) sz h)) = (set_map fst (dom h) ∖ {[blk]}:gset _).
Proof.
  intros Exact.
  induction sz as [|? IHsz] in n,h,Exact|-*.
  - rewrite difference_disjoint_L //.
    apply disjoint_singleton_r.
    intros ((blk' & l) & -> & Hin%elem_of_dom)%elem_of_map.
    specialize (Exact (l - n)).
    rewrite //= /shift_loc Zplus_minus in Exact.
    apply Exact in Hin. lia.
  - rewrite //= -free_mem_delete.
    rewrite IHsz.
    { rewrite dom_delete_L. apply gset_leibniz.
      intros k. split.
      - intros (((blk'&l) & -> & (Hin & Hnin2)%elem_of_difference)%elem_of_map & Hnin)%elem_of_difference.
        eapply elem_of_difference; split; last done.
        eapply elem_of_map. by eexists.
      - intros (((blk'&l) & -> & Hin)%elem_of_map & Hnin)%elem_of_difference.
        eapply elem_of_difference; split; last done.
        eapply elem_of_map. eexists; split; first done.
        eapply elem_of_difference. split; first done.
        intros [= -> ->]%elem_of_singleton. cbn in Hnin. set_solver. }
    intros m. destruct (Exact (1 + m)) as (HL & HR).
    rewrite //= /shift_loc //= in HL,HR,Exact|-*. split.
    + intros H. assert (m ≠ -1) as Hnneg.
      * intros ->. rewrite -Z.add_assoc Z.add_opp_diag_r Z.add_0_r lookup_delete in H.
        by apply is_Some_None in H.
      * rewrite Z.add_assoc in HL.
        rewrite lookup_delete_ne in H; first by apply HL in H; lia.
        intros [= HH]; lia.
    + intros H. rewrite lookup_delete_ne; last (intros [= HH]; lia).
      rewrite -Z.add_assoc. apply HR. lia.
Qed.

(** Dealloc *)
Lemma dealloc_step_wf σ σ' e e' l bor ptr efs :
  mem_expr_step σ.(shp) e (DeallocEvt l bor ptr) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (DeallocEvt l bor ptr)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq.
  inversion IS as [ | | | | |????? ACC | | ]; clear IS; simplify_eq.
  destruct (trees_deallocate_isSome _ _ _ _ _ _ (mk_is_Some _ _ ACC)) as [x [Lookup Update]].
  constructor; simpl.
  - rewrite /same_blocks dom_delete_L.
    rewrite free_mem_block_dom; [|auto].
    erewrite <- apply_within_trees_same_dom; [|eassumption].
    pose proof (WF.(state_wf_dom _)) as Same; simpl in Same.
    rewrite /same_blocks in Same.
    rewrite Same. done.
  - apply delete_trees_wf.
    eapply apply_within_trees_wf; first exact ACC.
    2: apply WF.
    eapply deallocate_preserve_tree_tag_count.
  - apply delete_trees_compat_nexts.
    eapply apply_within_trees_compat; first exact ACC.
    3: eapply WF. 1: done. all: simpl.
    intros ??. eapply memory_deallocate_compat_nexts.
  - intros blk tr' (Hin&Hne)%lookup_delete_Some.
    eapply apply_within_trees_lookup in ACC as (_&ACC).
    erewrite <- ACC in Hne; last done.
    eapply (state_wf_non_empty _ WF), Hne.
  - apply (WF.(state_wf_cid_agree _)).
Qed.

Lemma read_step_wf σ σ' e e' l bor ptr vl efs :
  mem_expr_step σ.(shp) e (CopyEvt l bor ptr vl) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (CopyEvt l bor ptr vl)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq.
  inversion IS as [ |?????? ACC| | | | | | ]; clear IS; simplify_eq.
  constructor; simpl.
  - rewrite /same_blocks.
    pose proof (WF.(state_wf_dom _)) as Same; simpl in Same.
    rewrite /same_blocks in Same. rewrite <- Same.
    rewrite (apply_within_trees_same_dom trs _ _ _ ACC).
    set_solver.
  - (* wf *)
    eapply apply_within_trees_wf.
    * exact ACC.
    * eapply memory_access_tag_count.
    * apply WF.
  - eapply apply_within_trees_compat.
    * exact ACC.
    * done.
    * intros ??. eapply memory_access_compat_nexts.
    * apply WF.
  - eapply apply_within_trees_compat_nonempty. 1: apply WF. 2: exact ACC.
    intros tr1 tr2. eapply preserve_tag_count_nonempty, memory_access_tag_count.
  - (* cids *) apply (WF.(state_wf_cid_agree _)).
Qed.

Lemma failed_copy_step_wf σ σ' e e' l bor T efs :
  mem_expr_step σ.(shp) e (FailedCopyEvt l bor T) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (FailedCopyEvt l bor T)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS; clear IS; simplify_eq.
  done.
Qed.

(* TODO less equalities makes applying the rule easier, see _sane version below *)
Lemma write_mem_dom l (vl : value) h h'
  (DEFINED: ∀ i : nat, (i < length vl)%nat → (l +ₗ i) ∈ dom h)
  (SUCCESS: write_mem l vl h = h') :
  dom h' = dom h.
Proof.
  revert l h h' DEFINED SUCCESS. induction vl as [|sc vl IH]; intros l h h' DEFINED SUCCESS.
  - simpl in *. subst. reflexivity.
  - simpl in *. rewrite <- SUCCESS.
    erewrite IH; [| |reflexivity].
    + rewrite dom_insert_lookup_L; first done.
      pose proof (DEFINED 0%nat) as Overwrite.
      rewrite shift_loc_0 in Overwrite.
      apply elem_of_dom.
      apply Overwrite.
      lia.
    + intros i Length.
      rewrite dom_insert.
      apply elem_of_union_r.
      rewrite shift_loc_assoc.
      replace (l +ₗ (1 + i)) with (l +ₗ (1 + i)%nat) by (unfold shift_loc; simpl; f_equal; lia).
      apply DEFINED.
      lia.
Qed.
Lemma write_mem_dom_sane l (vl : value) h
  (DEFINED: ∀ i : nat, (i < length vl)%nat → (l +ₗ i) ∈ dom h) :
  dom (write_mem l vl h) = dom h.
Proof.
  by eapply write_mem_dom.
Qed.

(* These two are not needed for write_step_wf but for other parts of the development *)

Lemma write_mem_lookup l vl h :
  (∀ (i: nat), (i < length vl)%nat → write_mem l vl h !! (l +ₗ i) = vl !! i) ∧
  (∀ (l': loc), (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) →
    write_mem l vl h !! l' = h !! l').
Proof.
  revert l h. induction vl as [|v vl IH]; move => l h; simpl;
    [split; [intros ?; by lia|done]|].
  destruct (IH (l +ₗ 1) (<[l:=v]> h)) as [IH1 IH2]. split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat /=. rewrite IH2; [by rewrite lookup_insert|].
      move => ? _.
      rewrite shift_loc_assoc -{1}(shift_loc_0 l) => /shift_loc_inj ?. by lia.
    + rewrite /= -IH1; [|lia].  by rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_insert_ne; [done|].
      move => ?. subst l'. apply (Lt O); [lia|by rewrite shift_loc_0_nat].
    + move => i Lti. rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
      apply Lt. by lia.
Qed.

Lemma write_mem_lookup_outside l vl h l' :
  ¬ (l'.1 = l.1 ∧ (l.2 ≤ l'.2 < l.2 + length vl)%Z) →
  write_mem l vl h !! l' = h !! l'.
Proof.
  destruct (write_mem_lookup l vl h) as (_&H).
  intros Hout. rewrite H //.
  intros i Hlt ->.
  apply Hout.
  split; first done.
  simpl. lia.
Qed.

Lemma write_mem_lookup_case l vl h l' :
  (∃ (i: nat), (i < length vl)%nat ∧ l' = l +ₗ i ∧ write_mem l vl h !! (l +ₗ i) = vl !! i)
  ∨ ((∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) ∧ write_mem l vl h !! l' = h !! l').
Proof.
  destruct (write_mem_lookup l vl h) as [EQ1 EQ2].
  case (decide (l'.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l'.2 < l.2 + length vl)) => [[Le Lt]|NIN]|].
  - have Eql2: l' = l +ₗ Z.of_nat (Z.to_nat (l'.2 - l.2)). {
      destruct l, l'. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    have Lt1: (Z.to_nat (l'.2 - l.2) < length vl)%nat
      by rewrite -(Nat2Z.id (length _)) -Z2Nat.inj_lt; lia.
    specialize (EQ1 _ Lt1).
    rewrite -Eql2 in EQ1. left.
    exists (Z.to_nat (l'.2 - l.2)). repeat split; [done..|by rewrite -Eql2].
  - right.
    have ?: (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i).
    { intros i Lt Eq3. apply NIN. rewrite Eq3 /=. lia. }
    split; [done|]. by apply EQ2.
  - right.
    have ?: (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i).
    { intros i Lt Eq3. apply NEql. by rewrite Eq3. }
    split; [done|]. by apply EQ2.
Qed.

Lemma write_step_wf σ σ' e e' l bor ptr vl efs :
  mem_expr_step σ.(shp) e (WriteEvt l bor ptr vl) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (WriteEvt l bor ptr vl)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq.
  inversion IS as [ | | |?????? ACC | | | | ]; clear IS; simplify_eq.
  constructor; simpl.
  - rewrite /same_blocks.
    pose proof (WF.(state_wf_dom _)) as Same; simpl in Same.
    rewrite /same_blocks in Same.
    erewrite write_mem_dom; [|eassumption|reflexivity].
    rewrite <- Same.
    rewrite (apply_within_trees_same_dom trs _ _ _ ACC).
    set_solver.
  - (* wf *)
    eapply apply_within_trees_wf.
    * exact ACC.
    * eapply memory_access_tag_count.
    * apply WF.
  - eapply apply_within_trees_compat.
    * exact ACC.
    * done.
    * intros ??. eapply memory_access_compat_nexts.
    * apply WF.
  - eapply apply_within_trees_compat_nonempty. 1: apply WF. 2: exact ACC.
    intros tr1 tr2. eapply preserve_tag_count_nonempty, memory_access_tag_count.
  - (* cids *) apply (WF.(state_wf_cid_agree _)).
Qed.


Lemma initcall_step_wf σ σ' e e' n efs :
  mem_expr_step σ.(shp) e (InitCallEvt n) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (InitCallEvt n)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [try apply WF..|].
  - eapply trees_compat_nexts_mono; [| |apply WF]; auto.
  - intros c. rewrite elem_of_union.
    move => [|/(state_wf_cid_agree _ WF)]; [intros ->%elem_of_singleton_1; by left|by right].
Qed.

(** EndCall *)
Lemma endcall_step_wf σ σ' e e' n efs :
  mem_expr_step σ.(shp) e (EndCallEvt n) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (EndCallEvt n)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [apply WF..|].
  - intros c IN. apply WF.
    apply elem_of_difference in IN. apply IN.
Qed.

(** Retag *)
Lemma insert_child_notfound tr (it:item) P Pdec :
  (every_node (λ x, ~P x) tr) →
  @insert_child_at _ tr it P Pdec = tr.
Proof.
  intros Hevery.
  induction tr as [|d tr1 IH1 tr2 IH2] in Hevery|-*; first done.
  simpl in Hevery|-*. destruct Hevery as (Hnd & Hn1 & Hn2).
  rewrite decide_False //.
  f_equal.
  - by eapply IH1.
  - by eapply IH2.
Qed.

Lemma insert_child_wf cids oldt nxtp pk rk cid nxtc tro trn
  (IT_WF : item_wf (create_new_item nxtp pk rk cid) (S nxtp) nxtc)
  : 
  create_child cids oldt nxtp pk rk cid tro = Some trn →
  tree_items_compat_nexts tro nxtp nxtc →
  wf_tree tro →
  tree_items_compat_nexts trn (S nxtp) nxtc ∧
  wf_tree trn.
Proof.
  intros CREATE Hcompat Hwf.
  destruct (decide (tree_contains oldt tro)) as [Hin|Hnin]; last first.
  { rewrite /create_child insert_child_notfound in CREATE.
    - injection CREATE as ->. split; last done.
      eapply tree_items_compat_nexts_mono; last exact Hcompat. all:lia.
    - by eapply every_not_eqv_not_exists. }
  split; last first.
  - intros tg Hcont%count_gt0_exists.
    destruct (decide (tg = nxtp)) as [->|].
    + eapply create_child_determined in CREATE as H2; try done.
      * destruct H2 as (_&H2).
        rewrite /create_child in CREATE. injection CREATE as <-.
        eapply inserted_unique. 1: done.
        -- intros H1. eapply tree_items_compat_next_not_containing; [exact H1|done|lia].
        -- by eapply (Hwf _ Hin).
      * intros ?. eapply tree_items_compat_next_not_containing. 1-2: done. lia.
    + erewrite <- create_child_preserves_count in Hcont; try done.
      eapply count_gt0_exists, Hwf in Hcont as Hunq.
      rewrite /tree_unique in Hunq.
      by erewrite create_child_preserves_count in Hunq.
  - injection CREATE as <-.
    eapply (insert_true_preserves_every tro).
    + apply IT_WF. 
    + eapply tree_items_compat_nexts_mono; last done; lia.
Qed.

Lemma retag_step_wf σ σ' e e' l ot nt pk rk cid efs :
  mem_expr_step σ.(shp) e (RetagEvt l ot nt pk cid rk) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (RetagEvt l ot nt pk cid rk)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS as [| | | |??????????? RETAG_EFFECT READ_ON_REBOR| | |]. clear IS. simplify_eq.
  assert (trees_compat_nexts trs' (S nt) nxtc' ∧ wf_trees trs') as (Hwf1 & Hwf2).
  { eapply apply_within_trees_compat_both; first done.
    1: done. 3: eapply apply_within_trees_compat_both; first done; last first.
    - intros ?????; split; first by eapply memory_access_compat_nexts.
      by eapply memory_access_wf.
    - intros ???? ?%count_gt0_exists. left. eapply count_gt0_exists.
      by erewrite memory_access_tag_count.
    - split; by eapply WF.
    - simpl. intros tr tr' tg Hcr Hcont.
      destruct (decide (tg = nt)) as [->|Hne].
      1: right; lia.
      1: left; eapply insertion_minimal_tags; last done; try done.
    - simpl. intros ?????.
      eapply insert_child_wf; try done.
      split; rewrite /create_new_item /=.
      + rewrite /=. intros ? <-; lia.
      + destruct rk; last done.
        rewrite /= /protector_is_for_call /=.
        intros ? [= <-]. by eapply WF.
    - simpl. intros ??. eapply tree_items_compat_nexts_mono; last done; lia. }
  constructor; simpl.
  - rewrite /same_blocks /=
            -(apply_within_trees_same_dom _ _ _ _ READ_ON_REBOR)
            -(apply_within_trees_same_dom _ _ _ _ RETAG_EFFECT).
    apply WF.
  - done.
  - done.
  - eapply apply_within_trees_compat_nonempty; last done.
    1: eapply apply_within_trees_compat_nonempty; last done.
    1: apply WF.
    + intros ????; by eapply create_child_preserve_nonempty.
    + intros ????. eapply preserve_tag_count_nonempty; try done.
      eapply memory_access_tag_count.
  - apply WF.
Qed.

Lemma base_step_wf P σ σ' e e' efs :
  base_step P e σ e' σ' efs → state_wf σ → state_wf σ'.
Proof.
  intros HS WF. inversion HS; [by subst|]. simplify_eq.
  rename select event into ev. destruct ev.
  - eapply alloc_step_wf; eauto.
  - eapply dealloc_step_wf; eauto.
  - eapply read_step_wf; eauto.
  - eapply failed_copy_step_wf; eauto.
  - eapply write_step_wf; eauto.
  - eapply initcall_step_wf; eauto.
  - eapply endcall_step_wf; eauto.
  - eapply retag_step_wf; eauto.
  - rename select (mem_expr_step _ _ _ _ _ _) into Hstep. inversion Hstep.
Qed.
