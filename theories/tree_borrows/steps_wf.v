(** This file has been adapted from the Stacked Borrows development, available at 
https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.tree_borrows Require Import helpers.
From simuliris.tree_borrows Require Export defs steps_foreach steps_access steps_preserve bor_lemmas.
From iris.prelude Require Import options.

Lemma wf_init_state : state_wf init_state.
Proof.
  constructor; simpl; try intros ?; set_solver.
Qed.

(** Steps preserve wellformedness *)

Lemma wf_item_fresh_mono it :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (wf_item_fresh it).
Proof.
  move=> ?? Le1 ?? Le2 [WFle WFprot].
  split.
  - intros tg tgit. specialize (WFle tg tgit). lia.
  - intros cid protit. specialize (WFprot cid protit). lia.
Qed.

Lemma wf_tree_fresh_mono tr :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (wf_tree_fresh tr).
Proof.
  move=> ?? Le1 ? ? Le2 WF.
  eapply every_node_increasing; first eassumption.
  rewrite every_node_eqv_universal; move=> ? ?.
  apply wf_item_fresh_mono; assumption.
Qed.

Lemma wf_trees_fresh_mono trs :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (wf_trees_fresh trs).
Proof.
  move=> ?? Le1 ? ? Le2 WF ?? /WF Hf.
  eapply wf_tree_fresh_mono; eassumption.
Qed.

Lemma wf_mem_tag_mono h :
  Proper ((≤)%nat ==> impl) (wf_mem_tag h).
Proof.
  move => ??? WF ?? tg Access.
  specialize (WF _ _ tg Access); simpl in WF.
  lia.
Qed.

Definition preserve_wf_tree_fresh (fn:app (tree item)) nxtp nxtp' nxtc nxtc' :=
  forall tr tr',
    wf_tree_nodup tr ->
    wf_tree_fresh tr nxtp nxtc ->
    fn tr = Some tr' ->
    wf_tree_fresh tr' nxtp' nxtc'.

Definition preserve_wf_tree_nodup (fn:app (tree item)) Precond :=
  forall tr tr',
    Precond tr ->
    wf_tree_nodup tr ->
    fn tr = Some tr' ->
    wf_tree_nodup tr'.

Definition preserve_tree_nonempty (fn:app (tree item)) :=
  forall tr tr', ~tr = empty -> fn tr = Some tr' -> ~tr' = empty.

(* Any function that operates only on permissions (which is all transitions steps)
   leaves the tag and protector unchanged which means that most of the preservation lemmas
   are trivial once we get to the level of items *)
Definition preserve_item_metadata (fn:app item) :=
  forall it it', fn it = Some it' -> it.(iprot) = it'.(iprot) /\ it.(initp) = it'.(initp) /\ it.(itag) = it'.(itag).

(* Since there are a lot of layers to the model (trees -> tree -> item -> perms)
   that we mostly don't really need to reason about (e.g. tree_item_included is per-item
   and we don't need tree-wide reasoning) we start with some lemmas to turn the per-trees
   wf preservation to per-item wf preservation *)

Lemma apply_within_trees_wf_nodup trs trs' blk fn Precond :
  apply_within_trees fn blk trs = Some trs' ->
  trees_at_block Precond trs blk ->
  preserve_wf_tree_nodup fn Precond ->
  wf_trees_nodup trs -> wf_trees_nodup trs'.
Proof.
  intros App Pre WFfn WF.
  unfold apply_within_trees in App; destruct (trs !! blk) as [t|] eqn:Lookup; inversion App as [App0]; clear App.
  destruct (fn t) eqn:Map; inversion App0 as [E]; clear App0.
  intro blk'; destruct (decide (blk = blk')); intros tr Lookup'.
  all: inversion E; simplify_eq.
  (* Handle the insertion/deletion *)
  1: rewrite lookup_insert in Lookup'.
  2: rewrite lookup_insert_ne in Lookup'; [|done].
  all: simplify_eq.
  (* WF impl *)
  - apply (WFfn t).
    + rewrite /trees_contain /trees_at_block Lookup in Pre. assumption.
    + apply (WF _ _ Lookup).
    + done.
  - apply (WF blk' _ Lookup').
Qed.

Lemma apply_within_trees_wf_fresh trs trs' nxtp nxtp' nxtc nxtc' blk fn:
  apply_within_trees fn blk trs = Some trs' ->
  (forall tr, wf_tree_fresh tr nxtp nxtc -> wf_tree_fresh tr nxtp' nxtc') ->
  preserve_wf_tree_fresh fn nxtp nxtp' nxtc nxtc' ->
  wf_trees_nodup trs ->
  wf_trees_fresh trs nxtp nxtc -> wf_trees_fresh trs' nxtp' nxtc'.
Proof.
  intros App WFtrans WFfn Nodup WF.
  unfold apply_within_trees in App; destruct (trs !! blk) as [t|] eqn:Lookup; inversion App as [App0]; clear App.
  destruct (fn t) eqn:Map; inversion App0 as [E]; clear App0.
  intro blk'; destruct (decide (blk = blk')); intros tr Lookup'.
  all: inversion E; simplify_eq.
  (* Handle the insertion/deletion *)
  1: rewrite lookup_insert in Lookup'.
  2: rewrite lookup_insert_ne in Lookup'; [|done].
  all: simplify_eq.
  (* WF impl *)
  - apply (WFfn t).
    + apply (Nodup blk' _ Lookup).
    + apply (WF blk' _ Lookup).
    + done.
  - apply (WFtrans tr); apply (WF blk' _ Lookup').
Qed.

Lemma apply_within_trees_preserve_nonempty trs trs' blk fn :
  wf_non_empty trs ->
  preserve_tree_nonempty fn ->
  apply_within_trees fn blk trs = Some trs' ->
  wf_non_empty trs'.
Proof.
  intros WF Preserve ApplySome blk' tr'' Lookup.
  destruct (apply_within_trees_lookup _ _ _ _ ApplySome) as [LookupEq LookupNeq].
  destruct (decide (blk' = blk)).
  - subst.
    destruct LookupEq as [tr [tr' [Eqtr [Eqtr' Eqtrfn]]]].
    rewrite Eqtr' in Lookup; injection Lookup; intro; subst.
    apply (Preserve tr tr'').
    * apply (WF blk).
      unfold apply_within_trees in ApplySome.
      exact Eqtr.
    * auto.
  - apply (WF blk').
    rewrite LookupNeq; [auto|lia].
Qed.

Lemma delete_trees_preserve_nonempty trs blk :
  wf_non_empty trs ->
  wf_non_empty (delete blk trs).
Proof.
  intros WF blk' tr Delete.
  eapply WF.
  apply (proj1 (lookup_delete_Some _ _ _ _) Delete).
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

Lemma extend_trees_wf_nodup trs tr blk :
  wf_trees_nodup trs ->
  wf_tree_nodup tr ->
  wf_trees_nodup (<[blk := tr]> trs).
Proof.
  intros WFs WF.
  intros blk' tr'.
  destruct (decide (blk = blk')).
  - simplify_eq; rewrite lookup_insert; intro H; injection H; intro; subst; done.
  - rewrite lookup_insert_ne; [|done]; apply (WFs blk').
Qed.

Lemma extend_trees_wf_fresh trs tr blk nxtp nxtc :
  wf_trees_fresh trs nxtp nxtc ->
  wf_tree_fresh tr nxtp nxtc ->
  wf_trees_fresh (<[blk := tr]> trs) nxtp nxtc.
Proof.
  intros WFs WF.
  intros blk' tr'.
  destruct (decide (blk = blk')).
  - simplify_eq; rewrite lookup_insert; intro H; injection H; intro; subst; done.
  - rewrite lookup_insert_ne; [|done]; apply (WFs blk').
Qed.

Lemma delete_trees_wf_nodup trs blk :
  wf_trees_nodup trs ->
  wf_trees_nodup (delete blk trs).
Proof.
  intros WFs blk'.
  intros tr' Delete.
  intros.
  eapply WFs.
  apply (proj1 (lookup_delete_Some _ _ _ _) Delete).
Qed.

Lemma delete_trees_wf_fresh trs blk nxtp nxtc :
  wf_trees_fresh trs nxtp nxtc ->
  wf_trees_fresh (delete blk trs) nxtp nxtc.
Proof.
  intros WFs blk'.
  intros tr' Delete.
  intros.
  eapply WFs.
  apply (proj1 (lookup_delete_Some _ _ _ _) Delete).
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

Lemma joinmap_preserve_nonempty fn :
  preserve_tree_nonempty (fun tr => join_nodes (map_nodes fn tr)).
Proof.
  intro tr; induction tr as [|data ????]; intros tr' Nonempty JoinMap; [contradiction|].
  simpl in JoinMap.
  destruct (fn data); [|inversion JoinMap]; simpl in *.
  destruct (join_nodes _); [|inversion JoinMap]; simpl in *.
  destruct (join_nodes _); [|inversion JoinMap]; simpl in *.
  injection JoinMap; intro; subst.
  intro H; inversion H.
Qed.

Lemma deallocate_preserve_nonempty cids tg range :
  preserve_tree_nonempty (memory_deallocate cids tg range).
Proof.
  intros tr tr' Nonempty Dealloc.
  rewrite /memory_deallocate /memory_access_nonchildren_only in Dealloc.
  remember (tree_apply_access (nonchildren_only _) _ _ _ _) as tr''.
  destruct tr''; simpl in Dealloc; [|discriminate].
  eapply joinmap_preserve_nonempty.
  2: exact Dealloc.
  eapply joinmap_preserve_nonempty.
  1: exact Nonempty.
  symmetry; eassumption.
Qed.

Lemma memory_access_preserve_nonempty kind cids tg range :
  preserve_tree_nonempty (memory_access kind cids tg range).
Proof.
  intros tr tr' Nonempty Read.
  eapply joinmap_preserve_nonempty.
  1: exact Nonempty.
  apply Read.
Qed.

Lemma create_child_preserve_nonempty cids oldtg newtg pk rk cid :
  preserve_tree_nonempty (create_child cids oldtg newtg pk rk cid).
Proof.
  intros tr tr' Nonempty Create.
  unfold create_child in Create.
  injection Create; intros; subst; clear Create.
  (* No need to do an induction, we can prove it's nonempty with just the root *)
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
  revert tr'.
  induction tr as [|data ? IHtr1 ? IHtr2]; intros tr' Access.
  - inversion Access; subst. reflexivity.
  - rewrite /tree_apply_access in Access.
    destruct (option_bind_success_step _ _ _ Access) as [data' [data'Spec Access']].
    destruct (option_bind_success_step _ _ _ Access') as [tr1' [tr1'Spec Access'']].
    destruct (option_bind_success_step _ _ _ Access'') as [tr2' [tr2'Spec Access''']].
    injection Access'''; intros; subst.
    simpl.
    erewrite IHtr1; [|apply tr1'Spec].
    erewrite IHtr2; [|apply tr2'Spec].
    assert (has_tag tg data = has_tag tg data') as SameTg. {
      rewrite /has_tag /IsTag.
      destruct (item_apply_access_preserves_metadata data'Spec) as [EqTg _].
      simpl in *.
      destruct (decide (itag data = tg)), (decide (itag data' = tg)).
      all: repeat (rewrite bool_decide_eq_true_2; [|easy]).
      all: repeat (rewrite bool_decide_eq_false_2; [|easy]).
      all: try reflexivity.
      all: congruence.
    }
    rewrite SameTg.
    reflexivity.
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

Lemma exists_with_tag
  {it tr}
  : exists_node (eq it) tr ->
  tree_contains (itag it) tr.
Proof.
  intro Ex.
  eapply exists_node_increasing; first eassumption.
  rewrite every_node_eqv_universal; intros ? _ ?; subst.
  rewrite /IsTag //=.
Qed.

Lemma determined_contains_exists_equal
  {tr it tg} :
  itag it = tg ->
  tree_contains tg tr ->
  tree_item_determined tg it tr ->
  exists_node (eq it) tr.
Proof.
  intros Tg Ex Det.
  rewrite /tree_item_determined in Det.
  rewrite every_node_eqv_universal in Det.
  eapply exists_node_increasing; first eassumption.
  rewrite every_node_eqv_universal; intros it0 Exit0 Tg0.
  symmetry; apply Det; done.
Qed.

Lemma unique_exists_determined
  {tr it tg} :
  IsTag tg it ->
  tree_unique tg tr ->
  exists_node (eq it) tr ->
  tree_item_determined tg it tr.
Proof.
  intros Tg Unq Eq.
  rewrite /tree_item_determined.
  rewrite every_node_eqv_universal.
  intros it' Eq' Tg'.
  destruct (unique_lookup _ _ Unq) as [it0 Det0].
  rewrite /tree_item_determined every_node_eqv_universal in Det0.
  rewrite (Det0 _ Eq); last assumption.
  rewrite (Det0 _ Eq'); last assumption.
  reflexivity.
Qed.

Lemma tree_apply_access_wf_nodup fn tr tr' cids tg range :
  wf_tree_nodup tr ->
  tree_apply_access fn cids tg range tr = Some tr' ->
  wf_tree_nodup tr'.
Proof.
  intros WF Access.
  intros tg0 Ex0'.
  specialize (WF tg0).
  rewrite /tree_unique.
  erewrite <-tree_apply_access_same_count; last eassumption.
  apply WF. apply count_gt0_exists.
  erewrite tree_apply_access_same_count; last eassumption.
  apply count_gt0_exists.
  assumption.
Qed.

Lemma tree_apply_access_wf_fresh fn tr tr' cids tg range nxtp nxtc :
  wf_tree_nodup tr ->
  wf_tree_fresh tr nxtp nxtc ->
  tree_apply_access fn cids tg range tr = Some tr' ->
  wf_tree_fresh tr' nxtp nxtc.
Proof.
  rewrite /wf_tree_fresh.
  do 2 rewrite every_node_eqv_universal.
  intros Nodup WF Access.
  pose proof (tree_apply_access_wf_nodup _ _ _ _ _ _ Nodup Access) as Nodup'.
  intros it' ExEq'.
  pose proof (exists_with_tag ExEq') as Ex'.
  pose proof (proj2 (access_preserves_tags Access) Ex') as Ex.
  pose proof (Nodup _ Ex) as Unq.
  destruct (unique_lookup _ _ Unq) as [it Det].
  assert (exists_node (eq it) tr) as Exit. {
    eapply determined_contains_exists_equal; [|eassumption|eassumption].
    eapply tree_determined_specifies_tag; eassumption.
  }
  pose proof (WF it Exit) as Freshit.
  destruct (apply_access_spec_per_node Ex Det Access) as [post [PostSpec [_ Unqpost]]].
  assert (post = it'). {
    eapply tree_determined_unify.
    - apply Ex'.
    - apply Unqpost.
    - eapply unique_exists_determined.
      + rewrite /IsTag //=.
      + apply Nodup'. assumption.
      + assumption.
  }
  subst.
  symmetry in PostSpec.
  destruct (item_apply_access_preserves_metadata PostSpec) as [Same1 [Same2 _]].
  rewrite /wf_item_fresh /IsTag /protector_is_for_call. rewrite <- Same1, <- Same2.
  auto.
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

Lemma memory_deallocate_wf_nodup tr tr' cids tg range :
  wf_tree_nodup tr ->
  memory_deallocate cids tg range tr = Some tr' ->
  wf_tree_nodup tr'.
Proof.
  intros Nodup Dealloc.
  rewrite /memory_deallocate /memory_access_nonchildren_only in Dealloc.
  remember (tree_apply_access _ _ _ _ _) as tr''.
  destruct tr'' as [tr''|]; simpl in Dealloc; [|discriminate].
  assert (wf_tree_nodup tr'') as WF''. {
    apply (tree_apply_access_wf_nodup _ _ _ _ _ _ Nodup ltac:(symmetry; eassumption)).
  }
  erewrite <- (join_map_id_is_Some_identical _ tr'' tr').
  - assumption.
  - exact Dealloc.
Qed.

Lemma memory_deallocate_wf_fresh tr tr' cids tg range nxtp nxtc :
  wf_tree_nodup tr ->
  wf_tree_fresh tr nxtp nxtc ->
  memory_deallocate cids tg range tr = Some tr' ->
  wf_tree_fresh tr' nxtp nxtc.
Proof.
  intros Nodup WF Dealloc.
  rewrite /memory_deallocate /memory_access_nonchildren_only in Dealloc.
  remember (tree_apply_access _ _ _ _ _) as tr''.
  destruct tr'' as [tr''|]; simpl in Dealloc; [|discriminate].
  assert (wf_tree_fresh tr'' nxtp nxtc) as WF''. {
    apply (tree_apply_access_wf_fresh _ _ _ _ _ _ _ _ Nodup WF ltac:(symmetry; eassumption)).
  }
  erewrite <- (join_map_id_is_Some_identical _ tr'' tr').
  - assumption.
  - exact Dealloc.
Qed.

Lemma memory_read_wf_nodup tr tr' cids tg range :
  wf_tree_nodup tr ->
  memory_access AccessRead cids tg range tr = Some tr' ->
  wf_tree_nodup tr'.
Proof.
  intros.
  eapply tree_apply_access_wf_nodup; eassumption.
Qed.

Lemma memory_read_wf_fresh tr tr' cids tg range nxtp nxtc :
  wf_tree_nodup tr ->
  wf_tree_fresh tr nxtp nxtc ->
  memory_access AccessRead cids tg range tr = Some tr' ->
  wf_tree_fresh tr' nxtp nxtc.
Proof.
  intros.
  eapply tree_apply_access_wf_fresh; eassumption.
Qed.

Lemma memory_write_wf_nodup tr tr' cids tg range :
  wf_tree_nodup tr ->
  memory_access AccessWrite cids tg range tr = Some tr' ->
  wf_tree_nodup tr'.
Proof.
  intros.
  eapply tree_apply_access_wf_nodup; eassumption.
Qed.

Lemma memory_write_wf_fresh tr tr' cids tg range nxtp nxtc :
  wf_tree_nodup tr ->
  wf_tree_fresh tr nxtp nxtc ->
  memory_access AccessWrite cids tg range tr = Some tr' ->
  wf_tree_fresh tr' nxtp nxtc.
Proof.
  intros.
  eapply tree_apply_access_wf_fresh; eassumption.
Qed.

Lemma memory_access_wf_nodup tr tr' acc cids tg range :
  wf_tree_nodup tr ->
  memory_access acc cids tg range tr = Some tr' ->
  wf_tree_nodup tr'.
Proof.
  destruct acc.
  - eapply memory_read_wf_nodup.
  - eapply memory_write_wf_nodup.
Qed.

Lemma memory_access_wf tr tr' acc cids tg range nxtp nxtc :
  wf_tree_nodup tr ->
  wf_tree_fresh tr nxtp nxtc ->
  memory_access acc cids tg range tr = Some tr' ->
  wf_tree_fresh tr' nxtp nxtc.
Proof.
  destruct acc.
  - eapply memory_read_wf_fresh.
  - eapply memory_write_wf_fresh.
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

Lemma init_tree_wf_nodup t :
  wf_tree_nodup (init_tree t).
Proof.
  rewrite /init_tree.
  intro t'. rewrite /= /IsTag /=.
  intros [e|[|]]; try contradiction; subst.
  rewrite /tree_unique /= /has_tag /IsTag /=.
  rewrite bool_decide_eq_true_2; lia.
Qed.

Lemma init_tree_wf_fresh c t t' :
  (t' < t)%nat ->
  wf_tree_fresh (init_tree t') t c.
Proof.
  intro Le.
  unfold wf_tree_fresh. rewrite every_node_eqv_universal.
  intros it Ex. inversion Ex as [isTag|[Contra|Contra]].
  2,3: inversion Contra.
  simpl in isTag.
  subst.
  rewrite /wf_item_fresh /IsTag /protector_is_for_call /=.
  split; intros; try discriminate; subst; auto.
Qed.

Lemma init_tree_nonempty t :
  forall tr, tr = (init_tree t) -> tr ≠ empty.
Proof.
  intros. subst.
  rewrite /init_tree //.
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
  - apply extend_trees_wf_fresh.
    * eapply wf_trees_fresh_mono.
      3: apply WF.
      all: simpl; lia.
    * apply init_tree_wf_fresh.
      lia.
  - apply extend_trees_wf_nodup.
    * apply WF.
    * apply init_tree_wf_nodup.
  - intros blk.
    destruct (decide (blk = fresh_block h)).
    * simplify_eq.
      intros tr IsSome.
      eapply init_tree_nonempty.
      rewrite /extend_trees in IsSome.
      rewrite lookup_insert in IsSome.
      injection IsSome.
      eauto.
    * intros tr.
      rewrite /extend_trees.
      rewrite lookup_insert_ne.
      + apply WF.(state_wf_non_empty _).
      + congruence.
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

Lemma wf_fresh_not_contains
  {trs nxtp nxtc tg blk} :
  wf_trees_fresh trs nxtp nxtc ->
  (tg >= nxtp)%nat ->
  ~trees_contain tg trs blk.
Proof.
  intros WF Ge Ex.
  rewrite /trees_contain /trees_at_block in Ex.
  destruct (trs !! blk) as [tr|] eqn:Lookup; last contradiction.
  pose proof (WF blk tr Lookup) as Fresh.
  rewrite /wf_tree_fresh every_node_eqv_universal in Fresh.
  rewrite /tree_contains exists_node_eqv_existential in Ex.
  destruct Ex as [it [Exit Tgit]].
  specialize (Fresh it Exit).
  destruct Fresh as [Freshtg _].
  rewrite /wf_item_fresh in Freshtg.
  specialize (Freshtg tg Tgit).
  lia.
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
  - apply delete_trees_wf_fresh.
    apply (apply_within_trees_wf_fresh _ _ nxtp' nxtp' nxtc' nxtc' _ _ ACC).
    * tauto.
    * intros tr tr'. apply memory_deallocate_wf_fresh.
    * apply (WF.(state_wf_tree_nodup _)).
    * apply (WF.(state_wf_tree_fresh _)).
  - apply delete_trees_wf_nodup.
    apply (apply_within_trees_wf_nodup _ _ _ _ (fun it => True) ACC).
    * rewrite /trees_at_block Lookup //=.
    * intros nEx tr tr'. apply memory_deallocate_wf_nodup.
    * apply (WF.(state_wf_tree_nodup _)).
  - apply delete_trees_preserve_nonempty.
    apply (apply_within_trees_preserve_nonempty _ _ _ _ (WF.(state_wf_non_empty _)) (deallocate_preserve_nonempty _ _ _) ACC).
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
    apply (apply_within_trees_wf_fresh _ _ nxtp' nxtp' nxtc' nxtc' _ _ ACC).
    * tauto.
    * intros tr tr'. apply memory_read_wf_fresh.
    * apply (WF.(state_wf_tree_nodup _)).
    * apply (WF.(state_wf_tree_fresh _)).
  - (* nodup *)
    apply (apply_within_trees_wf_nodup _ _ _ _ (fun _ => True) ACC).
    * rewrite /trees_at_block. rewrite /apply_within_trees in ACC.
      destruct (trs !! l); [tauto|discriminate].
    * intros nEx tr tr'. apply memory_read_wf_nodup.
    * apply (WF.(state_wf_tree_nodup _)).
  - (* nonempty *)
    apply (apply_within_trees_preserve_nonempty _ _ _ _ (WF.(state_wf_non_empty _)) (memory_access_preserve_nonempty _ _ _ _) ACC).
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

(* TODO make it sane *)
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
    apply (apply_within_trees_wf_fresh _ _ nxtp' nxtp' nxtc' nxtc' _ _ ACC).
    * tauto.
    * intros tr tr'. apply memory_write_wf_fresh.
    * apply (WF.(state_wf_tree_nodup _)).
    * apply (WF.(state_wf_tree_fresh _)).
  - (* nodup *)
    apply (apply_within_trees_wf_nodup _ _ _ _ (fun _ => True) ACC).
    * rewrite /trees_at_block. rewrite /apply_within_trees in ACC.
      destruct (trs !! l); [tauto|discriminate].
    * intros nEx tr tr'. apply memory_write_wf_nodup.
    * apply (WF.(state_wf_tree_nodup _)).
  - (* nonempty *)
    apply (apply_within_trees_preserve_nonempty _ _ _ _ (WF.(state_wf_non_empty _)) (memory_access_preserve_nonempty _ _ _ _) ACC).
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
  - eapply wf_trees_fresh_mono; [| |apply WF]; auto.
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

Lemma insert_child_wf_fresh cids oldt nxtp pk rk cid nxtc
  (IT_WF : wf_item_fresh (create_new_item nxtp pk rk cid) (S nxtp) nxtc)
  : preserve_wf_tree_fresh (create_child cids oldt nxtp pk rk cid) nxtp (S nxtp) nxtc nxtc.
Proof.
  intros tr tr' Nodup WF CREATE.
  rewrite /wf_tree_fresh.
  inversion CREATE.
  rewrite <- insert_true_preserves_every.
  - eapply wf_tree_fresh_mono; last apply WF; lia.
  - assumption.
Qed.

Lemma insert_child_wf_nodup cids oldt nxtp pk rk cid :
  preserve_wf_tree_nodup (create_child cids oldt nxtp pk rk cid)
    (fun tr => ~tree_contains nxtp tr /\ tree_unique oldt tr).
Proof.
  intros tr tr' [nEx Exp] WF Create.
  injection Create; intros; subst; clear Create.
  intros tg Ex.
  destruct (decide (tg = nxtp)).
  + subst.
    apply inserted_unique.
    * apply new_item_has_tag.
    * assumption.
    * assumption.
  + rewrite /tree_unique.
    rewrite <- (create_child_preserves_count tg tr _ nxtp cids oldt pk rk cid);
      last reflexivity; try eassumption.
    enough (tree_contains tg tr) by (apply WF; done).
    rewrite <-count_gt0_exists.
    erewrite (create_child_preserves_count tg tr _ nxtp cids oldt pk rk cid);
      last reflexivity; last eassumption; try eassumption.
    rewrite count_gt0_exists.
    eassumption.
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
  constructor; simpl.
  - rewrite /same_blocks /=.
    (* Something is bodged here *)
    setoid_rewrite <- (apply_within_trees_same_dom _ _ _ _ READ_ON_REBOR).
    setoid_rewrite <- (apply_within_trees_same_dom _ _ _ _ RETAG_EFFECT).
    apply WF.
  - apply (apply_within_trees_wf_fresh _ _ (S nt) (S nt) nxtc' nxtc' _ _ READ_ON_REBOR).
    * intros tr WFtr. eapply wf_tree_fresh_mono; [| |eassumption]; auto.
    * intros tr tr'.
      intros WFold Access. eapply memory_read_wf_fresh; eassumption.
    * eapply apply_within_trees_wf_nodup; [eassumption| |eapply insert_child_wf_nodup|apply WF].
      unfold trees_contain, trees_at_block in *.
      destruct (trs !! l) eqn:Lookup; last tauto.
      split; first assumption.
      apply (WF.(state_wf_tree_nodup _) l _ Lookup); assumption.
    * apply (apply_within_trees_wf_fresh _ _ nt (S nt) nxtc' nxtc' _ _ RETAG_EFFECT).
      + intros tr WFtr. eapply wf_tree_fresh_mono; [| |eassumption]; auto.
      + intros tr tr'.
        intros WFold Access. eapply insert_child_wf_fresh; [|eassumption|eassumption].
        rewrite /wf_item_fresh /create_new_item /IsTag /protector_is_for_call /call_of_protector /=.
        rewrite /retag_kind_to_prot /pointer_kind_to_strength.
        split; first lia.
        intro.
        destruct rk; simpl; last discriminate.
        intro H; injection H; intros; subst.
        apply WF. simpl. assumption.
      + apply WF.
      + apply WF.
  - eapply (apply_within_trees_wf_nodup _ _ _ _ (fun _ => True)).
    + eassumption.
    + rewrite /trees_at_block. rewrite /apply_within_trees in READ_ON_REBOR.
      destruct (_ !! l); [tauto|discriminate].
    + intros nEx tr tr'. apply memory_read_wf_nodup.
    + eapply apply_within_trees_wf_nodup; [| |eapply insert_child_wf_nodup|].
      * eassumption.
      * unfold trees_contain, apply_within_trees, trees_at_block in *.
        destruct (trs !! l) eqn:Lookup; [simpl in *| discriminate].
        split; [assumption|].
        apply (WF.(state_wf_tree_nodup _) _ _ Lookup). eassumption.
      * apply WF.
  - unshelve eapply (apply_within_trees_preserve_nonempty _ _ _ _ _ (memory_access_preserve_nonempty _ _ _ _) READ_ON_REBOR).
    unshelve eapply (apply_within_trees_preserve_nonempty _ _ _ _ _ (create_child_preserve_nonempty _ _ _ _ _ _) RETAG_EFFECT).
    apply WF.
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
