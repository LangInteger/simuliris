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

Lemma wf_item_mono it :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (item_wf it).
Proof.
  move=> ?? Le1 ?? Le2 [WFle WFprot].
  split.
  - intros tg tgit. specialize (WFle tg tgit). lia.
  - intros cid protit. specialize (WFprot cid protit). lia.
Qed.

Lemma wf_tree_mono tr :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (wf_tree tr).
Proof.
  move=> ?? Le1 ? ? Le2 WF ? Ex.
  destruct (WF _ Ex) as [it [Uniqueit [Detit WFit]]].
  exists it; split; [|split].
  - assumption.
  - assumption.
  - eapply wf_item_mono; eauto.
Qed.

Lemma wf_trees_mono trs :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (wf_trees trs).
Proof.
  move=> ?? Le1 ? ? Le2 WF ?? /WF Hf.
  eapply wf_tree_mono; eassumption.
Qed.

Lemma wf_mem_tag_mono h :
  Proper ((≤)%nat ==> impl) (wf_mem_tag h).
Proof.
  move => ??? WF ?? tg Access.
  specialize (WF _ _ tg Access); simpl in WF.
  lia.
Qed.

Definition preserve_tree_wf (fn:app (tree item)) nxtp nxtp' nxtc nxtc' :=
  forall tr tr', wf_tree tr nxtp nxtc -> fn tr = Some tr' -> wf_tree tr' nxtp' nxtc'.

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

Lemma apply_within_trees_wf trs trs' nxtp nxtp' nxtc nxtc' blk fn:
  apply_within_trees fn blk trs = Some trs' ->
  (forall tr, wf_tree tr nxtp nxtc -> wf_tree tr nxtp' nxtc') ->
  preserve_tree_wf fn nxtp nxtp' nxtc nxtc' ->
  wf_trees trs nxtp nxtc -> wf_trees trs' nxtp' nxtc'.
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

Lemma extend_trees_wf trs tr blk nxtp nxtc :
  wf_trees trs nxtp nxtc ->
  wf_tree tr nxtp nxtc ->
  wf_trees (<[blk := tr]> trs) nxtp nxtc.
Proof.
  intros WFs WF.
  intros blk' tr'.
  destruct (decide (blk = blk')).
  - simplify_eq; rewrite lookup_insert; intro H; injection H; intro; subst; done.
  - rewrite lookup_insert_ne; [|done]; apply (WFs blk').
Qed.

Lemma delete_trees_wf trs blk nxtp nxtc :
  wf_trees trs nxtp nxtc ->
  wf_trees (delete blk trs) nxtp nxtc.
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

Lemma create_child_preserve_nonempty cids oldtg newtg newp :
  preserve_tree_nonempty (create_child cids oldtg newtg newp).
Proof.
  intros tr tr' Nonempty Create.
  unfold create_child in Create.
  injection Create; intros; subst; clear Create.
  (* No need to do an induction, we can prove it's nonempty with just the root *)
  destruct tr as [|data].
  1: contradiction.
  simpl. destruct (decide (IsTag oldtg data)); intro H; inversion H.
Qed.

Lemma tree_apply_access_preserve_unique
  {tr tr' tg fn cids acc_tg range} :
  tree_apply_access fn cids acc_tg range tr = Some tr' ->
  tree_unique tg tr <-> tree_unique tg tr'.
Proof.
Admitted.

Lemma tree_apply_access_wf fn tr tr' cids tg range nxtp nxtc :
  wf_tree tr nxtp nxtc ->
  tree_apply_access fn cids tg range tr = Some tr' ->
  wf_tree tr' nxtp nxtc.
Proof.
  rewrite /wf_tree /tree_item_included.
  intros WF Access.
  intros tg' Ex'.
  pose proof (proj2 (access_preserves_tags Access) Ex') as Ex.
  destruct (WF tg' Ex) as  [it [Unqit [Detit Wfit]]].
  destruct (apply_access_spec_per_node Ex Detit Access) as [post [PostSpec [_ Unqpost]]].
  exists post; split; [|split].
  - rewrite -tree_apply_access_preserve_unique.
    + exact Unqit.
    + apply Access.
  - assumption.
  - rewrite /item_wf in Wfit |- *.
    symmetry in PostSpec.
    destruct (item_apply_access_preserves_metadata PostSpec) as [Same1 Same2].
    simpl. rewrite /IsTag /protector_is_for_call. rewrite <- Same1, <- Same2.
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

Lemma memory_deallocate_wf tr tr' cids tg range nxtp nxtc :
  wf_tree tr nxtp nxtc ->
  memory_deallocate cids tg range tr = Some tr' ->
  wf_tree tr' nxtp nxtc.
Proof.
  intros WF Dealloc.
  rewrite /memory_deallocate /memory_access_nonchildren_only in Dealloc.
  remember (tree_apply_access _ _ _ _ _) as tr''.
  destruct tr'' as [tr''|]; simpl in Dealloc; [|discriminate].
  assert (wf_tree tr'' nxtp nxtc) as WF''. {
    apply (tree_apply_access_wf _ _ _ _ _ _ _ _ WF ltac:(symmetry; eassumption)).
  }
  erewrite <- (join_map_id_is_Some_identical _ tr'' tr').
  - assumption.
  - exact Dealloc.
Qed.

Lemma memory_read_wf tr tr' cids tg range nxtp nxtc :
  wf_tree tr nxtp nxtc ->
  memory_access AccessRead cids tg range tr = Some tr' ->
  wf_tree tr' nxtp nxtc.
Proof.
  intros WF Dealloc.
  apply (tree_apply_access_wf _ _ _ _ _ _ _ _ WF Dealloc).
Qed.

Lemma memory_write_wf tr tr' cids tg range nxtp nxtc :
  wf_tree tr nxtp nxtc ->
  memory_access AccessWrite cids tg range tr = Some tr' ->
  wf_tree tr' nxtp nxtc.
Proof.
  intros WF Dealloc.
  apply (tree_apply_access_wf _ _ _ _ _ _ _ _ WF Dealloc).
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

Lemma wf_init_tree c t t' :
  (t' < t)%nat ->
  wf_tree (init_tree t') t c.
Proof.
  intro Le.
  unfold wf_tree; unfold tree_item_included.
  intros tg Ex. inversion Ex as [isTag|[Contra|Contra]].
  -- simpl in isTag; inversion isTag as [isRootTag]. simpl in isRootTag. eexists; simpl.
     rewrite /IsTag in isTag |- *; simpl in *. split; [|split].
     ** rewrite /init_tree /tree_unique /= /has_tag /IsTag /=.
        rewrite bool_decide_eq_true_2; auto.
     ** tauto.
     ** rewrite /item_wf. simpl. split.
        ++ intros tg' Tag. inversion Tag. subst. simpl. lia.
        ++ intros cid' Prot. inversion Prot.
  -- inversion Contra.
  -- inversion Contra.
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
  - apply extend_trees_wf.
    * eapply wf_trees_mono.
      3: apply WF.
      all: simpl; lia.
    * apply wf_init_tree.
      lia.
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
    apply (apply_within_trees_wf _ _ nxtp' nxtp' nxtc' nxtc' _ _ ACC).
    * tauto.
    * intros tr tr'. apply memory_deallocate_wf.
    * apply (WF.(state_wf_tree_item _)).
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
    apply (apply_within_trees_wf _ _ nxtp' nxtp' nxtc' nxtc' _ _ ACC).
    * tauto.
    * intros tr tr'. apply memory_read_wf.
    * apply (WF.(state_wf_tree_item _)).
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
    apply (apply_within_trees_wf _ _ nxtp' nxtp' nxtc' nxtc' _ _ ACC).
    * tauto.
    * intros tr tr'. apply memory_write_wf.
    * apply (WF.(state_wf_tree_item _)).
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
  - eapply wf_trees_mono; [| |apply WF]; auto.
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

Lemma insert_child_wf cids oldt nxtp newp nxtc
  (IT_WF : item_wf (create_new_item nxtp newp) (S nxtp) nxtc)
  : preserve_tree_wf (create_child cids oldt nxtp newp) nxtp (S nxtp) nxtc nxtc.
Proof.
  intros tr tr' WF CREATE tg Ex'.
  destruct (decide (tg = nxtp)).
  - unfold create_child in CREATE.
    exists (create_new_item nxtp newp).
    split; [|split].
    + injection CREATE; intros; subst; clear CREATE.
      apply inserted_unique.
      * rewrite /create_new_item /IsTag //=.
      * intro TooBig. destruct (WF nxtp TooBig) as [it0 [_ [Det0 [Lt0 _]]]].
        specialize (Lt0 nxtp ltac:(eapply tree_determined_specifies_tag; eauto)).
        lia.
      * assert (tree_contains oldt tr) as ExOld. {
          eapply exists_insert_requires_parent; [|apply Ex'].
          rewrite every_not_eqv_not_exists; intro Exp.
          destruct (WF nxtp Exp) as [it0 [_ [Det0 [Lt0 _]]]].
          specialize (Lt0 nxtp ltac:(eapply tree_determined_specifies_tag; eauto)).
          lia.
        }
        destruct (WF oldt ExOld) as [_ [Unq _]].
        assumption.
    + injection CREATE; intros; subst; clear CREATE.
      apply insert_true_preserves_every.
      * tauto.
      * unfold wf_tree in WF; unfold tree_item_included in WF.
        rewrite every_node_eqv_universal. intros it Ex'' MalformedIsTag.
        assert (tree_contains nxtp tr) as MalformedContains. {
          eapply exists_node_increasing; [exact Ex''|].
          rewrite every_node_eqv_universal; intros.
          simpl; subst.
          assumption.
        }
        destruct (WF nxtp MalformedContains) as [it' [Uniqueit' [Detit' [Wfit' _]]]].
        specialize (Wfit' nxtp). unfold IsTag in Wfit'.
        rewrite (tree_determined_specifies_tag tr _ _ MalformedContains Detit') in Wfit'.
        specialize (Wfit' ltac:(auto)).
        lia.
    + assumption.
  - assert (tree_contains tg tr) as Ex. {
      eapply insertion_minimal_tags; [| |exact CREATE]; auto.
    }
    destruct (WF tg Ex) as [it [Uniqueit [Detit WFit]]].
    exists it. split; [|split].
    + rewrite /tree_unique. erewrite <-create_child_preserves_count; eassumption.
    + eapply create_child_preserves_determined; [| |exact CREATE]; auto.
    + eapply wf_item_mono; [| |eassumption]; lia.
Qed.

Lemma retag_step_wf σ σ' e e' l ot nt ptr cid efs :
  mem_expr_step σ.(shp) e (RetagEvt l ot nt ptr cid) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (RetagEvt l ot nt ptr cid)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS as [| | | |????????? SAME_CID ? RETAG_EFFECT READ_ON_REBOR| | |]. clear IS. simplify_eq.
  constructor; simpl.
  - rewrite /same_blocks /=.
    (* Something is bodged here *)
    setoid_rewrite <- (apply_within_trees_same_dom _ _ _ _ READ_ON_REBOR).
    setoid_rewrite <- (apply_within_trees_same_dom _ _ _ _ RETAG_EFFECT).
    apply WF.
  - apply (apply_within_trees_wf _ _ (S nt) (S nt) nxtc' nxtc' _ _ READ_ON_REBOR).
    * intros tr WFtr. eapply wf_tree_mono; [| |eassumption]; auto.
    * intros tr tr'.
      intros WFold Access. eapply memory_read_wf; [|eassumption].
      eapply wf_tree_mono; [| |eassumption]; auto.
    * apply (apply_within_trees_wf _ _ nt (S nt) nxtc' nxtc' _ _ RETAG_EFFECT).
      + intros tr WFtr. eapply wf_tree_mono; [| |eassumption]; auto.
      + intros tr tr'.
        intros WFold Access. eapply insert_child_wf; [|eassumption|eassumption].
        unfold item_wf. split.
        -- intros tg Eqtg. unfold IsTag, create_new_item in Eqtg. simpl in Eqtg. lia.
        -- intros cid' prot.
           apply WF; simpl.
           enough (cid = cid') by (subst; auto).
           simpl in prot.
           unfold protector_is_for_call in prot, SAME_CID.
           rewrite prot in SAME_CID.
           injection SAME_CID; [auto|].
           destruct (new_protector ptr); auto.
           inversion prot.
      + apply WF.
  - unshelve eapply (apply_within_trees_preserve_nonempty _ _ _ _ _ (memory_access_preserve_nonempty _ _ _ _) READ_ON_REBOR).
    unshelve eapply (apply_within_trees_preserve_nonempty _ _ _ _ _ (create_child_preserve_nonempty _ _ _ _) RETAG_EFFECT).
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
