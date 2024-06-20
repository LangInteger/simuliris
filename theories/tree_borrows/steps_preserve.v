From iris.prelude Require Import prelude options.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas bor_lemmas.
From iris.prelude Require Import options.

(* Any function that operates only on permissions (which is all transitions steps)
   leaves the tag and protector unchanged which means that most of the preservation lemmas
   are trivial once we get to the level of items *)
Definition preserve_item_metadata (fn:item -> option item) :=
  forall it it', fn it = Some it' -> it.(itag) = it'.(itag) /\ it.(iprot) = it'.(iprot) /\ it.(initp) = it'.(initp).

Lemma item_apply_access_preserves_metadata_dep
  {kind cids rel range} :
  preserve_item_metadata (λ it, item_apply_access kind cids (rel it) range it).
Proof.
  intros it it'. rewrite /item_apply_access.
  destruct permissions_apply_range'; simpl.
  2: intro; discriminate.
  intros [= <-]. rewrite //=.
Qed.

Lemma item_apply_access_preserves_metadata
  {kind cids rel range} :
  preserve_item_metadata (λ it, item_apply_access kind cids rel range it).
Proof.
  eapply item_apply_access_preserves_metadata_dep.
Qed.

Lemma access_eqv_immediate_rel
  {t t' tr tr' fn cids tg range}
  (Access : tree_apply_access fn cids tg range tr = Some tr')
  : ImmediateParentChildIn t t' tr <-> ImmediateParentChildIn t t' tr'.
Proof.
  eapply join_map_eqv_imm_rel; [|exact Access].
  rewrite /=.
  move=> ???.
  unshelve erewrite (proj1 (item_apply_access_preserves_metadata _ _ ltac:(eassumption))).
  reflexivity.
Qed.

Lemma access_eqv_strict_rel
  {t t' tr tr' fn cids tg range}
  (Access : tree_apply_access fn cids tg range tr = Some tr')
  : StrictParentChildIn t t' tr <-> StrictParentChildIn t t' tr'.
Proof.
  eapply join_map_eqv_strict_rel; [|exact Access].
  rewrite /=.
  move=> ???.
  unshelve erewrite (proj1 (item_apply_access_preserves_metadata _ _ ltac:(eassumption))).
  reflexivity.
Qed.

Lemma access_eqv_rel
  {t t' tr tr' fn cids tg range}
  (Access : tree_apply_access fn cids tg range tr = Some tr')
  : ParentChildIn t t' tr <-> ParentChildIn t t' tr'.
Proof.
  unfold ParentChildIn.
  rewrite access_eqv_strict_rel; [|exact Access].
  tauto.
Qed.

Lemma access_preserves_tags
  {tr tg  tr' tg' app cids range}
  (Access : tree_apply_access app cids tg' range tr = Some tr')
  : tree_contains tg tr <-> tree_contains tg tr'.
Proof.
  unfold tree_apply_access in Access.
  unfold tree_contains in *.
  rewrite (join_project_exists _ _ tr').
  2: exact Access.
  rewrite exists_node_map.
  unfold compose.
  pose proof (proj1 (join_success_condition (map_nodes _ tr)) (mk_is_Some _ _ Access)) as H.
  rewrite every_node_map in H.
  split; intro Contains.
  * eapply exists_node_increasing.
    - exact Contains.
    - unfold compose in H.
      rewrite every_node_eqv_universal.
      rewrite every_node_eqv_universal in H.
      intros x Exists Tagx.
      pose proof (H x Exists) as Hspec.
      destruct Hspec as [v App].
      exists v.
      split; auto.
      subst.
      symmetry.
      rewrite (proj1 ( item_apply_access_preserves_metadata _ _ ltac:(eassumption))).
      reflexivity.
  * eapply exists_node_increasing.
    - exact Contains.
    - rewrite every_node_eqv_universal.
      intros x Exists xspec.
      destruct xspec as [v App].
      destruct App as [H0].
      subst.
      rewrite (proj1 (item_apply_access_preserves_metadata _ _ ltac:(eassumption))).
      reflexivity.
Qed.

Lemma insertion_preserves_tags
  {tr tg tgp tgc cids tr' pk rk cid}
  (Ex : tree_contains tg tr)
  (Create : create_child cids tgp tgc pk rk cid tr = Some tr')
  : tree_contains tg tr'.
Proof.
  unfold tree_contains in *.
  pose proof (create_child_isSome tr _ _ _ _ _ _ _ Create) as Insert.
  rewrite Insert.
  apply insert_preserves_exists.
  exact Ex.
Qed.

Lemma insertion_minimal_tags
  {tr tg tgp tgc cids tr' pk rk cid}
  (Ne : tgc ≠ tg)
  (Ex : tree_contains tg tr')
  (Create : create_child cids tgp tgc pk rk cid tr = Some tr')
  : tree_contains tg tr.
Proof.
  unfold tree_contains in *.
  pose proof (create_child_isSome tr _ _ _ _ _ _ _ Create) as Insert.
  all: rewrite Insert in Ex.
  eapply insert_false_infer_exists; [|exact Ex].
  simpl; assumption.
Qed.

Lemma apply_access_spec_per_node
  {tr affected_tag access_tag pre fn cids range tr'}
  (*(ExAcc : tree_contains access_tag tr)*)
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (Access : tree_apply_access fn cids access_tag range tr = Some tr')
  : exists post,
    Some post = item_apply_access fn cids (rel_dec tr access_tag pre.(itag)) range pre
    /\ tree_contains affected_tag tr'
    /\ tree_item_determined affected_tag post tr'.
Proof.
  (* Grab the success condition of every node separately *)
  pose proof (proj1 (join_success_condition _) (mk_is_Some _ _ Access)) as SuccessCond.
  rewrite every_node_map in SuccessCond; rewrite every_node_eqv_universal in SuccessCond.
  pose proof (exists_determined_exists _ _ _ ExAff UnqAff) as Expre.
  pose proof (SuccessCond pre Expre) as [post SpecPost].
  unfold tree_item_determined in UnqAff. rewrite every_node_eqv_universal in UnqAff.
  (* Now do some transformations to get to the node level *)
  unfold tree_item_determined.
  exists post.
  split; [symmetry; auto|].
  split; [rewrite <- (access_preserves_tags Access); exact ExAff|].
  rewrite join_project_every; [|exact Access].
  rewrite every_node_map.
  unfold compose.
  rewrite every_node_eqv_universal.
  intros n Exn.
  destruct (decide (IsTag affected_tag n)).
  * pose proof (UnqAff n Exn) as PerNodeEqual.
    clear Access ExAff SuccessCond UnqAff ExAff Exn.
    exists post.
    split; [|tauto].
    rewrite PerNodeEqual; auto.
  * pose proof (SuccessCond n Exn) as NodeSuccess.
    destruct NodeSuccess as [post' post'Spec].
    exists post'.
    split.
    - tauto.
    - rewrite <- (proj1 (item_apply_access_preserves_metadata _ _ ltac:(eassumption))).
      tauto.
Qed.

Lemma bor_local_step_preserves_contains
  {tg tr tr' cids cids' evt}
  (Ex : tree_contains tg tr)
  (Step : bor_local_step
    tr cids
    evt
    tr' cids')
  : tree_contains tg tr'.
Proof.
  inversion Step as [????? ACC| | |]; subst.
  - (* Access *)
    erewrite <- access_preserves_tags; [eassumption|exact ACC].
  - (* InitCall *) assumption.
  - (* EndCall *) assumption.
  - (* Retag *)
    eapply insertion_preserves_tags; eauto.
Qed.

Lemma bor_local_step_retag_produces_contains_determined
  {tgp tg tr tr' cids cids' pk rk cid}
  (Step : bor_local_step
    tr cids
    (RetagBLEvt tgp tg pk cid rk)
    tr' cids')
  : tree_contains tg tr'
  /\ tree_item_determined tg (create_new_item tg pk rk cid) tr'.
Proof.
  inversion Step as [| | |????????? RETAG_EFFECT]; subst.
  split.
  - eapply insertion_contains; eauto.
  - injection RETAG_EFFECT; intros; subst.
    eapply inserted_determined; [apply new_item_has_tag|].
    assumption.
Qed.

Lemma bor_local_step_preserves_determined_easy
  {tg tr it tr' cids cids' evt}
  (Ex : tree_contains tg tr)
  (Unq : tree_item_determined tg it tr)
  (Step : bor_local_step tr cids evt tr' cids')
  : exists it',
  tree_item_determined tg it' tr'
  /\ match evt with
  | AccessBLEvt _ _ _ => iprot it = iprot it'
  | InitCallBLEvt _
  | EndCallBLEvt _
  | RetagBLEvt _ _ _ _ _
  | SilentBLEvt => it = it'
  end.
Proof.
  inversion Step as [???? EXISTS_TAG ACC| | |???????? FRESH_CHILD RETAG_EFFECT]; subst.
  - (* Access *)
    destruct (apply_access_spec_per_node Ex Unq ACC) as [?[Spec[_?]]].
    eexists; split; eauto.
    symmetry in Spec. eapply item_apply_access_preserves_metadata; exact Spec.
  - eexists; split; [|reflexivity]; assumption.
  - eexists; split; [|reflexivity]; assumption.
  - (* Retag *)
    eexists; split; [|reflexivity].
    eapply create_child_preserves_determined; [|exact Unq|exact RETAG_EFFECT].
    intro; subst. destruct (FRESH_CHILD Ex).
Qed.

Lemma bor_local_step_eqv_rel
  {tg tg' tr tr' cids cids' evt}
  (Ex : tree_contains tg tr)
  (Ex' : tree_contains tg' tr)
  (Step : bor_local_step tr cids evt tr' cids')
  : ParentChildIn tg tg' tr <-> ParentChildIn tg tg' tr'.
Proof.
  inversion Step as [????? ACC| | |???????? FRESH_CHILD RETAG_EFFECT]; subst.
  - (* Access *)
    rewrite access_eqv_rel; [|apply ACC].
    tauto.
  - tauto.
  - tauto.
  - (* Retag *)
    injection RETAG_EFFECT; intros; subst.
    rewrite <- insert_eqv_rel.
    * tauto.
    * rewrite new_item_has_tag; intro; subst; destruct (FRESH_CHILD Ex).
    * rewrite new_item_has_tag; intro; subst; destruct (FRESH_CHILD Ex').
Qed.

Lemma bor_local_step_eqv_imm_rel
  {tg tg' tr tr' cids cids' evt}
  (Ex : tree_contains tg tr)
  (Ex' : tree_contains tg' tr)
  (Step : bor_local_step tr cids evt tr' cids')
  : ImmediateParentChildIn tg tg' tr <-> ImmediateParentChildIn tg tg' tr'.
Proof.
  inversion Step as [????? ACC| | |???????? FRESH_CHILD RETAG_EFFECT]; subst.
  - (* Access *)
    rewrite access_eqv_immediate_rel; [|apply ACC].
    tauto.
  - tauto.
  - tauto.
  - (* Retag *)
    injection RETAG_EFFECT; intros; subst.
    rewrite <- insert_eqv_imm_rel.
    * tauto.
    * rewrite new_item_has_tag; intro; subst; destruct (FRESH_CHILD Ex).
    * rewrite new_item_has_tag; intro; subst; destruct (FRESH_CHILD Ex').
Qed.

Lemma bor_local_step_retag_produces_rel
  {tgp tg tr tr' cids cids' pk rk cid}
  (Step : bor_local_step
    tr cids
    (RetagBLEvt tgp tg pk rk cid)
    tr' cids')
  : ParentChildIn tgp tg tr'.
Proof.
  inversion Step as [????? ACC| | |??????? EXISTS_PARENT FRESH_CHILD RETAG_EFFECT]; subst.
  injection RETAG_EFFECT; intros; subst.
  eapply insert_produces_ParentChild.
  * eapply new_item_has_tag.
  * intro; subst; destruct (FRESH_CHILD EXISTS_PARENT).
Qed.

Lemma bor_local_step_retag_order_nonparent
  {tgp tg tg' tr tr' cids cids' pk rk cid}
  (Ex' : tree_contains tg' tr)
  (Step : bor_local_step
    tr cids
    (RetagBLEvt tgp tg pk rk cid)
    tr' cids')
  : ~ParentChildIn tg tg' tr'.
Proof.
  inversion Step as [????? ACC| | |??????? EXISTS_PARENT FRESH_CHILD RETAG_EFFECT]; subst.
  injection RETAG_EFFECT; intros; subst.
  eapply insertion_order_nonparent; eassumption.
Qed.

Lemma apply_access_perm_preserves_backward_reach
  {pre post kind rel b p0}
  (Access : apply_access_perm kind rel b pre = Some post)
  : reach p0 (perm pre) -> reach p0 (perm post).
Proof.
  destruct b, kind, rel.
  (* We have to destructure the permission a bit deep because of the Reserved parameters *)
  all: destruct pre as [[] [[][]| | |]]; try (inversion Access; done).
  all: destruct post as [[] [[][]| | |]]; try (inversion Access; done).
  all: destruct p0 as [[][]| | |]; try (inversion Access; done).
Qed.

Lemma apply_access_perm_preserves_forward_unreach
  {pre post kind rel b p0}
  (Access : apply_access_perm kind rel b pre = Some post)
  : ~reach (perm pre) p0 -> ~reach (perm post) p0.
Proof.
  destruct b, kind, rel.
  all: destruct pre as [[][[][]| | |]]; try (inversion Access; done).
  all: destruct post as [[][[][]| | |]]; try (inversion Access; done).
  all: destruct p0 as [[][]| | |]; try (inversion Access; done).
Qed.

Lemma apply_access_perm_preserves_protected_freeze_like
  {pre post kind rel}
  (Access : apply_access_perm kind rel true pre = Some post)
  : freeze_like (perm pre) -> freeze_like (perm post).
Proof.
  unfold freeze_like.
  destruct kind, rel.
  all: destruct pre as [[][[][]| | |]].
  all: inversion Access.
  (* all cases easy *)
  all: intros [H|[H|H]]; inversion H.
  all: try (left; done).
  all: try (right; left; done).
  all: try (right; right; done).
Qed.

(* Preservation of reachability *)
Lemma memory_access_preserves_backward_reach
  {access_tag affected_tag pre tr post tr' kind cids range p0 z}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  : reach p0 (item_perm_at_loc pre z) -> reach p0 (item_perm_at_loc post z).
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_preserves_backward_reach.
    rewrite Lkup; simpl. exact Apply.
  - rewrite Spec; tauto.
Qed.

Lemma memory_access_preserves_forward_unreach
  {access_tag affected_tag pre tr post tr' kind cids range p0 z}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  : ~reach (item_perm_at_loc pre z) p0 -> ~reach (item_perm_at_loc post z) p0.
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_preserves_forward_unreach.
    rewrite Lkup; simpl. exact Apply.
  - rewrite Spec; tauto.
Qed.

Lemma memory_access_preserves_protected_freeze_like
  {access_tag affected_tag pre tr post tr' kind cids range z}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Prot : protector_is_active (iprot pre) cids)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  : freeze_like (item_perm_at_loc pre z) -> freeze_like (item_perm_at_loc post z).
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ Prot post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_preserves_protected_freeze_like.
    rewrite bool_decide_eq_true_2 in Apply; [|assumption].
    rewrite Lkup; simpl. exact Apply.
  - rewrite Spec; tauto.
Qed.

Lemma bor_local_step_preserves_backward_reach
  {tg tr tr' cids cids' pre post evt p0 z}
  (Ex : tree_contains tg tr)
  (UnqPre : tree_item_determined tg pre tr)
  (Step : bor_local_step tr cids evt tr' cids')
  (UnqPost : tree_item_determined tg post tr')
  : reach p0 (item_perm_at_loc pre z) -> reach p0 (item_perm_at_loc post z).
Proof.
  inversion Step as [???? EXISTS_TAG ACC| | |]; subst.
  - apply (memory_access_preserves_backward_reach Ex UnqPre EXISTS_TAG ACC UnqPost).
  - rewrite (tree_determined_unify Ex UnqPre UnqPost); tauto.
  - rewrite (tree_determined_unify Ex UnqPre UnqPost); tauto.
  - pose proof (bor_local_step_preserves_contains Ex Step) as ExPost'.
    pose proof (bor_local_step_preserves_determined_easy Ex UnqPre Step) as [it' [UnqPost' Eq]]; subst; simpl in UnqPost'.
    rewrite (tree_determined_unify ExPost' UnqPost' UnqPost); tauto.
Qed.

Lemma bor_local_step_preserves_forward_unreach
  {tg tr tr' cids cids' pre post evt p0 z}
  (Ex : tree_contains tg tr)
  (UnqPre : tree_item_determined tg pre tr)
  (Step : bor_local_step tr cids evt tr' cids')
  (UnqPost : tree_item_determined tg post tr')
  : ~reach (item_perm_at_loc pre z) p0 -> ~reach (item_perm_at_loc post z) p0.
Proof.
  inversion Step as [???? EXISTS_TAG ACC| | |]; subst.
  - apply (memory_access_preserves_forward_unreach Ex UnqPre EXISTS_TAG ACC UnqPost).
  - rewrite (tree_determined_unify Ex UnqPre UnqPost); tauto.
  - rewrite (tree_determined_unify Ex UnqPre UnqPost); tauto.
  - pose proof (bor_local_step_preserves_contains Ex Step) as ExPost'.
    pose proof (bor_local_step_preserves_determined_easy Ex UnqPre Step) as [it' [UnqPost' Eq]]; subst; simpl in UnqPost'.
    rewrite (tree_determined_unify ExPost' UnqPost' UnqPost); tauto.
Qed.

Lemma bor_local_step_preserves_protected_freeze_like
  {tg tr tr' cids cids' pre post evt z}
  (Ex : tree_contains tg tr)
  (UnqPre : tree_item_determined tg pre tr)
  (Prot : protector_is_active (iprot pre) cids)
  (Step : bor_local_step tr cids evt tr' cids')
  (UnqPost : tree_item_determined tg post tr')
  : freeze_like (item_perm_at_loc pre z) -> freeze_like (item_perm_at_loc post z).
Proof.
  inversion Step as [???? EXISTS_TAG ACC| | |]; subst.
  - apply (memory_access_preserves_protected_freeze_like Ex UnqPre EXISTS_TAG Prot ACC UnqPost).
  - rewrite (tree_determined_unify Ex UnqPre UnqPost); tauto.
  - rewrite (tree_determined_unify Ex UnqPre UnqPost); tauto.
  - pose proof (bor_local_step_preserves_contains Ex Step) as ExPost'.
    pose proof (bor_local_step_preserves_determined_easy Ex UnqPre Step) as [it' [UnqPost' Eq]]; subst; simpl in UnqPost'.
    rewrite (tree_determined_unify ExPost' UnqPost' UnqPost); tauto.
Qed.

Lemma seq_always_build_forward
  {invariant invariant'}
  {tr cids evts tr' cids'}
  (INV0 : invariant'.(seq_inv) tr cids)
  (Preserve : forall tr cids tr' cids' evt,
    bor_local_step tr cids evt tr' cids' ->
    invariant.(seq_inv) tr cids ->
    invariant'.(seq_inv) tr cids ->
    invariant'.(seq_inv) tr' cids'
  )
  (Seq : bor_local_seq invariant tr cids evts tr' cids')
  : bor_local_seq invariant' tr cids evts tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent tr'.
  generalize dependent cids.
  generalize dependent cids'.
  induction evts; move=> ????? Seq; inversion Seq; subst.
  - constructor; assumption.
  - econstructor; eauto.
Qed.

Lemma seq_always_destruct_first
  {invariant}
  {tr cids evts tr' cids'}
  (Seq : bor_local_seq invariant tr cids evts tr' cids')
  : invariant.(seq_inv) tr cids.
Proof. inversion Seq; subst; assumption. Qed.

Lemma seq_always_destruct_last
  {invariant}
  {tr cids evts tr' cids'}
  (Seq : bor_local_seq invariant tr cids evts tr' cids')
  : invariant.(seq_inv) tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction evts as [|?? IHevts]; move=> ?? Seq; inversion Seq; subst.
  - assumption.
  - eapply IHevts; eauto.
Qed.

Lemma bor_local_step_deterministic
  {tr cids evt tr1 cids1 tr2 cids2}
  (Step1 : bor_local_step tr cids evt tr1 cids1)
  (Step2 : bor_local_step tr cids evt tr2 cids2)
  : tr1 = tr2 /\ cids1 = cids2.
Proof.
  destruct evt; inversion Step1 as [????? ACC1| | |????????? RETAG_EFFECT1];
      inversion Step2 as [????? ACC2| | |????????? RETAG_EFFECT2]; subst.
  - rewrite ACC1 in ACC2; injection ACC2; tauto.
  - tauto.
  - tauto.
  - rewrite RETAG_EFFECT1 in RETAG_EFFECT2; injection RETAG_EFFECT2; tauto.
Qed.

Lemma bor_local_seq_deterministic
  {invariant tr cids evts tr1 cids1 tr2 cids2}
  (Seq1 : bor_local_seq invariant tr cids evts tr1 cids1)
  (Seq2 : bor_local_seq invariant tr cids evts tr2 cids2)
  : tr1 = tr2 /\ cids1 = cids2.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  generalize dependent tr1.
  generalize dependent cids1.
  generalize dependent tr2.
  generalize dependent cids2.
  induction evts as [|?? IHevts]; move=> ?????? Seq1 Seq2; inversion Seq1 as [|??????? HEAD1]; inversion Seq2 as [|??????? HEAD2].
  - subst. tauto.
  - pose proof (bor_local_step_deterministic HEAD1 HEAD2) as [??]; subst.
    eapply IHevts; eauto.
Qed.

Lemma bor_local_seq_forget
  {invariant tr cids evts tr' cids'}
  (Seq : bor_local_seq invariant tr cids evts tr' cids')
  : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction evts as [|?? IHevts]; move=> ?? Seq; inversion Seq as [|??????? HEAD1]; subst.
  - constructor; done.
  - econstructor; [done|exact HEAD1|].
    eapply IHevts; assumption.
Qed.

Lemma seq_always_build_direct
  {invariant tr cids evts tr' cids'}
  (PTR : forall tr cids, invariant.(seq_inv) tr cids)
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : bor_local_seq invariant tr cids evts tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction evts; move=> ?? Seq; inversion Seq; subst.
  + constructor; auto.
  + econstructor; eauto.
Qed.

Lemma seq_always_build_weaken
  {invariant invariant' tr cids evts tr' cids'}
  (WEAKEN : forall tr cids, invariant.(seq_inv) tr cids -> invariant'.(seq_inv) tr cids)
  (Seq : bor_local_seq invariant tr cids evts tr' cids')
  : bor_local_seq invariant' tr cids evts tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction evts; move=> ?? Seq; inversion Seq; subst.
  + constructor; auto.
  + econstructor; eauto.
Qed.

Lemma seq_always_merge
  {invariant1 invariant2 tr cids evts tr' cids'}
  (Seq1 : bor_local_seq invariant1 tr cids evts tr' cids')
  (Seq2 : bor_local_seq invariant2 tr cids evts tr' cids')
  : bor_local_seq {| seq_inv:=fun tr cids => invariant1.(seq_inv) tr cids /\ invariant2.(seq_inv) tr cids|} tr cids evts tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction evts; move=> ?? Seq1 Seq2; inversion Seq1 as [|??????? HEAD1 REST1]; inversion Seq2 as [|??????? HEAD2 REST2].
  - constructor; split; assumption.
  - pose proof (bor_local_step_deterministic HEAD1 HEAD2) as [??]; subst.
    pose proof (bor_local_seq_deterministic (bor_local_seq_forget REST1) (bor_local_seq_forget REST2)) as [??]; subst.
    econstructor; simpl; eauto.
Qed.

Lemma bor_local_seq_always_contains
  {tg tr cids tr' cids' evts}
  (Ex : tree_contains tg tr)
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : bor_local_seq {|seq_inv:=fun tr _ => (tree_contains tg) tr|} tr cids evts tr' cids'.
Proof.
  eapply seq_always_build_forward; [assumption| |exact Seq].
  clear.
  move=> ????? Step _ Ex; simpl in *.
  eapply bor_local_step_preserves_contains; eassumption.
Qed.

Lemma bor_local_seq_last_contains
  {tg tr cids tr' cids' evts}
  (Ex : tree_contains tg tr)
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : tree_contains tg tr'.
Proof.
  pose proof (seq_always_destruct_last (bor_local_seq_always_contains Ex Seq)).
  assumption.
Qed.

Lemma bor_local_seq_always_determined
  {tg tr tr' prot cids cids' evts pre}
  (Ex : tree_contains tg tr)
  (Unq : tree_item_determined tg pre tr)
  (ProtEq : iprot pre = prot)
  (Seq : bor_local_seq {|seq_inv:=fun tr _ => (tree_contains tg) tr|} tr cids evts tr' cids')
  : bor_local_seq {|seq_inv:=fun tr _ => exists it, tree_item_determined tg it tr /\ iprot it = prot|} tr cids evts tr' cids'.
Proof.
  eapply seq_always_build_forward; [| |exact Seq].
  - eexists; split; eassumption.
  - clear. simpl. move=> ???? evt Step Ex [?[Unq Prot]].
    destruct (bor_local_step_preserves_determined_easy Ex Unq Step) as [?[??]].
    eexists.
    split; [eassumption|].
    destruct evt; subst; auto.
Qed.

Lemma bor_local_seq_last_determined
  {tg tr tr' cids cids' evts pre}
  (Ex : tree_contains tg tr)
  (Unq : tree_item_determined tg pre tr)
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : exists post, tree_item_determined tg post tr' /\ iprot pre = iprot post.
Proof.
  pose proof (bor_local_seq_always_contains Ex Seq) as AllEx.
  destruct (seq_always_destruct_last (bor_local_seq_always_determined Ex Unq eq_refl AllEx)) as [?[??]].
  eexists; split; subst; eauto.
Qed.

Lemma bor_local_seq_always_rel
  {tg tg' tr tr' cids cids' evts}
  (Rel : ParentChildIn tg tg' tr)
  (Ex : tree_contains tg tr)
  (Ex' : tree_contains tg' tr)
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : bor_local_seq {|seq_inv:=fun tr _ => (ParentChildIn tg tg') tr|} tr cids evts tr' cids'.
Proof.
  pose proof (seq_always_merge
    (bor_local_seq_always_contains Ex Seq)
    (bor_local_seq_always_contains Ex' Seq)) as AllExEx'.
  eapply seq_always_build_forward; [assumption| |exact AllExEx'].
  clear; simpl; move=> ????? Step [Ex Ex'] Rel.
  rewrite <- (bor_local_step_eqv_rel Ex Ex' Step).
  assumption.
Qed.

Lemma bor_local_seq_always_unrel
  {tg tg' tr tr' cids cids' evts}
  (Rel : ~ParentChildIn tg tg' tr)
  (Ex : tree_contains tg tr)
  (Ex' : tree_contains tg' tr)
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : bor_local_seq {|seq_inv:=fun tr _ => ~ParentChildIn tg tg' tr|} tr cids evts tr' cids'.
Proof.
  pose proof (seq_always_merge
    (bor_local_seq_always_contains Ex Seq)
    (bor_local_seq_always_contains Ex' Seq)) as AllExEx'.
  eapply seq_always_build_forward; [assumption| |exact AllExEx'].
  clear; simpl; move=> ????? Step [Ex Ex'] Rel.
  rewrite <- (bor_local_step_eqv_rel Ex Ex' Step).
  assumption.
Qed.

Lemma bor_local_seq_last_eqv_rel
  {tg tg' tr tr' cids cids' evts}
  (Ex : tree_contains tg tr)
  (Ex' : tree_contains tg' tr)
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : ParentChildIn tg tg' tr <-> ParentChildIn tg tg' tr'.
Proof.
  destruct (decide (ParentChildIn tg tg' tr)) as [Rel|Unrel].
  - pose proof (seq_always_destruct_last (bor_local_seq_always_rel Rel Ex Ex' Seq)).
    tauto.
  - pose proof (seq_always_destruct_last (bor_local_seq_always_unrel Unrel Ex Ex' Seq)).
    simpl in *.
    tauto.
Qed.

Lemma bor_local_seq_always_backward_reach
  {tg tr tr' cids cids' pre evts p0 z}
  (Ex : tree_contains tg tr)
  (Unq : tree_item_determined tg pre tr)
  (Reach : reach p0 (item_perm_at_loc pre z))
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : bor_local_seq {|seq_inv:=fun tr _ => forall post (UnqPost : tree_item_determined tg post tr), reach p0 (item_perm_at_loc post z)|}
      tr cids evts tr' cids'.
Proof.
  pose proof (bor_local_seq_always_contains Ex Seq) as AllEx.
  pose proof (seq_always_merge AllEx (bor_local_seq_always_determined Ex Unq eq_refl AllEx)) as AllExUnq.
  eapply seq_always_build_forward; [| |exact AllExUnq].
  + move=> ? Unq'. pose proof (tree_determined_unify Ex Unq Unq'); subst. assumption.
  + clear; simpl; move=> ????? Step [Ex [?[Unq _]]] Reach.
    move=> ? Unq'.
    eapply bor_local_step_preserves_backward_reach; eauto.
Qed.

Lemma bor_local_seq_always_protected_freeze_like
  {tg tr tr' cids cids' pre evts cid z}
  (Ex : tree_contains tg tr)
  (Unq : tree_item_determined tg pre tr)
  (Prot : protector_is_for_call cid (iprot pre))
  (Reach : freeze_like (item_perm_at_loc pre z))
  (Seq : bor_local_seq {|seq_inv:=fun _ cids => call_is_active cid cids|} tr cids evts tr' cids')
  : bor_local_seq {|seq_inv:=fun tr _ => forall post (UnqPost : tree_item_determined tg post tr), protector_is_for_call cid (iprot post) /\ freeze_like (item_perm_at_loc post z)|}
      tr cids evts tr' cids'.
Proof.
  pose proof (bor_local_seq_always_contains Ex (bor_local_seq_forget Seq)) as AllEx.
  pose proof (seq_always_merge Seq (seq_always_merge AllEx (bor_local_seq_always_determined Ex Unq eq_refl AllEx))) as AllExUnqProt.
  eapply seq_always_build_forward; [| |exact AllExUnqProt].
  + move=> ? Unq'. pose proof (tree_determined_unify Ex Unq Unq'); subst. split; assumption.
  + clear; simpl; move=> ???? evt Step [Prot [Ex [? [Unq _]]]] Reach.
    move=> ? Unq'.
    destruct (Reach _ Unq) as [SameProt FrzLike].
    split.
    * pose proof (bor_local_step_preserves_contains Ex Step) as Ex'.
      destruct (bor_local_step_preserves_determined_easy Ex Unq Step) as [x [Unqx Protx]].
      pose proof (tree_determined_unify Ex' Unq' Unqx); subst.
      destruct evt; rewrite <- Protx; assumption.
    * eapply bor_local_step_preserves_protected_freeze_like; eauto.
      exists cid; split; assumption.
Qed.

Lemma bor_local_seq_last_backward_reach
  {tg tr tr' cids cids' pre evts p0 z}
  (Ex : tree_contains tg tr)
  (Unq : tree_item_determined tg pre tr)
  (Reach : reach p0 (item_perm_at_loc pre z))
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : forall post (UnqPost : tree_item_determined tg post tr'), reach p0 (item_perm_at_loc post z).
Proof.
  pose proof (seq_always_destruct_last (bor_local_seq_always_backward_reach Ex Unq Reach Seq)).
  assumption.
Qed.

Lemma bor_local_seq_last_protected_freeze_like
  {tg tr tr' cids cids' pre evts cid z}
  (Ex : tree_contains tg tr)
  (Unq : tree_item_determined tg pre tr)
  (Prot : protector_is_for_call cid (iprot pre))
  (FrzLike : freeze_like (item_perm_at_loc pre z))
  (Seq : bor_local_seq {|seq_inv:=fun _ cids => call_is_active cid cids|} tr cids evts tr' cids')
  : forall post (UnqPost : tree_item_determined tg post tr'), protector_is_for_call cid (iprot post) /\ freeze_like (item_perm_at_loc post z).
Proof.
  pose proof (seq_always_destruct_last (bor_local_seq_always_protected_freeze_like Ex Unq Prot FrzLike Seq)).
  assumption.
Qed.

Lemma bor_local_seq_always_forward_unreach
  {tg tr tr' cids cids' pre evts p0 z}
  (Ex : tree_contains tg tr)
  (Unq : tree_item_determined tg pre tr)
  (Unreach : ~reach (item_perm_at_loc pre z) p0)
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : bor_local_seq {|seq_inv:=fun tr _ => forall post (UnqPost : tree_item_determined tg post tr), ~reach (item_perm_at_loc post z) p0|}
      tr cids evts tr' cids'.
Proof.
  pose proof (bor_local_seq_always_contains Ex Seq) as AllEx.
  pose proof (seq_always_merge AllEx (bor_local_seq_always_determined Ex Unq eq_refl AllEx)) as AllExUnq.
  eapply seq_always_build_forward; [| |exact AllExUnq].
  + move=> ? Unq'. pose proof (tree_determined_unify Ex Unq Unq'); subst. assumption.
  + clear; move=> ????? Step [Ex [?[Unq _]]] Reach.
    move=> ? Unq'.
    eapply bor_local_step_preserves_forward_unreach; eauto.
Qed.

Lemma bor_local_seq_last_forward_unreach
  {tg tr tr' cids cids' pre evts p0 z}
  (Ex : tree_contains tg tr)
  (Unq : tree_item_determined tg pre tr)
  (Unreach : ~reach (item_perm_at_loc pre z) p0)
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : forall post (UnqPost : tree_item_determined tg post tr'), ~reach (item_perm_at_loc post z) p0.
Proof.
  pose proof (seq_always_destruct_last (bor_local_seq_always_forward_unreach Ex Unq Unreach Seq)).
  assumption.
Qed.

Lemma bor_local_seq_split
  {invariant tr tr' cids cids' l l'}
  : bor_local_seq invariant tr cids (l ++ l') tr' cids'
  <-> exists tr'' cids'', bor_local_seq invariant tr cids l tr'' cids'' /\ bor_local_seq invariant tr'' cids'' l' tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction l as [|?? IHl]; move=> ??.
  - simpl; split; intro Hyp.
    + eexists. eexists. split; [constructor|assumption].
      all: inversion Hyp; subst; auto.
    + destruct Hyp as [?[?[S S']]].
      inversion S; subst.
      exact S'.
  - simpl; split; intro Hyp.
    + inversion Hyp as [|??????? HEAD REST]; subst.
      rewrite IHl in REST.
      destruct REST as [?[?[S' S'']]].
      eexists. eexists.
      split.
      * econstructor; [assumption|exact HEAD|exact S'].
      * assumption.
    + destruct Hyp as [?[?[S S']]].
      inversion S as [|??????? HEAD REST]; subst.
      econstructor; [assumption|exact HEAD|].
      rewrite IHl.
      eexists. eexists.
      split; eassumption.
Qed.

Lemma apply_access_perm_preserves_perminit
  {pre post kind rel b}
  (Access : apply_access_perm kind rel b pre = Some post)
  : (initialized pre) = PermInit -> initialized post = PermInit.
Proof.
  destruct kind, rel.
  all: destruct pre as [[][[][]| | |]], b.
  all: inversion Access.
  (* all cases easy *)
  all: simpl; auto.
  all: intros H H'; inversion H'; inversion H.
Qed.


Lemma memory_access_preserves_perminit
  {access_tag affected_tag pre tr post tr' kind cids range z zpre zpost}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (ItemPost : item_lazy_perm_at_loc post z = zpost)
  (Init : initialized zpre = PermInit)
  : initialized zpost = PermInit.
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ Init post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  destruct (bool_decide _).
  all: destruct (decide (range'_contains _ _)).
  all: try (rewrite Spec; tauto).
  all: destruct Spec as [?[Lkup Apply]].
  all: eapply apply_access_perm_preserves_perminit; [|eassumption].
  all: rewrite Lkup; simpl; try exact Apply.
Qed.

Lemma apply_access_perm_child_produces_perminit
  {pre post kind b rel}
  (CHILD : if rel is Child _ then True else False)
  (Access : apply_access_perm kind rel b pre = Some post)
  : initialized post = PermInit.
Proof.
  destruct kind, rel; try inversion CHILD.
  all: destruct pre as [[][[][]| | |]], b.
  all: inversion Access.
  (* all cases easy *)
  all: simpl; auto.
Qed.

Lemma memory_access_child_produces_perminit
  {access_tag affected_tag pre tr post tr' kind cids range z zpre zpost}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (Rel : ParentChildIn affected_tag access_tag tr)
  (WithinRange : range'_contains range z)
  (UnqAff' : tree_item_determined affected_tag post tr')
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (ItemPost : item_lazy_perm_at_loc post z = zpost)
  : initialized zpost = PermInit.
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  rewrite (tree_determined_specifies_tag _ _ _ ExAff UnqAff) in PostSpec.
  unfold rel_dec in PostSpec.
  destruct (decide (ParentChildIn affected_tag access_tag tr)); [|contradiction].
  destruct (decide (ParentChildIn access_tag affected_tag tr)).
  all: option step in PostSpec as ?:Foreach.
  all: injection PostSpec; intros e; subst; clear PostSpec.
  all: pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  all: rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  all: destruct (bool_decide _).
  all: destruct (decide (range'_contains _ _)); [|contradiction].
  all: try (rewrite Spec; tauto).
  all: destruct Spec as [?[Lkup Apply]].
  all: eapply apply_access_perm_child_produces_perminit.
  all: try eassumption.
  all: try (rewrite Lkup; simpl; try exact Apply).
  all: simpl; done.
Qed.

Lemma bor_local_step_preserves_perminit
  {affected_tag tr cids evt tr' cids' pre z zpre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_item_determined affected_tag pre tr)
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (Initialized : initialized zpre = PermInit)
  (Step : bor_local_step tr cids evt tr' cids')
  : forall post,
    tree_item_determined affected_tag post tr' ->
    initialized (item_lazy_perm_at_loc post z) = PermInit.
Proof.
  move=> post Unq'.
  inversion Step as [???? EXISTS_TAG ACC| | |?? tg???? FRESH_CHILD ? RETAG_EFFECT]; subst.
  - eapply memory_access_preserves_perminit.
    + exact Ex.
    + exact Unq.
    + exact EXISTS_TAG.
    + exact ACC.
    + exact Unq'.
    + reflexivity.
    + reflexivity.
    + exact Initialized.
  - pose proof (tree_determined_unify Ex Unq Unq'); subst.
    assumption.
  - pose proof (tree_determined_unify Ex Unq Unq'); subst.
    assumption.
  - assert (affected_tag ≠ tg) as Ne by (intro; subst; contradiction).
    pose proof (create_child_preserves_determined _ _ _ _ _ _ _ _ _ _ Ne Unq RETAG_EFFECT) as UnqPost.
    pose proof (insertion_preserves_tags Ex RETAG_EFFECT) as Ex'.
    pose proof (tree_determined_unify Ex' UnqPost Unq'); subst.
    assumption.
Qed.

Lemma bor_local_step_child_produces_perminit
  {access_tag affected_tag pre tr tr' kind cids cids' z range}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (Rel : ParentChildIn affected_tag access_tag tr)
  (WithinRange : range'_contains range z)
  (Step : bor_local_step tr cids (AccessBLEvt kind access_tag range) tr' cids')
  : forall post,
    tree_item_determined affected_tag post tr' ->
    initialized (item_lazy_perm_at_loc post z) = PermInit.
Proof.
  inversion Step; subst.
  intros.
  eapply memory_access_child_produces_perminit.
  1: exact ExAff.
  all: eauto.
Qed.

Lemma bor_local_seq_always_perminit
  {affected_tag tr tr' cids cids' evts pre z}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_item_determined affected_tag pre tr)
  (InitPre : initialized (item_lazy_perm_at_loc pre z) = PermInit)
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  : bor_local_seq
    {|seq_inv:=fun tr _ =>
      forall it,
      tree_item_determined affected_tag it tr ->
      initialized (item_lazy_perm_at_loc it z) = PermInit|}
    tr cids evts tr' cids'.
Proof.
  pose proof (bor_local_seq_always_contains Ex Seq) as SeqEx.
  pose proof (bor_local_seq_always_determined Ex Unq eq_refl SeqEx) as SeqUnq.
  eapply seq_always_build_forward; simpl; [| |exact (seq_always_merge SeqEx SeqUnq)].
  - intros pre' Unq'. pose proof (tree_determined_unify Ex Unq Unq'); subst.
    assumption.
  - intros ????? Step Inv Init.
    simpl in Inv; destruct Inv as [Exi [?[Unqi ?]]].
    eapply bor_local_step_preserves_perminit.
    1: exact Exi.
    all: eauto.
Qed.

Lemma apply_access_perm_protected_initialized_preserves_active
  {pre post kind rel}
  (Access : apply_access_perm kind rel true pre = Some post)
  : (initialized pre) = PermInit -> (perm pre) = Active -> (perm post) = Active.
Proof.
  destruct kind, rel.
  all: destruct pre as [[][]].
  all: inversion Access.
  (* all cases easy *)
  all: simpl; auto.
  all: intros H H'; inversion H'; inversion H.
Qed.

Lemma memory_access_protected_initialized_preserves_active
  {access_tag affected_tag pre tr post tr' kind cids range z zpre zpost}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  (Prot : protector_is_active (iprot pre) cids)
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (ItemPost : item_lazy_perm_at_loc post z = zpost)
  (Init : initialized zpre = PermInit)
  : perm zpre = Active -> perm zpost = Active.
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ Prot Init post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  rewrite bool_decide_eq_true_2 in Spec; [|assumption].
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_protected_initialized_preserves_active.
    + rewrite Lkup; simpl. exact Apply.
    + assumption.
  - rewrite Spec; tauto.
Qed.

Lemma protected_during_step_stays_active
  {affected_tag tr cids evt tr' cids' pre z zpre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_item_determined affected_tag pre tr)
  (Prot : protector_is_active (iprot pre) cids)
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (Init : initialized zpre = PermInit)
  (ActPre : perm zpre = Active)
  (Step : bor_local_step tr cids evt tr' cids')
  : forall post, tree_item_determined affected_tag post tr' -> item_perm_at_loc post z = Active.
Proof.
  move=> ? Unq'.
  inversion Step as [???? EXISTS_TAG ACC| | |?? tg???? FRESH_CHILD ? RETAG_EFFECT]; subst.
  - apply (memory_access_protected_initialized_preserves_active Ex Unq EXISTS_TAG ACC Unq' Prot eq_refl eq_refl Init ActPre).
  - rewrite <- (tree_determined_unify Ex Unq Unq'); tauto.
  - rewrite <- (tree_determined_unify Ex Unq Unq'); tauto.
  - pose proof (bor_local_step_preserves_contains Ex Step) as ExPost'.
    pose proof (bor_local_step_preserves_determined_easy Ex Unq Step) as [it' [UnqPost' Eq]]; subst; simpl in UnqPost'.
    rewrite <- (tree_determined_unify ExPost' UnqPost' Unq'); tauto.
Qed.

Lemma protected_during_seq_always_stays_active
  {affected_tag tr cids evts tr' cid cids' prot pre z}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_item_determined affected_tag pre tr)
  (Prot : iprot pre = prot)
  (Call : protector_is_for_call cid prot)
  (StartsActive : item_perm_at_loc pre z = Active)
  (Seq : bor_local_seq
    {|seq_inv:=fun tr cids =>
      (forall it, tree_item_determined affected_tag it tr -> initialized (item_lazy_perm_at_loc it z) = PermInit)
      /\ call_is_active cid cids|}
    tr cids evts tr' cids')
  : bor_local_seq
    {|seq_inv:=fun tr _ => forall it, tree_item_determined affected_tag it tr -> perm (item_lazy_perm_at_loc it z) = Active|}
    tr cids evts tr' cids'.
Proof.
  pose proof (bor_local_seq_always_contains Ex (bor_local_seq_forget Seq)) as AllEx.
  pose proof (bor_local_seq_always_determined Ex Unq Prot AllEx) as AllUnq.
  pose proof (seq_always_merge AllEx (seq_always_merge Seq AllUnq)) as AllExUnqInitProt.
  eapply seq_always_build_forward; [| |exact AllExUnqInitProt].
  + move=> it Unq'. pose proof (tree_determined_unify Ex Unq Unq'); subst. assumption.
  + generalize Call; clear; simpl; move=> Call ????? Step [Ex [[Init CallAct] [?[Unq ProtEq]]]] Act.
    move=> ? Unq'.
    subst.
    eapply protected_during_step_stays_active; eauto.
    eexists; split; eauto.
Qed.

Lemma protected_during_seq_last_stays_active
  {affected_tag tr cids evts tr' cids' cid prot pre z}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_item_determined affected_tag pre tr)
  (Prot : iprot pre = prot)
  (Call : protector_is_for_call cid prot)
  (StartsActive : item_perm_at_loc pre z = Active)
  (Seq : bor_local_seq
    {|seq_inv:=fun tr cids =>
      (forall it, tree_item_determined affected_tag it tr -> initialized (item_lazy_perm_at_loc it z) = PermInit)
      /\ call_is_active cid cids|}
    tr cids evts tr' cids')
  : forall post, tree_item_determined affected_tag post tr' -> perm (item_lazy_perm_at_loc post z) = Active.
Proof.
  pose proof (seq_always_destruct_last (protected_during_seq_always_stays_active Ex Unq Prot Call StartsActive Seq)).
  assumption.
Qed.

Lemma apply_access_perm_protected_initialized_preserves_nondis
  {pre post kind rel}
  (Access : apply_access_perm kind rel true pre = Some post)
  : (initialized pre) = PermInit -> ~reach Disabled (perm pre) -> ~reach Disabled (perm post).
Proof.
  destruct kind, rel.
  all: destruct pre as [[][[][]| | |]].
  all: inversion Access.
  (* all cases easy *)
  all: simpl; auto.
  all: intro H; inversion H.
Qed.

Lemma memory_access_protected_initialized_preserves_nondis
  {access_tag affected_tag pre tr post tr' kind cids range z zpre zpost}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_item_determined affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind cids access_tag range tr = Some tr')
  (UnqAff' : tree_item_determined affected_tag post tr')
  (Prot : protector_is_active (iprot pre) cids)
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (ItemPost : item_lazy_perm_at_loc post z = zpost)
  (Init : initialized zpre = PermInit)
  : ~reach Disabled (perm zpre) -> ~reach Disabled (perm zpost).
Proof.
  destruct (apply_access_spec_per_node ExAff UnqAff Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_determined_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ Prot Init post _ Access _.
  option step in Access as ?:Foreach.
  injection Access; intros e; subst; clear Access.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc /item_lookup; simpl.
  rewrite bool_decide_eq_true_2 in Spec; [|assumption].
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_protected_initialized_preserves_nondis.
    + rewrite Lkup; simpl. exact Apply.
    + assumption.
  - rewrite Spec; tauto.
Qed.

Lemma protected_during_step_stays_nondis
  {affected_tag tr cids evt tr' cids' pre z zpre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_item_determined affected_tag pre tr)
  (Prot : protector_is_active (iprot pre) cids)
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (Init : initialized zpre = PermInit)
  (NonDisPre : ~reach Disabled (perm zpre))
  (Step : bor_local_step tr cids evt tr' cids')
  : forall post, tree_item_determined affected_tag post tr' -> ~reach Disabled (item_perm_at_loc post z).
Proof.
  move=> ? Unq'.
  inversion Step as [???? EXISTS_TAG ACC| | |?? tg???? FRESH_CHILD ? RETAG_EFFECT]; subst.
  - apply (memory_access_protected_initialized_preserves_nondis Ex Unq EXISTS_TAG ACC Unq' Prot eq_refl eq_refl Init NonDisPre).
  - rewrite <- (tree_determined_unify Ex Unq Unq'); tauto.
  - rewrite <- (tree_determined_unify Ex Unq Unq'); tauto.
  - pose proof (bor_local_step_preserves_contains Ex Step) as ExPost'.
    pose proof (bor_local_step_preserves_determined_easy Ex Unq Step) as [it' [UnqPost' Eq]]; subst; simpl in UnqPost'.
    rewrite <- (tree_determined_unify ExPost' UnqPost' Unq'); tauto.
Qed.

Lemma protected_during_seq_always_stays_nondis
  {affected_tag tr cids evts tr' cid cids' prot pre z}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_item_determined affected_tag pre tr)
  (Prot : iprot pre = prot)
  (Call : protector_is_for_call cid prot)
  (StartsNonDis : ~reach Disabled (item_perm_at_loc pre z))
  (Seq : bor_local_seq
    {|seq_inv:=fun tr cids =>
      (forall it, tree_item_determined affected_tag it tr -> initialized (item_lazy_perm_at_loc it z) = PermInit)
      /\ call_is_active cid cids|}
    tr cids evts tr' cids')
  : bor_local_seq
    {|seq_inv:=fun tr _ => forall it, tree_item_determined affected_tag it tr -> ~reach Disabled (perm (item_lazy_perm_at_loc it z))|}
    tr cids evts tr' cids'.
Proof.
  pose proof (bor_local_seq_always_contains Ex (bor_local_seq_forget Seq)) as AllEx.
  pose proof (bor_local_seq_always_determined Ex Unq Prot AllEx) as AllUnq.
  pose proof (seq_always_merge AllEx (seq_always_merge Seq AllUnq)) as AllExUnqInitProt.
  eapply seq_always_build_forward; [| |exact AllExUnqInitProt].
  + move=> it Unq'. pose proof (tree_determined_unify Ex Unq Unq'); subst. assumption.
  + generalize Call; clear; simpl; move=> Call ????? Step [Ex [[Init CallAct] [?[Unq ProtEq]]]] Act.
    move=> ? Unq'.
    subst.
    eapply protected_during_step_stays_nondis; eauto.
    eexists; split; eauto.
Qed.

Lemma protected_during_seq_last_stays_nondis
  {affected_tag tr cids evts tr' cids' cid prot pre z}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_item_determined affected_tag pre tr)
  (Prot : iprot pre = prot)
  (Call : protector_is_for_call cid prot)
  (StartsNonDis : ~reach Disabled (item_perm_at_loc pre z))
  (Seq : bor_local_seq
    {|seq_inv:=fun tr cids =>
      (forall it, tree_item_determined affected_tag it tr -> initialized (item_lazy_perm_at_loc it z) = PermInit)
      /\ call_is_active cid cids|}
    tr cids evts tr' cids')
  : forall post, tree_item_determined affected_tag post tr' -> ~reach Disabled (perm (item_lazy_perm_at_loc post z)).
Proof.
  pose proof (seq_always_destruct_last (protected_during_seq_always_stays_nondis Ex Unq Prot Call StartsNonDis Seq)).
  assumption.
Qed.

(* For bor_seq

== Preservation lemmas ==
[X] contains
[X] determined (quantified)
[X] reach, unreach
[X] when protected: stays active, stays frozen
[X] stays initialized

== Lookahead lemmas ==
[ ] future EndCall implies call currently active
[ ] future retag implies currently fresh
[ ] future retag implies parent exists

== Other lemmas ==
[X] split/merge list manipulations

*)
