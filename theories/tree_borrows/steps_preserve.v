From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas bor_lemmas.
From iris.prelude Require Import options.

(*
Lemma trees_at_block_build (prop : tree item -> Prop) trs blk :
  forall tr,
  trs !! blk = Some tr ->
  prop tr ->
  trees_at_block prop trs blk.
Proof.
  move=> ? Eq ?.
  rewrite /trees_at_block.
  rewrite Eq; auto.
Qed.

Lemma trees_at_block_destruct (prop : tree item -> Prop) trs blk :
  trees_at_block prop trs blk ->
  exists tr,
  trs !! blk = Some tr
  /\ prop tr.
Proof.
  rewrite /trees_at_block.
  case_match; [eauto|intro Contra; inversion Contra].
Qed.

Lemma trees_at_block_project (prop : tree item -> Prop) trs blk :
  forall tr,
  trees_at_block prop trs blk ->
  trs !! blk = Some tr ->
  prop tr.
Proof.
  rewrite /trees_at_block.
  move=> ? H H'.
  rewrite H' in H.
  assumption.
Qed.

Lemma trees_at_block_project_neg (prop : tree item -> Prop) trs blk :
  forall tr,
  ~trees_at_block prop trs blk ->
  trs !! blk = Some tr ->
  ~prop tr.
Proof.
  rewrite /trees_at_block.
  move=> ? H H'.
  rewrite H' in H.
  assumption.
Qed.

Lemma trees_at_block_insert (prop : tree item -> Prop) trs blk tr' :
  prop tr' ->
  trees_at_block prop (<[blk := tr']>trs) blk.
Proof.
  move=> ?.
  rewrite /trees_at_block lookup_insert.
  assumption.
Qed.

Lemma trees_at_block_insert_ne (prop : tree item -> Prop) trs blk :
  forall blk' tr',
  blk' ≠ blk ->
  trees_at_block prop trs blk <-> trees_at_block prop (<[blk' := tr']>trs) blk.
Proof.
  move=> ?? Ne.
  rewrite /trees_at_block lookup_insert_ne; [|auto].
  reflexivity.
Qed.
*)

Lemma access_eqv_strict_rel t t' (tr tr':tree item) :
  forall fn cids tg range dyn_rel,
  app_preserves_tag fn ->
  tree_apply_access fn cids tg range tr dyn_rel = Some tr' ->
  StrictParentChildIn t t' tr <-> StrictParentChildIn t t' tr'.
Proof.
  move=> ????? Preserves Access.
  eapply join_map_eqv_strict_rel; [|exact Access].
  move=> ??.
  apply Preserves.
Qed.

Lemma access_eqv_rel t t' (tr tr':tree item) :
  forall fn cids tg range dyn_rel,
  app_preserves_tag fn ->
  tree_apply_access fn cids tg range tr dyn_rel = Some tr' ->
  ParentChildIn t t' tr <-> ParentChildIn t t' tr'.
Proof.
  move=> ????? Preserves Access.
  unfold ParentChildIn.
  rewrite access_eqv_strict_rel; [|exact Preserves|exact Access].
  tauto.
Qed.

Lemma item_apply_access_preserves_tag kind strong :
  app_preserves_tag (item_apply_access kind strong).
Proof.
  move=> ??? it it'.
  unfold item_apply_access.
  destruct (permissions_foreach); simpl; [|intro H; inversion H].
  intro H; injection H; intros; subst.
  simpl; reflexivity.
Qed.

Lemma item_apply_access_preserves_prot kind strong :
  forall it it' cids rel range, item_apply_access kind strong cids rel range it = Some it' -> iprot it = iprot it'.
Proof.
  move=> ?????.
  unfold item_apply_access.
  destruct (permissions_foreach); simpl; [|intro H; inversion H].
  intro H; injection H; intros; subst.
  simpl; reflexivity.
Qed.

Lemma access_preserves_tags tr tg :
  forall tr' tg' app cids range dyn_rel,
  app_preserves_tag app ->
  tree_apply_access app cids tg' range tr dyn_rel = Some tr' ->
  tree_contains tg tr <-> tree_contains tg tr'.
Proof.
  move=> tr' tg' app ??? Preserve Access.
  unfold tree_apply_access in Access.
  unfold tree_contains in *.
  rewrite (join_project_exists _ _ tr').
  2: exact Access.
  rewrite exists_node_map.
  unfold compose.
  pose proof (proj1 (join_success_condition (map_nodes _ tr)) (mk_is_Some _ _ Access)).
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
      unfold IsTag in *; subst.
      symmetry.
      apply (Preserve _ _ _ _ _ App).
  * eapply exists_node_increasing.
    - exact Contains.
    - rewrite every_node_eqv_universal.
      intros x Exists xspec.
      destruct xspec as [v App].
      destruct App.
      unfold IsTag in *; subst.
      apply (Preserve _ _ _ _ _ H0).
Qed.

Lemma insertion_preserves_tags tr tg :
  forall tgp tgc cids tr' newp,
  tree_contains tg tr ->
  create_child cids tgp tgc newp tr = Some tr' ->
  tree_contains tg tr'.
Proof.
  move=> ??? tr' ? Contains CreateChild.
  unfold tree_contains in *.
  pose proof (create_child_isSome tr _ _ _ _ _ CreateChild) as Insert.
  rewrite Insert.
  apply insert_preserves_exists.
  exact Contains.
Qed.

Lemma insertion_minimal_tags tr tg :
  forall tgp tgc cids tr' newp,
  tgc ≠ tg ->
  tree_contains tg tr' ->
  create_child cids tgp tgc newp tr = Some tr' ->
  tree_contains tg tr.
Proof.
  move=> ????? Ne Contains CreateChild.
  unfold tree_contains in *.
  pose proof (create_child_isSome tr _ _ _ _ _ CreateChild) as Insert.
  all: rewrite Insert in Contains.
  eapply insert_false_infer_exists; [|exact Contains].
  rewrite /IsTag; simpl; assumption.
Qed.

Lemma apply_access_spec_per_node tr affected_tag access_tag pre:
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag pre tr ->
  forall fn cids range tr' dyn_rel,
  app_preserves_tag fn ->
  tree_apply_access fn cids access_tag range tr dyn_rel = Some tr' ->
  exists post,
    Some post = fn cids (if dyn_rel pre.(itag) access_tag then AccessChild else AccessForeign) range pre
    /\ tree_contains affected_tag tr'
    /\ tree_unique affected_tag post tr'.
Proof.
  intros Contains Contains' TgSpec fn cids range tr' dyn_rel FnPreservesTag Success.
  (* Grab the success condition of every node separately *)
  pose proof (proj1 (join_success_condition _) (mk_is_Some _ _ Success)) as SuccessCond.
  rewrite every_node_map in SuccessCond; rewrite every_node_eqv_universal in SuccessCond.
  pose proof (exists_unique_exists _ _ _ Contains' TgSpec) as Expre.
  pose proof (SuccessCond pre Expre) as [post SpecPost].
  unfold tree_unique in TgSpec. rewrite every_node_eqv_universal in TgSpec.
  (* Now do some transformations to get to the node level *)
  unfold tree_unique.
  exists post.
  split; [symmetry; auto|].
  split; [rewrite <- (access_preserves_tags _ _ _ _ _ _ _ _ FnPreservesTag Success); exact Contains'|].
  rewrite join_project_every; [|exact Success].
  rewrite every_node_map.
  unfold compose.
  rewrite every_node_eqv_universal.
  intros n Exn.
  destruct (decide (IsTag affected_tag n)).
  * pose proof (TgSpec n Exn) as PerNodeEqual.
    clear Success Contains SuccessCond TgSpec Contains' Exn.
    exists post.
    split; [|tauto].
    rewrite PerNodeEqual; auto.
  * pose proof (SuccessCond n Exn) as NodeSuccess.
    destruct NodeSuccess as [post' post'Spec].
    exists post'.
    unfold IsTag; rewrite <- (FnPreservesTag _ _ _ _ _ post'Spec).
    split; [|tauto].
    exact post'Spec.
Qed.

Lemma bor_local_step_preserves_contains
  tg tr
  (Ex : tree_contains tg tr)
  tr' cids cids' evt
  (Step : bor_local_step
    tr cids
    evt
    tr' cids')
  : tree_contains tg tr'.
Proof.
  inversion Step; subst.
  - (* Access *)
    rewrite <- access_preserves_tags; [eassumption| |exact ACC].
    eapply item_apply_access_preserves_tag.
  - (* InitCall *) assumption.
  - (* EndCall *) assumption.
  - (* Retag *)
    eapply insertion_preserves_tags; eauto.
Qed.
Arguments bor_local_step_preserves_contains {_ _} Ex {_ _ _ _} Step.

Lemma bor_local_step_retag_produces_contains_unique
  tgp tg tr tr' cids cids' newp cid
  (Step : bor_local_step
    tr cids
    (RetagBLEvt tgp tg newp cid)
    tr' cids')
  : tree_contains tg tr'
  /\ tree_unique tg (create_new_item tg newp) tr'.
Proof.
  inversion Step; subst.
  split.
  - eapply insertion_contains; eauto.
  - injection RETAG_EFFECT; intros; subst.
    eapply inserted_unique; [apply new_item_has_tag|].
    assumption.
Qed.
Arguments bor_local_step_retag_produces_contains_unique {_ _ _ _ _ _ _ _} Step.

(* This lemma does not handle the complicated case of an access in the same block as blk.
   See bor_estep_access_spec. *)
Lemma bor_local_step_preserves_unique_easy
  tg tr it tr'
  (Ex : tree_contains tg tr)
  (Unq : tree_unique tg it tr)
  cids cids' evt
  (Step : bor_local_step
    tr cids
    evt
    tr' cids')
  : exists it',
  tree_unique tg it' tr'
  /\ match evt with
  | AccessBLEvt _ _ _ _ => iprot it = iprot it'
  | InitCallBLEvt _
  | EndCallBLEvt _
  | RetagBLEvt _ _ _ _
  | SilentBLEvt => it = it'
  end.
Proof.
  inversion Step; subst.
  - (* Access *)
    destruct (apply_access_spec_per_node _ _ _ _ EXISTS_TAG Ex Unq _ _ _ _ _ (item_apply_access_preserves_tag _ _) ACC) as [?[Spec[_?]]].
    eexists; split; eauto.
    symmetry in Spec. eapply item_apply_access_preserves_prot; exact Spec.
  - eexists; split; [|reflexivity]; assumption.
  - eexists; split; [|reflexivity]; assumption.
  - (* Retag *)
    eexists; split; [|reflexivity].
    eapply create_child_preserves_unique; [|exact Unq|exact RETAG_EFFECT].
    intro; subst. destruct (FRESH_CHILD Ex).
Qed.
Arguments bor_local_step_preserves_unique_easy {_ _ _ _} Ex Unq {_ _ _} Step.

Lemma bor_local_step_eqv_rel
  {tg tg' tr tr' cids cids' evt}
  (Ex : tree_contains tg tr)
  (Ex' : tree_contains tg' tr)
  (Step : bor_local_step
    tr cids
    evt
    tr' cids')
  : ParentChildIn tg tg' tr <-> ParentChildIn tg tg' tr'.
Proof.
  inversion Step; subst.
  all: try tauto.
  - (* Access *)
    rewrite access_eqv_rel; [|apply item_apply_access_preserves_tag|apply ACC].
    tauto.
  - (* Retag *)
    injection RETAG_EFFECT; intros; subst.
    rewrite <- insert_eqv_rel.
    * tauto.
    * rewrite /IsTag new_item_has_tag; intro; subst; destruct (FRESH_CHILD Ex).
    * rewrite /IsTag new_item_has_tag; intro; subst; destruct (FRESH_CHILD Ex').
Qed.

Lemma bor_local_step_retag_produces_rel
  {tgp tg tr tr' cids cids' newp cid}
  (Step : bor_local_step
    tr cids
    (RetagBLEvt tgp tg newp cid)
    tr' cids')
  : ParentChildIn tgp tg tr'.
Proof.
  inversion Step; subst.
  injection RETAG_EFFECT; intros; subst.
  eapply insert_produces_ParentChild.
  * eapply new_item_has_tag.
  * intro; subst; destruct (FRESH_CHILD EXISTS_PARENT).
Qed.

Lemma bor_local_step_retag_order_nonparent
  {tgp tg tg' tr tr' cids cids' newp cid}
  (Ex' : tree_contains tg' tr)
  (Step : bor_local_step
    tr cids
    (RetagBLEvt tgp tg newp cid)
    tr' cids')
  : ~ParentChildIn tg tg' tr'.
Proof.
  inversion Step; subst.
  injection RETAG_EFFECT; intros; subst.
  eapply insertion_order_nonparent.
  - exact Ex'.
  - exact FRESH_CHILD.
  - exact EXISTS_PARENT.
  - exact RETAG_EFFECT.
Qed.

Lemma apply_access_perm_preserves_backward_reach
  {pre post kind rel b b' p0}
  (Access : apply_access_perm kind rel b b' pre = Some post)
  : reach p0 (perm pre) -> reach p0 (perm post).
Proof.
  destruct b, b', kind, rel.
  all: destruct pre, initialized, perm.
  all: destruct p0.
  all: inversion Access.
  (* all cases easy *)
  all: intro H; inversion H.
  all: auto.
Qed.

Lemma apply_access_perm_preserves_forward_unreach
  {pre post kind rel b b' p0}
  (Access : apply_access_perm kind rel b b' pre = Some post)
  : ~reach (perm pre) p0 -> ~reach (perm post) p0.
Proof.
  destruct b, b', kind, rel.
  all: destruct pre, initialized, perm.
  all: destruct p0.
  all: inversion Access.
  (* all cases easy *)
  all: intros H H'; apply H; inversion H'.
  all: auto.
Qed.

(* Preservation of reachability *)
Lemma memory_access_preserves_backward_reach
  {access_tag affected_tag pre tr post tr' kind strong cids range p0 z}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_unique affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind strong cids access_tag range tr = Some tr')
  (UnqAff' : tree_unique affected_tag post tr')
  : reach p0 (item_perm_at_loc pre z) -> reach p0 (item_perm_at_loc post z).
Proof.
  destruct (apply_access_spec_per_node _ _ _ _ ExAcc ExAff UnqAff _ _ _ _ _ (item_apply_access_preserves_tag _ _) Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_unique_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ post _ Access _.
  symmetry in Access; destruct (option_bind_success_step _ _ _ Access) as [?[Foreach Access']]; clear Access.
  injection Access'; intros e; subst; clear Access'.
  pose proof (range_foreach_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc; simpl.
  destruct (decide (range_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_preserves_backward_reach.
    rewrite Lkup; simpl. exact Apply.
  - rewrite Spec; tauto.
Qed.

Lemma memory_access_preserves_forward_unreach
  {access_tag affected_tag pre tr post tr' kind strong cids range p0 z}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_unique affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind strong cids access_tag range tr = Some tr')
  (UnqAff' : tree_unique affected_tag post tr')
  : ~reach (item_perm_at_loc pre z) p0 -> ~reach (item_perm_at_loc post z) p0.
Proof.
  destruct (apply_access_spec_per_node _ _ _ _ ExAcc ExAff UnqAff _ _ _ _ _ (item_apply_access_preserves_tag _ _) Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_unique_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ post _ Access _.
  symmetry in Access; destruct (option_bind_success_step _ _ _ Access) as [?[Foreach Access']]; clear Access.
  injection Access'; intros e; subst; clear Access'.
  pose proof (range_foreach_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc; simpl.
  destruct (decide (range_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_preserves_forward_unreach.
    rewrite Lkup; simpl. exact Apply.
  - rewrite Spec; tauto.
Qed.

Lemma bor_local_step_preserves_backward_reach
  {tg tr tr' cids cids' pre post evt p0 z}
  (Ex : tree_contains tg tr)
  (UnqPre : tree_unique tg pre tr)
  (Step : bor_local_step tr cids evt tr' cids')
  (UnqPost : tree_unique tg post tr')
  : reach p0 (item_perm_at_loc pre z) -> reach p0 (item_perm_at_loc post z).
Proof.
  inversion Step; subst.
  - apply (memory_access_preserves_backward_reach Ex UnqPre EXISTS_TAG ACC UnqPost).
  - rewrite (tree_unique_unify Ex UnqPre UnqPost); tauto.
  - rewrite (tree_unique_unify Ex UnqPre UnqPost); tauto.
  - pose proof (bor_local_step_preserves_contains Ex Step) as ExPost'.
    pose proof (bor_local_step_preserves_unique_easy Ex UnqPre Step) as [it' [UnqPost' Eq]]; subst; simpl in UnqPost'.
    rewrite (tree_unique_unify ExPost' UnqPost' UnqPost); tauto.
Qed.

Lemma bor_local_step_preserves_forward_unreach
  {tg tr tr' cids cids' pre post evt p0 z}
  (Ex : tree_contains tg tr)
  (UnqPre : tree_unique tg pre tr)
  (Step : bor_local_step tr cids evt tr' cids')
  (UnqPost : tree_unique tg post tr')
  : ~reach (item_perm_at_loc pre z) p0 -> ~reach (item_perm_at_loc post z) p0.
Proof.
  inversion Step; subst.
  - apply (memory_access_preserves_forward_unreach Ex UnqPre EXISTS_TAG ACC UnqPost).
  - rewrite (tree_unique_unify Ex UnqPre UnqPost); tauto.
  - rewrite (tree_unique_unify Ex UnqPre UnqPost); tauto.
  - pose proof (bor_local_step_preserves_contains Ex Step) as ExPost'.
    pose proof (bor_local_step_preserves_unique_easy Ex UnqPre Step) as [it' [UnqPost' Eq]]; subst; simpl in UnqPost'.
    rewrite (tree_unique_unify ExPost' UnqPost' UnqPost); tauto.
Qed.

Lemma seq_always_build_forward
  {Ptr INVtr : tree item -> Prop}
  {Pcids INVcids : call_id_set -> Prop}
  {tr cids evts tr' cids'}
  (PTR0 : Ptr tr)
  (PCID0 : Pcids cids)
  (Preserve : forall tr cids tr' cids' evt,
    bor_local_step tr cids evt tr' cids' ->
    Ptr tr -> Pcids cids ->
    INVtr tr -> INVcids cids ->
    Ptr tr' /\ Pcids cids'
  )
  (Seq : bor_local_seq INVtr INVcids tr cids evts tr' cids')
  : bor_local_seq Ptr Pcids tr cids evts tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent tr'.
  generalize dependent cids.
  generalize dependent cids'.
  induction evts; move=> ?????? Seq; inversion Seq; subst.
  - constructor; assumption.
  - econstructor; eauto.
    destruct (Preserve _ _ _ _ _ HEAD) as [??]; try assumption.
    eapply IHevts; auto.
Qed.

Lemma seq_always_destruct_first
  {Ptr : tree item -> Prop}
  {Pcids : call_id_set -> Prop}
  {tr cids evts tr' cids'}
  (Seq : bor_local_seq Ptr Pcids tr cids evts tr' cids')
  : Ptr tr /\ Pcids cids.
Proof. inversion Seq; subst; split; assumption. Qed.

Lemma seq_always_destruct_last
  {Ptr : tree item -> Prop}
  {Pcids : call_id_set -> Prop}
  {tr cids evts tr' cids'}
  (Seq : bor_local_seq Ptr Pcids tr cids evts tr' cids')
  : Ptr tr' /\ Pcids cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction evts; move=> ?? Seq; inversion Seq; subst.
  - split; assumption.
  - eapply IHevts; eauto.
Qed.

Lemma bor_local_step_deterministic
  {tr cids evt tr1 cids1 tr2 cids2}
  (Step1 : bor_local_step tr cids evt tr1 cids1)
  (Step2 : bor_local_step tr cids evt tr2 cids2)
  : tr1 = tr2 /\ cids1 = cids2.
Proof.
  destruct evt; inversion Step1; inversion Step2; subst.
  - rewrite ACC in ACC0; injection ACC0; tauto.
  - tauto.
  - tauto.
  - rewrite RETAG_EFFECT in RETAG_EFFECT0; injection RETAG_EFFECT0; tauto.
Qed.

Lemma bor_local_seq_deterministic
  {tr cids evts tr1 cids1 tr2 cids2}
  (Seq1 : bor_local_seq ignore ignore tr cids evts tr1 cids1)
  (Seq2 : bor_local_seq ignore ignore tr cids evts tr2 cids2)
  : tr1 = tr2 /\ cids1 = cids2.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  generalize dependent tr1.
  generalize dependent cids1.
  generalize dependent tr2.
  generalize dependent cids2.
  induction evts; move=> ?????? Seq1 Seq2; inversion Seq1; inversion Seq2; subst.
  - tauto.
  - pose proof (bor_local_step_deterministic HEAD HEAD0) as [??]; subst.
    eapply IHevts; eauto.
Qed.

Lemma ignore_always_True {T} : forall (t:T), ignore t.
Proof. rewrite /ignore; tauto. Qed.

Lemma bor_local_seq_forget
  {Ptr Pcids tr cids evts tr' cids'}
  (Seq : bor_local_seq Ptr Pcids tr cids evts tr' cids')
  : bor_local_seq ignore ignore tr cids evts tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction evts; move=> ?? Seq; inversion Seq; subst.
  - constructor; apply ignore_always_True.
  - econstructor; [apply ignore_always_True|apply ignore_always_True|exact HEAD|].
    eapply IHevts; assumption.
Qed.

Lemma seq_always_merge
  {tr cids evts tr' cids'}
  {Ptr1 Ptr2 : tree item -> Prop}
  {Pcids1 Pcids2 : call_id_set -> Prop}
  (Seq1 : bor_local_seq Ptr1 Pcids1 tr cids evts tr' cids')
  (Seq2 : bor_local_seq Ptr2 Pcids2 tr cids evts tr' cids')
  : bor_local_seq (fun tr => Ptr1 tr /\ Ptr2 tr) (fun cids => Pcids1 cids /\ Pcids2 cids) tr cids evts tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction evts; move=> ?? Seq1 Seq2; inversion Seq1; inversion Seq2; subst.
  - constructor; split; assumption.
  - pose proof (bor_local_step_deterministic HEAD HEAD0) as [??]; subst.
    pose proof (bor_local_seq_deterministic (bor_local_seq_forget REST) (bor_local_seq_forget REST0)) as [??]; subst.
    econstructor; eauto.
Qed.

Lemma bor_local_seq_always_contains
  {tg tr cids tr' cids' evts}
  (Ex : tree_contains tg tr)
  (Seq : bor_local_seq ignore ignore tr cids evts tr' cids')
  : bor_local_seq (tree_contains tg) ignore tr cids evts tr' cids'.
Proof.
  eapply seq_always_build_forward; [assumption|apply ignore_always_True| |exact Seq].
  clear.
  move=> ????? Step Ex _; split; [|apply ignore_always_True].
  eapply bor_local_step_preserves_contains; eassumption.
Qed.

Lemma bor_local_seq_last_contains
  {tg tr cids tr' cids' evts}
  (Ex : tree_contains tg tr)
  (Seq : bor_local_seq ignore ignore tr cids evts tr' cids')
  : tree_contains tg tr'.
Proof.
  destruct (seq_always_destruct_last (bor_local_seq_always_contains Ex Seq)) as [??].
  assumption.
Qed.

Lemma bor_local_seq_always_unique
  {tg tr tr' prot cids cids' evts pre}
  (Ex : tree_contains tg tr)
  (Unq : tree_unique tg pre tr)
  (ProtEq : iprot pre = prot)
  (Seq : bor_local_seq (tree_contains tg) ignore tr cids evts tr' cids')
  : bor_local_seq (fun tr => exists it, tree_unique tg it tr /\ iprot it = prot) ignore tr cids evts tr' cids'.
Proof.
  eapply seq_always_build_forward; [|apply ignore_always_True| |exact Seq].
  - eexists; split; eassumption.
  - clear. move=> ???? evt Step [?[Unq Prot]] _ Ex _.
    split; [|apply ignore_always_True].
    destruct (bor_local_step_preserves_unique_easy Ex Unq Step) as [?[??]].
    eexists.
    split; [eassumption|].
    destruct evt; subst; auto.
Qed.

Lemma bor_local_seq_last_unique
  {tg tr tr' cids cids' evts pre}
  (Ex : tree_contains tg tr)
  (Unq : tree_unique tg pre tr)
  (Seq : bor_local_seq ignore ignore tr cids evts tr' cids')
  : exists post, tree_unique tg post tr' /\ iprot pre = iprot post.
Proof.
  pose proof (bor_local_seq_always_contains Ex Seq) as AllEx.
  destruct (seq_always_destruct_last (bor_local_seq_always_unique Ex Unq eq_refl AllEx)) as [[?[??]]?].
  eexists; split; subst; eauto.
Qed.

Lemma bor_local_seq_always_rel
  {tg tg' tr tr' cids cids' evts}
  (Rel : ParentChildIn tg tg' tr)
  (Ex : tree_contains tg tr)
  (Ex' : tree_contains tg' tr)
  (Seq : bor_local_seq ignore ignore tr cids evts tr' cids')
  : bor_local_seq (ParentChildIn tg tg') ignore tr cids evts tr' cids'.
Proof.
  pose proof (seq_always_merge
    (bor_local_seq_always_contains Ex Seq)
    (bor_local_seq_always_contains Ex' Seq)) as AllExEx'.
  eapply seq_always_build_forward; [assumption|apply ignore_always_True| |exact AllExEx'].
  clear; simpl; move=> ????? Step Rel _ [Ex Ex'] _.
  split; [|apply ignore_always_True].
  rewrite <- (bor_local_step_eqv_rel Ex Ex' Step).
  assumption.
Qed.

Lemma bor_local_seq_always_unrel
  {tg tg' tr tr' cids cids' evts}
  (Rel : ~ParentChildIn tg tg' tr)
  (Ex : tree_contains tg tr)
  (Ex' : tree_contains tg' tr)
  (Seq : bor_local_seq ignore ignore tr cids evts tr' cids')
  : bor_local_seq (compose not (ParentChildIn tg tg')) ignore tr cids evts tr' cids'.
Proof.
  pose proof (seq_always_merge
    (bor_local_seq_always_contains Ex Seq)
    (bor_local_seq_always_contains Ex' Seq)) as AllExEx'.
  eapply seq_always_build_forward; [assumption|apply ignore_always_True| |exact AllExEx'].
  clear; simpl; move=> ????? Step Rel _ [Ex Ex'] _.
  split; [|apply ignore_always_True].
  rewrite <- (bor_local_step_eqv_rel Ex Ex' Step).
  assumption.
Qed.

Lemma bor_local_seq_last_eqv_rel
  {tg tg' tr tr' cids cids' evts}
  (Ex : tree_contains tg tr)
  (Ex' : tree_contains tg' tr)
  (Seq : bor_local_seq ignore ignore tr cids evts tr' cids')
  : ParentChildIn tg tg' tr <-> ParentChildIn tg tg' tr'.
Proof.
  destruct (decide (ParentChildIn tg tg' tr)) as [Rel|Unrel].
  - destruct (seq_always_destruct_last (bor_local_seq_always_rel Rel Ex Ex' Seq)).
    tauto.
  - destruct (seq_always_destruct_last (bor_local_seq_always_unrel Unrel Ex Ex' Seq)).
    simpl in *.
    tauto.
Qed.

Lemma bor_local_seq_always_backward_reach
  {tg tr tr' cids cids' pre evts p0 z}
  (Ex : tree_contains tg tr)
  (Unq : tree_unique tg pre tr)
  (Reach : reach p0 (item_perm_at_loc pre z))
  (Seq : bor_local_seq ignore ignore tr cids evts tr' cids')
  : bor_local_seq (fun tr => forall post (UnqPost : tree_unique tg post tr), reach p0 (item_perm_at_loc post z)) ignore
      tr cids evts tr' cids'.
Proof.
  pose proof (bor_local_seq_always_contains Ex Seq) as AllEx.
  pose proof (seq_always_merge AllEx (bor_local_seq_always_unique Ex Unq eq_refl AllEx)) as AllExUnq.
  eapply seq_always_build_forward; [|apply ignore_always_True| |exact AllExUnq].
  + move=> ? Unq'. pose proof (tree_unique_unify Ex Unq Unq'); subst. assumption.
  + clear; move=> ????? Step Reach _ [Ex [?[Unq _]]] _.
    split; [|apply ignore_always_True].
    move=> ? Unq'.
    eapply bor_local_step_preserves_backward_reach; eauto.
Qed.

Lemma bor_local_seq_last_backward_reach
  {tg tr tr' cids cids' pre evts p0 z}
  (Ex : tree_contains tg tr)
  (Unq : tree_unique tg pre tr)
  (Reach : reach p0 (item_perm_at_loc pre z))
  (Seq : bor_local_seq ignore ignore tr cids evts tr' cids')
  : forall post (UnqPost : tree_unique tg post tr'), reach p0 (item_perm_at_loc post z).
Proof.
  pose proof (seq_always_destruct_last (bor_local_seq_always_backward_reach Ex Unq Reach Seq)) as [??].
  assumption.
Qed.

Lemma bor_local_seq_always_forward_unreach
  {tg tr tr' cids cids' pre evts p0 z}
  (Ex : tree_contains tg tr)
  (Unq : tree_unique tg pre tr)
  (Unreach : ~reach (item_perm_at_loc pre z) p0)
  (Seq : bor_local_seq ignore ignore tr cids evts tr' cids')
  : bor_local_seq (fun tr => forall post (UnqPost : tree_unique tg post tr), ~reach (item_perm_at_loc post z) p0) ignore
      tr cids evts tr' cids'.
Proof.
  pose proof (bor_local_seq_always_contains Ex Seq) as AllEx.
  pose proof (seq_always_merge AllEx (bor_local_seq_always_unique Ex Unq eq_refl AllEx)) as AllExUnq.
  eapply seq_always_build_forward; [|apply ignore_always_True| |exact AllExUnq].
  + move=> ? Unq'. pose proof (tree_unique_unify Ex Unq Unq'); subst. assumption.
  + clear; move=> ????? Step Reach _ [Ex [?[Unq _]]] _.
    split; [|apply ignore_always_True].
    move=> ? Unq'.
    eapply bor_local_step_preserves_forward_unreach; eauto.
Qed.

Lemma bor_local_seq_last_forward_unreach
  {tg tr tr' cids cids' pre evts p0 z}
  (Ex : tree_contains tg tr)
  (Unq : tree_unique tg pre tr)
  (Unreach : ~reach (item_perm_at_loc pre z) p0)
  (Seq : bor_local_seq ignore ignore tr cids evts tr' cids')
  : forall post (UnqPost : tree_unique tg post tr'), ~reach (item_perm_at_loc post z) p0.
Proof.
  pose proof (seq_always_destruct_last (bor_local_seq_always_forward_unreach Ex Unq Unreach Seq)) as [??].
  assumption.
Qed.

Lemma bor_local_seq_split
  {Ptr Pcids tr tr' cids cids' l l'}
  : bor_local_seq Ptr Pcids tr cids (l ++ l') tr' cids'
  <-> exists tr'' cids'', bor_local_seq Ptr Pcids tr cids l tr'' cids'' /\ bor_local_seq Ptr Pcids tr'' cids'' l' tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction l; move=> ??.
  - simpl; split; intro Hyp.
    + eexists. eexists. split; [constructor|assumption].
      all: inversion Hyp; subst; auto.
    + destruct Hyp as [?[?[S S']]].
      inversion S; subst.
      exact S'.
  - simpl; split; intro Hyp.
    + inversion Hyp; subst.
      rewrite IHl in REST.
      destruct REST as [?[?[S' S'']]].
      eexists. eexists.
      split.
      * econstructor; [assumption|assumption|exact HEAD|exact S'].
      * assumption.
    + destruct Hyp as [?[?[S S']]].
      inversion S; subst.
      econstructor; [assumption|assumption|exact HEAD|].
      rewrite IHl.
      eexists. eexists.
      split; eassumption.
Qed.

Lemma apply_access_perm_protected_initialized_preserves_active
  {pre post kind rel}
  (Access : apply_access_perm kind rel true true pre = Some post)
  : (initialized pre) = PermInit -> (perm pre) = Active -> (perm post) = Active.
Proof.
  destruct kind, rel.
  all: destruct pre, initialized, perm.
  all: inversion Access.
  (* all cases easy *)
  all: simpl; auto.
  all: intros H H'; inversion H'; inversion H.
Qed.

Lemma memory_access_protected_initialized_preserves_active
  {access_tag affected_tag pre tr post tr' kind cids range z zpre zpost}
  (ExAff : tree_contains affected_tag tr)
  (UnqAff : tree_unique affected_tag pre tr)
  (ExAcc : tree_contains access_tag tr)
  (Access : memory_access kind ProtStrong cids access_tag range tr = Some tr')
  (UnqAff' : tree_unique affected_tag post tr')
  (Prot : protector_is_active (iprot pre) cids)
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (ItemPost : item_lazy_perm_at_loc post z = zpost)
  (Init : initialized zpre = PermInit)
  : perm zpre = Active -> perm zpost = Active.
Proof.
  destruct (apply_access_spec_per_node _ _ _ _ ExAcc ExAff UnqAff _ _ _ _ _ (item_apply_access_preserves_tag _ _) Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_unique_unify ExPost UnqPost UnqAff'); subst.
  (* now it's just bruteforce case analysis *)
  generalize dependent post.
  generalize dependent pre.
  clear. move=> pre _ Prot Init post _ Access _.
  symmetry in Access; destruct (option_bind_success_step _ _ _ Access) as [?[Foreach Access']]; clear Access.
  injection Access'; intros e; subst; clear Access'.
  pose proof (range_foreach_spec _ _ z _ _ Foreach) as Spec; clear Foreach.
  rewrite /item_perm_at_loc /item_lazy_perm_at_loc; simpl.
  rewrite bool_decide_eq_true_2 in Spec; [|assumption].
  rewrite bool_decide_eq_true_2 in Spec; [|left; reflexivity].
  destruct (decide (range_contains _ _)).
  - destruct Spec as [?[Lkup Apply]].
    eapply apply_access_perm_protected_initialized_preserves_active.
    + rewrite Lkup; simpl. exact Apply.
    + assumption.
  - rewrite Spec; tauto.
Qed.

Lemma protected_during_step_stays_active
  {affected_tag tr cids evt tr' cids' pre z zpre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Prot : protector_is_active (iprot pre) cids)
  (ItemPre : item_lazy_perm_at_loc pre z = zpre)
  (Init : initialized zpre = PermInit)
  (ActPre : perm zpre = Active)
  (Step : bor_local_step tr cids evt tr' cids')
  : forall post, tree_unique affected_tag post tr' -> item_perm_at_loc post z = Active.
Proof.
  move=> ? Unq'.
  inversion Step; subst.
  - apply (memory_access_protected_initialized_preserves_active Ex Unq EXISTS_TAG ACC Unq' Prot eq_refl eq_refl Init ActPre).
  - rewrite <- (tree_unique_unify Ex Unq Unq'); tauto.
  - rewrite <- (tree_unique_unify Ex Unq Unq'); tauto.
  - pose proof (bor_local_step_preserves_contains Ex Step) as ExPost'.
    pose proof (bor_local_step_preserves_unique_easy Ex Unq Step) as [it' [UnqPost' Eq]]; subst; simpl in UnqPost'.
    rewrite <- (tree_unique_unify ExPost' UnqPost' Unq'); tauto.
Qed.

Lemma protected_during_seq_always_stays_active
  {affected_tag tr cids evts tr' cids' prot pre z}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Prot : iprot pre = prot)
  (StartsActive : item_perm_at_loc pre z = Active)
  (Seq : bor_local_seq
    (fun tr => forall it, tree_unique affected_tag it tr -> initialized (item_lazy_perm_at_loc it z) = PermInit)
    (protector_is_active prot)
    tr cids evts tr' cids')
  : bor_local_seq
    (fun tr => forall it, tree_unique affected_tag it tr -> perm (item_lazy_perm_at_loc it z) = Active)
    ignore
    tr cids evts tr' cids'.
Proof.
  pose proof (bor_local_seq_always_contains Ex (bor_local_seq_forget Seq)) as AllEx.
  pose proof (bor_local_seq_always_unique Ex Unq Prot AllEx) as AllUnq.
  pose proof (seq_always_merge AllEx (seq_always_merge Seq AllUnq)) as AllExUnqInitProt.
  eapply seq_always_build_forward; [|apply ignore_always_True| |exact AllExUnqInitProt].
  + move=> it Unq'. pose proof (tree_unique_unify Ex Unq Unq'); subst. assumption.
  + clear; simpl; move=> ????? Step Act _ [Ex [Init [?[Unq ProtEq]]]] [_ [Prot _]].
    split; [|apply ignore_always_True].
    move=> ? Unq'.
    subst.
    eapply protected_during_step_stays_active; eauto.
Qed.

(* For bor_seq

== Preservation lemmas ==
[X] contains
[X] unique (quantified)
[X] reach, unreach
[ ] when protected: stays active, stays frozen
[ ] stays initialized

== Lookahead lemmas ==
[ ] future EndCall implies call currently active

== Other lemmas ==
[X] split/merge list manipulations

*)
