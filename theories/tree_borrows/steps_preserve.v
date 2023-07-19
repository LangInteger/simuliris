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
  | AccessBLEvt _ _ _ _ => True
  | InitCallBLEvt _
  | EndCallBLEvt _
  | RetagBLEvt _ _ _ _
  | SilentBLEvt => it = it'
  end.
Proof.
  inversion Step; subst.
  - (* Access *)
    destruct (apply_access_spec_per_node _ _ _ _ EXISTS_TAG Ex Unq _ _ _ _ _ (item_apply_access_preserves_tag _ _) ACC) as [?[_[_?]]].
    eexists; eauto.
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

Lemma bor_local_seq_preserves_contains
  {tg tr cids tr' cids' evts}
  (Ex : tree_contains tg tr)
  (Seq : bor_local_seq tr cids evts tr' cids')
  : tree_contains tg tr'.
Proof.
  generalize dependent tr'.
  generalize dependent tr.
  generalize dependent cids'.
  generalize dependent cids.
  induction evts; move=> ????? Seq; inversion Seq; subst.
  - assumption.
  - eapply IHevts; [|exact REST].
    eapply bor_local_step_preserves_contains; [|exact HEAD].
    assumption.
Qed.

Lemma bor_local_seq_preserves_unique
  {tg tr tr' cids cids' evts pre}
  (Ex : tree_contains tg tr)
  (Unq : tree_unique tg pre tr)
  (Seq : bor_local_seq tr cids evts tr' cids')
  : exists post, tree_unique tg post tr'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  generalize dependent pre.
  induction evts; move=> ??? Ex Unq Seq; inversion Seq; subst.
  - eexists. eassumption.
  - destruct (bor_local_step_preserves_unique_easy Ex Unq HEAD) as [?[Unq' _]].
    eapply IHevts; [| |exact REST].
    * eapply bor_local_step_preserves_contains; [|exact HEAD].
      assumption.
    * eassumption.
Qed.

Lemma bor_local_seq_eqv_rel
  {tg tg' tr tr' cids cids' evts}
  (Ex : tree_contains tg tr)
  (Ex' : tree_contains tg' tr)
  (Step : bor_local_seq
    tr cids
    evts
    tr' cids')
  : ParentChildIn tg tg' tr <-> ParentChildIn tg tg' tr'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction evts; move=> ??? Ex Seq; inversion Seq; subst.
  - tauto.
  - eapply iff_trans.
    * eapply bor_local_step_eqv_rel; eauto.
    * eapply IHevts; eauto.
      all: eapply bor_local_step_preserves_contains; eauto.
Qed.

Lemma bor_local_seq_preserves_backward_reach_aux
  {tg tr tr' cids cids' pre post evts p0 z}
  (Ex : tree_contains tg tr)
  (UnqPre : tree_unique tg pre tr)
  (Seq : bor_local_seq tr cids evts tr' cids')
  (UnqPost : tree_unique tg post tr')
  : reach p0 (item_perm_at_loc pre z) -> reach p0 (item_perm_at_loc post z).
Proof.
  generalize dependent tr.
  generalize dependent cids.
  generalize dependent post.
  generalize dependent pre.
  induction evts; move=> ?? UnqPost ?? Ex UnqPre Seq; inversion Seq; subst.
  - pose proof (tree_unique_unify Ex UnqPre UnqPost); subst; tauto.
  - destruct (bor_local_step_preserves_unique_easy Ex UnqPre HEAD) as [?[Unq' _]].
    eapply impl_transitive.
    * eapply bor_local_step_preserves_backward_reach; eauto.
    * eapply IHevts; [| | |exact REST]; eauto.
      eapply bor_local_step_preserves_contains; [|exact HEAD].
      assumption.
Qed.

(* Same lemma as above but rewritten in a form that makes it easier to manipulate
   when we only have access to a single Unq at a time *)
Lemma bor_local_seq_preserves_backward_reach
  {tg tr tr' cids cids' pre evts p0 z}
  (Ex : tree_contains tg tr)
  (UnqPre : tree_unique tg pre tr)
  (Seq : bor_local_seq tr cids evts tr' cids')
  (Reach : reach p0 (item_perm_at_loc pre z))
  : forall post (UnqPost : tree_unique tg post tr'), reach p0 (item_perm_at_loc post z).
Proof. intros. eapply bor_local_seq_preserves_backward_reach_aux; eauto. Qed.


Lemma bor_local_seq_preserves_forward_unreach_aux
  {tg tr tr' cids cids' pre post evts p0 z}
  (Ex : tree_contains tg tr)
  (UnqPre : tree_unique tg pre tr)
  (Seq : bor_local_seq tr cids evts tr' cids')
  (UnqPost : tree_unique tg post tr')
  : ~reach (item_perm_at_loc pre z) p0 -> ~reach (item_perm_at_loc post z) p0.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  generalize dependent post.
  generalize dependent pre.
  induction evts; move=> ?? UnqPost ?? Ex UnqPre Seq; inversion Seq; subst.
  - pose proof (tree_unique_unify Ex UnqPre UnqPost); subst; tauto.
  - destruct (bor_local_step_preserves_unique_easy Ex UnqPre HEAD) as [?[Unq' _]].
    eapply impl_transitive.
    * eapply bor_local_step_preserves_forward_unreach; eauto.
    * eapply IHevts; [| | |exact REST]; eauto.
      eapply bor_local_step_preserves_contains; [|exact HEAD].
      assumption.
Qed.

Lemma bor_local_seq_preserves_forward_unreach
  {tg tr tr' cids cids' pre evts p0 z}
  (Ex : tree_contains tg tr)
  (UnqPre : tree_unique tg pre tr)
  (Seq : bor_local_seq tr cids evts tr' cids')
  (Unreach : ~reach (item_perm_at_loc pre z) p0)
  : forall post (UnqPost : tree_unique tg post tr'), ~reach (item_perm_at_loc post z) p0.
Proof. intros. eapply bor_local_seq_preserves_forward_unreach_aux; eauto. Qed.

Lemma bor_local_seq_split
  {tr tr' cids cids' l l'}
  : bor_local_seq tr cids (l ++ l') tr' cids'
  <-> exists tr'' cids'', bor_local_seq tr cids l tr'' cids'' /\ bor_local_seq tr'' cids'' l' tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction l; move=> ??.
  - simpl; split; intro Hyp.
    + eexists. eexists. split; [constructor|assumption].
    + destruct Hyp as [?[?[S S']]].
      inversion S; subst.
      exact S'.
  - simpl; split; intro Hyp.
    + inversion Hyp; subst.
      rewrite IHl in REST.
      destruct REST as [?[?[S' S'']]].
      eexists. eexists.
      split.
      * econstructor; [exact HEAD|exact S'].
      * assumption.
    + destruct Hyp as [?[?[S S']]].
      inversion S; subst.
      econstructor; [exact HEAD|].
      rewrite IHl.
      eexists. eexists.
      split; eassumption.
Qed.

(* For bor_seq

== Preservation lemmas ==
[X] contains
[X] unique (quantified)
[X] reach, unreach

== Lookahead lemmas ==
[ ] future EndCall implies call currently active

== Other lemmas ==
[X] split/merge list manipulations

*)
