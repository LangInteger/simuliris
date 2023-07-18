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

(*
Lemma trees_unique_tag_preserved tg blk0 trs trs' :
  (forall blk, trees_contain tg trs blk <-> trees_contain tg trs' blk) ->
  trees_unique_tag tg trs blk0 ->
  trees_unique_tag tg trs' blk0.
Proof.
  move=> Pres Unqt blk'.
  rewrite <- Pres.
  apply Unqt.
Qed.
*)

(*
Lemma trees_unique_tag_in_created tg trnew blknew trs :
  ~trees_contain tg trs blknew ->
  tree_contains tg trnew ->
  trees_unique tg (<[blknew:=trnew]>trs) blknew.
Proof.
  move=> Fresh Ins blk' Ex'.
  destruct (decide (blknew = blk')); [auto|].
  rewrite /trees_contain in Ex'.
  rewrite <- trees_at_block_insert_ne in Ex'; [|assumption].
  destruct (Fresh blk' Ex').
Qed.

Lemma trees_unique_tag_already_there tg blk0 trnew blknew trs :
  blk0 ≠ blknew ->
  trees_unique_tag tg trs blk0 ->
  ~tree_contains tg trnew ->
  trees_unique_tag tg (<[blknew:=trnew]>trs) blk0.
Proof.
  move=> Ne Unq NoCollision blk' Ex'.
  rewrite /trees_contain in Ex'.
  destruct (decide (blknew = blk')); [subst|].
  - rewrite /trees_at_block lookup_insert in Ex'. contradiction.
  - rewrite <- trees_at_block_insert_ne in Ex'; [|done].
    apply Unq. exact Ex'.
Qed.
*)

(*
Lemma trees_at_block_inserted (prop : tree item -> Prop) trs blk0 tr0 :
  trees_at_block prop (<[blk0:=tr0]>trs) blk0 <-> prop tr0.
Proof.
  rewrite /trees_at_block lookup_insert.
  tauto.
Qed.
*)

(*
Lemma bor_estep_preserves_unique_tag tg trs blk trs' :
  trees_contain tg trs blk ->
  trees_unique_tag tg trs blk ->
  forall cids cids' evt,
  bor_estep
    trs cids
    evt
    trs' cids'
  ->
  match evt with
  | DeallocBEvt blk'
  => blk ≠ blk' -> trees_unique_tag tg trs' blk
  | AccessBEvt _ _ _ _ _
  | AllocBEvt _ _
  | InitCallBEvt _
  | EndCallBEvt _
  | RetagBEvt _ _ _ _
  | SilentBEvt
  => trees_unique_tag tg trs' blk
  end.
Proof.
  move=> Ex Unqt ??? Step.
  inversion Step; subst.
  - (* Alloc *)
    apply trees_unique_tag_already_there.
    + intro; subst.
      destruct (trees_at_block_destruct _ _ _ Ex) as [?[Contra ?]].
      rewrite Contra in FRESH_BLOCK; inversion FRESH_BLOCK.
    + assumption.
    + simpl. rewrite /IsTag; simpl.
      destruct (decide (tg0 = tg)); [subst|].
      * destruct (FRESH_TAG _ Ex).
      * tauto.
  - (* Access *)
    destruct (option_bind_success_step _ _ _ ACC) as [?[Lookup ACC']]; clear ACC.
    destruct (option_bind_success_step _ _ _ ACC') as [?[Access ACC'']]; clear ACC'.
    injection ACC''; intros; subst; clear ACC''.
    apply (trees_unique_tag_preserved _ _ trs _); [|assumption].
    intro blk'.
    destruct (decide (blk' = blk0)); [subst|].
    + split; intro Hyp.
      * apply trees_at_block_insert.
        rewrite <- access_preserves_tags; [|apply item_apply_access_preserves_tag|exact Access].
        eapply trees_at_block_project; [exact Hyp|exact Lookup].
      * rewrite /trees_contain trees_at_block_inserted in Hyp.
        eapply trees_at_block_build; [exact Lookup|].
        rewrite access_preserves_tags; [|apply item_apply_access_preserves_tag|exact Access].
        exact Hyp.
    + rewrite /trees_contain. rewrite <- trees_at_block_insert_ne; [tauto|auto].
  - (* Dealloc *) intro; assumption.
  - (* InitCall *) assumption.
  - (* EndCall *) assumption.
  - (* Retag *)
    destruct (option_bind_success_step _ _ _ RETAG_EFFECT) as [?[Lookup RETAG']]; clear RETAG_EFFECT.
    destruct (option_bind_success_step _ _ _ RETAG') as [?[Ins RETAG'']]; clear RETAG'.
    injection RETAG''; intros; subst; clear RETAG''.
    apply (trees_unique_tag_preserved _ _ trs _); [|assumption].
    intro blk'.
    destruct (decide (blk' = blk0)); [subst|].
    + split; intro Hyp.
      * apply trees_at_block_insert.
        eapply insertion_preserves_tags; [|exact Ins].
        eapply trees_at_block_project; [exact Hyp|exact Lookup].
      * rewrite /trees_contain trees_at_block_inserted in Hyp.
        eapply trees_at_block_build; [exact Lookup|].
        eapply insertion_minimal_tags; [|exact Hyp|exact Ins].
        intro; subst; destruct (FRESH_CHILD _ Ex).
    + rewrite /trees_contain. rewrite <- trees_at_block_insert_ne; [tauto|auto].
Qed.
*)

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
  : match evt with
  | AccessBLEvt _ _ _ _ => exists it', tree_unique tg it' tr'
  | InitCallBLEvt _
  | EndCallBLEvt _
  | RetagBLEvt _ _ _ _
  | SilentBLEvt => tree_unique tg it tr'
  end.
Proof.
  inversion Step; subst.
  all: try assumption.
  - (* Access *)
    destruct (apply_access_spec_per_node _ _ _ _ EXISTS_TAG Ex Unq _ _ _ _ _ (item_apply_access_preserves_tag _ _) ACC) as [?[_[_?]]].
    eexists; eauto.
  - (* Retag *)
    eapply create_child_preserves_unique; [|exact Unq|exact RETAG_EFFECT].
    intro; subst. destruct (FRESH_CHILD Ex).
Qed.
Arguments bor_local_step_preserves_unique_easy {_ _ _ _} Ex Unq {_ _ _} Step.

Lemma bor_local_step_eqv_rel
  tg tg' tr tr'
  (Ex : tree_contains tg tr)
  (Ex' : tree_contains tg' tr)
  cids cids' evt
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
Arguments bor_local_step_eqv_rel {_ _ _ _} Ex Ex' {_ _ _} Step.

Lemma bor_local_step_retag_produces_rel
  tgp tg tr tr' cids cids' newp cid
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
Arguments bor_local_step_retag_produces_rel {_ _ _ _ _ _ _ _} Step.

Lemma bor_local_step_retag_order_nonparent
  tgp tg tg' tr tr'
  (Ex' : tree_contains tg' tr)
  cids cids' newp cid
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
Arguments bor_local_step_retag_order_nonparent {_ _ _ _ _} Ex' {_ _ _ _} Step.

(*
Lemma ParentChildInBlk_transitive tg tg' tg'' trs blk :
  ParentChildInBlk tg tg' trs blk ->
  ParentChildInBlk tg' tg'' trs blk ->
  ParentChildInBlk tg tg'' trs blk.
Proof.
  move=> Rel Rel'.
  destruct (trees_at_block_destruct _ _ _ Rel) as [?[Lkup R]].
  pose proof (trees_at_block_project _ _ _ x Rel' Lkup) as R'.
  eapply trees_at_block_build; [exact Lkup|].
  eapply ParentChild_transitive; eassumption.
Qed.
*)

Lemma apply_access_perm_preserves_backwards_reach pre post :
  forall kind rel b b',
  apply_access_perm kind rel b b' pre = Some post ->
  forall p0,
  reach p0 (perm pre) -> reach p0 (perm post).
Proof.
  move=> kind rel b b' Apply p0.
  destruct b, b', kind, rel.
  all: destruct pre, initialized, perm.
  all: destruct p0.
  all: inversion Apply.
  (* all cases easy *)
  all: intro H; inversion H.
  all: auto.
Qed.

Lemma apply_access_perm_preserves_forward_unreach pre post :
  forall kind rel b b',
  apply_access_perm kind rel b b' pre = Some post ->
  forall p0,
  ~reach (perm pre) p0 -> ~reach (perm post) p0.
Proof.
  move=> kind rel b b' Apply p0.
  destruct b, b', kind, rel.
  all: destruct pre, initialized, perm.
  all: destruct p0.
  all: inversion Apply.
  (* all cases easy *)
  all: intros H H'; apply H; inversion H'.
  all: auto.
Qed.

(* Preservation of reachability *)
Lemma memory_access_preserves_backwards_reach access_tag affected_tag pre tr post tr' :
  forall kind strong cids range,
  tree_contains affected_tag tr ->
  tree_unique affected_tag pre tr ->
  tree_contains access_tag tr ->
  memory_access kind strong cids access_tag range tr = Some tr' ->
  tree_unique affected_tag post tr' ->
  forall p0 z,
  reach p0 (item_perm_at_loc pre z) -> reach p0 (item_perm_at_loc post z).
Proof.
  move=> ???? ExAff UnqAff ExAcc Access UnqAff' p0 z.
  destruct (apply_access_spec_per_node _ _ _ _ ExAcc ExAff UnqAff _ _ _ _ _ (item_apply_access_preserves_tag _ _) Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_unique_unify _ _ _ _ ExPost UnqPost UnqAff'); subst.
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
    eapply apply_access_perm_preserves_backwards_reach.
    rewrite Lkup; simpl. exact Apply.
  - rewrite Spec; tauto.
Qed.

Lemma memory_access_preserves_forward_unreach access_tag affected_tag pre tr post tr' :
  forall kind strong cids range,
  tree_contains affected_tag tr ->
  tree_unique affected_tag pre tr ->
  tree_contains access_tag tr ->
  memory_access kind strong cids access_tag range tr = Some tr' ->
  tree_unique affected_tag post tr' ->
  forall p0 z,
  ~reach (item_perm_at_loc pre z) p0 -> ~reach (item_perm_at_loc post z) p0.
Proof.
  move=> ???? ExAff UnqAff ExAcc Access UnqAff' p0 z.
  destruct (apply_access_spec_per_node _ _ _ _ ExAcc ExAff UnqAff _ _ _ _ _ (item_apply_access_preserves_tag _ _) Access) as [post' [PostSpec [ExPost UnqPost]]].
  pose proof (tree_unique_unify _ _ _ _ ExPost UnqPost UnqAff'); subst.
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


