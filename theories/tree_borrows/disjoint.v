From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas.
From iris.prelude Require Import options.

Lemma insert_eqv_strict_rel t t' (ins:item) (tr:tree item) (search:Tprop item)
  {search_dec:forall it, Decision (search it)} :
  ~IsTag t ins ->
  ~IsTag t' ins ->
  StrictParentChildIn t t' tr <-> StrictParentChildIn t t' (insert_child_at tr ins search).
Proof.
  intros Nott Nott'; unfold ParentChildIn.
  induction tr; simpl; auto.
  destruct (decide (search data)).
  + rewrite IHtr1; clear IHtr1. rewrite IHtr2; clear IHtr2.
    simpl.
    split; intro Hyp.
    - destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
      try repeat split; auto.
      intro H; right; left. eapply insert_preserves_exists; auto.
    - destruct Hyp as [Hyp0 [Hyp1 [Hyp21 [Hyp22 _]]]].
      try repeat split; auto.
      intro H; destruct (Hyp0 H) as [|[|]]; [contradiction| |contradiction].
      eapply insert_false_infer_exists; eauto.
  + rewrite IHtr1; clear IHtr1. rewrite IHtr2; clear IHtr2.
    simpl.
    split; intro Hyp.
- destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
  try repeat split; auto.
  intro H; auto.
  apply insert_preserves_exists; auto.
- destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
  try repeat split; auto.
  intro H; auto.
  eapply insert_false_infer_exists; eauto.
Qed.

Lemma insert_eqv_rel t t' (ins:item) (tr:tree item) (search:Tprop item)
  {search_dec:forall it, Decision (search it)} :
  ~IsTag t ins ->
  ~IsTag t' ins ->
  ParentChildIn t t' tr <-> ParentChildIn t t' (insert_child_at tr ins search).
Proof.
  move=> ??.
  split; intro Hyp.
  all: destruct Hyp as [Eq|Strict]; [left; assumption|right].
  - erewrite <- insert_eqv_strict_rel; assumption.
  - erewrite <- insert_eqv_strict_rel in Strict; assumption.
Qed.

Lemma join_map_preserves_exists {X} (tr tr':tree X) (prop:Tprop X) :
  forall fn,
  (forall x y, fn x = Some y -> prop x <-> prop y) ->
  join_nodes (map_nodes fn tr) = Some tr' ->
  exists_node prop tr <-> exists_node prop tr'.
Proof.
  move=> ? Preserves JoinMap.
  generalize dependent tr'.
  induction tr; [simpl; move=> ? H; injection H; intros; subst; tauto|].
  intros tr' JoinMap.
  destruct (destruct_joined _ _ _ _ JoinMap) as [data' [tr1' [tr2' [EqTr' [EqData' [EqTr1' EqTr2']]]]]]; subst.
  simpl.
  erewrite IHtr1; [|eassumption].
  erewrite IHtr2; [|eassumption].
  rewrite Preserves; [|eassumption].
  tauto.
Qed.

Lemma join_map_eqv_strict_rel t t' (tr tr':tree item) :
  forall fn,
  (forall it it', fn it = Some it' -> itag it = itag it') ->
  join_nodes (map_nodes fn tr) = Some tr' ->
  StrictParentChildIn t t' tr <-> StrictParentChildIn t t' tr'.
Proof.
  intros fn FnPreservesTag Success.
  generalize dependent tr'.
  unfold StrictParentChildIn.
  induction tr; intros tr' Success; simpl in *.
  - inversion Success; auto.
  - destruct (destruct_joined _ _ _ _ Success) as [data' [tr1' [tr2' [EqTr' [EqData' [EqTr1' EqTr2']]]]]].
    rewrite IHtr1; [|eapply EqTr1'].
    rewrite IHtr2; [|eapply EqTr2'].
    subst; simpl.
    split; intro H; destruct H as [?[??]]; try repeat split; try assumption.
    all: intro Hyp.
    + rewrite <- join_map_preserves_exists; unfold IsTag in *.
      * apply H. erewrite FnPreservesTag; eassumption.
      * intros; subst. erewrite FnPreservesTag; eauto.
      * apply EqTr2'.
    + rewrite join_map_preserves_exists; unfold IsTag in *.
      * apply H. erewrite <- FnPreservesTag; eassumption.
      * intros; subst. erewrite FnPreservesTag; eauto.
      * apply EqTr2'.
Qed.

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

Lemma insert_produces_StrictParentChild t (ins:item) (tr:tree item) :
  ~IsTag t ins ->
StrictParentChildIn t ins.(itag) (insert_child_at tr ins (IsTag t)).
Proof.
  intro Nott.
  unfold StrictParentChildIn.
  induction tr; simpl; auto.
destruct (decide (IsTag t data)) eqn:Found; simpl.
  - try repeat split; auto.
    intro H; left; easy.
  - try repeat split; auto.
    intro H; contradiction.
Qed.

Lemma StrictParentChild_transitive t t' t'' (tr:tree item) :
  StrictParentChildIn t t' tr ->
StrictParentChildIn t' t'' tr ->
  StrictParentChildIn t t'' tr.
Proof.
  rewrite /StrictParentChildIn /HasStrictChildTag.
  induction tr; simpl; auto.
  intros [Condtt' [Reltt'1 Reltt'2]] [Condt't'' [Relt't''1 Relt't''2]].
split; auto.
  intro H.
  clear Relt't''1 Reltt'1 IHtr1 IHtr2.
  pose proof (Condtt' H) as Ex'.
  clear Condtt' H Condt't'' Reltt'2.
(* End of step 1: we have found a t'. Now look for a t''. *)
  induction tr2; [destruct Ex'|].
  destruct Relt't''2 as [IfHere [IfLeft IfRight]].
  destruct Ex' as [Here | [Left | Right]].
  - simpl in *; right; right; auto.
  - right; left; auto.
  - right; right; auto.
Qed.

Lemma ParentChild_transitive t t' t'' (tr:tree item) :
  ParentChildIn t t' tr ->
  ParentChildIn t' t'' tr ->
  ParentChildIn t t'' tr.
Proof.
  unfold ParentChildIn.
  destruct (decide (t = t')); [subst; tauto|].
  destruct (decide (t' = t'')); [subst; tauto|].
  intros Ptt' Pt't''.
  destruct Ptt'; [contradiction|].
  destruct Pt't''; [contradiction|].
  right.
  eapply StrictParentChild_transitive; eauto.
Qed.

Lemma insert_produces_StrictParentChild_transitive t t' (ins:item) (tr:tree item) :
  ~IsTag t ins ->
  ~IsTag t' ins ->
  StrictParentChildIn t t' tr ->
  StrictParentChildIn t ins.(itag) (insert_child_at tr ins (IsTag t')).
Proof.
  intros Nott Nott' Ptt'.
  apply (StrictParentChild_transitive t t' ins.(itag)).
  - apply insert_eqv_strict_rel; auto.
  - apply insert_produces_StrictParentChild; auto.
Qed.


Lemma insert_produces_minimal_ParentChild (t t':tag) (ins:item) (tr:tree item) :
  ~IsTag t ins ->
  ~IsTag t' ins ->
  ~t = t' ->
  ~tree_contains ins.(itag) tr ->
  StrictParentChildIn t ins.(itag) (insert_child_at tr ins (IsTag t')) ->
  StrictParentChildIn t t' tr.
Proof.
  intros Nott Nott' Diff Absent Pins.
  unfold tree_contains in Absent.
  rewrite <- every_not_eqv_not_exists in Absent.
  induction tr; simpl; auto.
  simpl in Pins; destruct (decide (IsTag t' data)) as [Tg'|].
  all: destruct Absent as [Absent0 [Absent1 Absent2]].
  all: destruct Pins as [Pins0 [Pins1 Pins2]].
  all: try repeat split.
  - intro Contra; exfalso; unfold IsTag in Tg'; unfold IsTag in Contra.
    subst; contradiction.
  - apply IHtr1; assumption.
  - apply IHtr2; [|destruct Pins2 as [?[??]]]; assumption.
  - intro Tg. simpl in Pins0.
    eapply exists_insert_requires_parent.
    + exact Absent2.
    + apply Pins0. exact Tg.
  - apply IHtr1; assumption.
  - apply IHtr2; assumption.
Qed.

Lemma inserted_empty_children (t:tag) (ins:item) (tr:tree item) :
  ~tree_contains ins.(itag) tr ->
  every_subtree (fun br => HasRootTag ins.(itag) br -> empty_children br) (insert_child_at tr ins (IsTag t)).
Proof.
  move=> Fresh.
  unfold tree_contains in Fresh.
  rewrite <- every_not_eqv_not_exists in Fresh.
  induction tr; simpl; auto.
  destruct (decide (IsTag t data)); simpl in *.
  all: destruct Fresh as [Fresh0 [Fresh1 Fresh2]].
  + try repeat split.
    - intro; contradiction.
    - apply IHtr1; exact Fresh1.
    - apply IHtr2; exact Fresh2.
  + try repeat split.
    - intro; contradiction.
    - apply IHtr1; exact Fresh1.
    - apply IHtr2; exact Fresh2.
Qed.

Lemma inserted_unique (t:tag) (ins:item) (tr:tree item) :
  ~tree_contains ins.(itag) tr ->
  tree_unique ins.(itag) (insert_child_at tr ins (IsTag t)) ins.
Proof.
  intro Fresh.
  unfold tree_unique.
  unfold tree_contains in Fresh; rewrite <- every_not_eqv_not_exists in Fresh.
  induction tr; simpl in *; auto.
  destruct Fresh as [?[??]].
  destruct (decide (IsTag t data)).
  - try repeat split; [|apply IHtr1; assumption|apply IHtr2; assumption].
    simpl; intro; contradiction.
  - try repeat split; [|apply IHtr1; assumption|apply IHtr2; assumption].
    simpl; intro; contradiction.
Qed.

Lemma inserted_not_strict_parent (t:tag) (ins:item) (tr:tree item) :
  tree_contains t tr ->
  ~tree_contains ins.(itag) tr ->
  forall t',
  tree_contains t' tr ->
  ~StrictParentChildIn ins.(itag) t' (insert_child_at tr ins (IsTag t)).
Proof.
  move=> ContainsParent Fresh t' ContainsOther Rel.
  assert (~t = ins.(itag)) as Net by (intro; subst; contradiction).
  assert (~t' = ins.(itag)) as Net' by (intro; subst; contradiction).
  unfold ParentChildIn in Rel.
  pose proof (inserted_empty_children t ins tr Fresh) as Contra.
  clear Fresh.
  clear ContainsOther.
  induction tr; simpl in *; try contradiction.
  destruct (decide (IsTag t data)).
  all: destruct ContainsParent as [Parent0 | [Parent1 | Parent2]].
  - simpl in Rel.
    destruct Rel as [_ [_ [Bad _]]]; apply Net'.
    unfold IsTag in Bad; destruct Bad; reflexivity.
  - apply IHtr1.
    * auto.
    * destruct Rel as [Rel0 [Rel1 Rel2]]; auto.
    * destruct Contra as [Contra0 [Contra1 Contra2]]; auto.
  - apply IHtr2.
    * auto.
    * destruct Rel as [Rel0 [Rel1 [Rel20 [Rel21 Rel22]]]]; auto.
    * destruct Contra as [Contra0 [Contra1 [Contra20 [Contra21 Contra22]]]]; auto.
  - contradiction.
  - apply IHtr1.
    * auto.
    * destruct Rel as [Rel0 [Rel1 Rel2]]; auto.
    * destruct Contra as [Contra0 [Contra1 Contra2]]; auto.
  - apply IHtr2.
    * auto.
    * destruct Rel as [Rel0 [Rel1 Rel2]]; auto.
    * destruct Contra as [Contra0 [Contra1 Contra2]]; auto.
Qed.

Lemma create_child_isSome tr tgp tgc :
  forall cids tr' newp,
  create_child cids tgp tgc newp tr = Some tr' ->
  tr' = insert_child_at tr (create_new_item tgc newp) (IsTag tgp).
Proof.
  move=> ? tr' ? CreateChild.
  unfold create_child in CreateChild.
  inversion CreateChild.
  auto.
Qed.

Lemma item_apply_access_preserves_tag kind :
  app_preserves_tag (item_apply_access kind).
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

Lemma new_item_has_tag tg :
  forall perm,
  IsTag tg (create_new_item tg perm).
Proof.
  move=> ?.
  unfold create_new_item.
  unfold IsTag; simpl; reflexivity.
Qed.

Lemma insertion_contains tr tgp tgc :
  forall cids tr' newp,
  tree_contains tgp tr ->
  create_child cids tgp tgc newp tr = Some tr' ->
  tree_contains tgc tr'.
Proof.
  move=> ? tr' ? ContainsParent CreateChild.
  unfold tree_contains in *.
  pose proof (create_child_isSome tr tgp tgc _ _ _ CreateChild) as Insert.
  rewrite Insert.
  apply insert_true_produces_exists.
  - apply new_item_has_tag.
  - exact ContainsParent.
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

Lemma insertion_order_nonstrictchild tr tg tg' :
  tree_contains tg' tr ->
  ~tree_contains tg tr ->
  forall tgp cids newp tr',
  tree_contains tgp tr ->
  create_child cids tgp tg newp tr = Some tr' ->
  ~StrictParentChildIn tg tg' tr'.
Proof.
  move=> Present Fresh tgp ?? tr' ParentPresent Insert Contra.
  unfold create_child in Insert.
  injection Insert; intros; subst; clear Insert.
  eapply inserted_not_strict_parent with (ins := (create_new_item tg _)).
  - apply ParentPresent.
  - simpl; apply Fresh.
  - apply Present.
  - apply Contra.
Qed.

Lemma insertion_order_nonchild tr tg tg' :
  tree_contains tg' tr ->
  ~tree_contains tg tr ->
  forall tgp cids newp tr',
  tree_contains tgp tr ->
  create_child cids tgp tg newp tr = Some tr' ->
  ~ParentChildIn tg tg' tr'.
Proof.
  intros; intro Related.
  destruct Related.
  - subst; contradiction.
  - eapply (insertion_order_nonstrictchild _ tg tg'); eauto.
Qed.

Lemma exists_unique_exists tr tg it :
  tree_contains tg tr ->
  tree_unique tg tr it ->
  exists_node (eq it) tr.
Proof.
  move=> Contains Unique.
  induction tr; simpl in *; auto.
  destruct Unique as [?[??]].
  destruct Contains as [?|[?|?]].
  - left; symmetry; auto.
  - right; left; auto.
  - right; right; auto.
Qed.

Lemma apply_access_spec_per_node tr affected_tag access_tag pre:
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  forall fn cids range tr' dyn_rel,
  app_preserves_tag fn ->
  tree_apply_access fn cids access_tag range tr dyn_rel = Some tr' ->
  exists post,
    Some post = fn cids (if dyn_rel pre.(itag) access_tag then AccessChild else AccessForeign) range pre
    /\ tree_contains affected_tag tr'
    /\ tree_unique affected_tag tr' post.
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

Lemma tree_unique_specifies_tag tr tg it :
  tree_contains tg tr ->
  tree_unique tg tr it ->
  itag it = tg.
Proof.
  rewrite /tree_contains /tree_unique.
  rewrite exists_node_eqv_existential.
  rewrite every_node_eqv_universal.
  intros [n [Exn Tgn]] Every.
  rewrite <- (Every n); auto.
Qed.

(* Key lemma: converts the entire traversal to a per-node level.
   This is applicable to every permission in the accessed range, all that's needed
   to complement it should be preservation of permissions outside of said range. *)
Lemma access_effect_per_loc_within_range tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  forall kind cids range tr' z zpre,
  range_contains range z ->
  item_lazy_perm_at_loc pre z = zpre ->
  tree_apply_access (item_apply_access kind) cids access_tag range tr (naive_rel_dec tr) = Some tr' ->
  exists post zpost, (
    let rel := if naive_rel_dec tr affected_tag access_tag then AccessChild else AccessForeign in
    let prot := bool_decide (is_active_protector cids pre.(iprot)) in
    apply_access_perm kind rel prot zpre = Some zpost
    /\ tree_unique affected_tag tr' post
    /\ item_lazy_perm_at_loc post z = zpost
    /\ iprot post = iprot pre
  ).
Proof.
  intros ContainsAcc ContainsAff UniqueAff kind cids range tr' z zpre WithinRange IsPre Success.
  (* use apply_access_spec_per_node to get info on the post permission *)
  destruct (apply_access_spec_per_node _ _ _ _
    ContainsAcc ContainsAff UniqueAff
    (item_apply_access kind) cids range tr' (naive_rel_dec tr)
    (item_apply_access_preserves_tag kind) Success) as [post [SpecPost [ContainsPost UniquePost]]].
  clear Success.
  (* and then it's per-tag work *)
  rewrite (tree_unique_specifies_tag _ _ _ ContainsAff UniqueAff) in SpecPost.
  symmetry in SpecPost.
  destruct (option_bind_success_step _ _ _  SpecPost) as [tmpperm [tmpSpec tmpRes]].
  injection tmpRes; intro H; subst; clear tmpRes.
  (* now down to per-location *)
  pose proof (range_foreach_spec _ _ z _ _ tmpSpec) as ForeachSpec.
  rewrite (decide_True _ _ WithinRange) in ForeachSpec.
  destruct ForeachSpec as [lazy_perm [PermExists ForeachSpec]].
  assert (unwrap {| initialized := false; perm := initp pre |} (iperm pre !! z) = item_lazy_perm_at_loc pre z) as InitPerm. {
    unfold item_lazy_perm_at_loc. destruct (iperm pre !! z); simpl; reflexivity.
  } rewrite InitPerm in ForeachSpec.
  eexists. eexists.
  split; [|split; [|split]]; [|exact UniquePost|reflexivity|reflexivity].
  rewrite ForeachSpec.
  unfold item_lazy_perm_at_loc.
  rewrite PermExists; simpl; reflexivity.
Qed.

Lemma access_effect_per_loc_outside_range tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  forall kind cids range tr' z zpre,
  ~range_contains range z ->
  item_lazy_perm_at_loc pre z = zpre ->
  tree_apply_access (item_apply_access kind) cids access_tag range tr (naive_rel_dec tr) = Some tr' ->
  exists post, (
    tree_unique affected_tag tr post
    /\ item_lazy_perm_at_loc post z = zpre
    /\ iprot post = iprot pre
  ).
Proof.
  intros ContainsAcc ContainsAff UniqueAff kind cids range tr' z zpre OutsideRange IsPre Success.
  destruct (apply_access_spec_per_node _ _ _ _
    ContainsAcc ContainsAff UniqueAff _ _ _ _ _
    (item_apply_access_preserves_tag kind)
    Success) as [post [SpecPost [ContainsPost UniquePost]]].
  (* We now show that
     (1) post has zpre at loc z
     (2) post is equal to whatever item the goal refers to *)
  assert (item_lazy_perm_at_loc post z = item_lazy_perm_at_loc pre z) as SamePerm. {
    symmetry in SpecPost.
    destruct (option_bind_success_step _ _ _ SpecPost) as [perms [SpecPerms Injectable]].
    injection Injectable; intros; subst; clear Injectable.
    pose proof (range_foreach_spec _ _ z _ _ SpecPerms) as RangeForeach.
    rewrite (decide_False _ _ OutsideRange) in RangeForeach.
    unfold item_lazy_perm_at_loc; simpl.
    rewrite RangeForeach; reflexivity.
  }
  eexists.
  split; [|split]; [exact UniqueAff|apply IsPre|reflexivity].
Qed.

Lemma nonchild_write_reserved_to_disabled tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  ~ParentChildIn affected_tag access_tag tr ->
  forall cids range tr' z zpre,
  range_contains range z ->
  item_lazy_perm_at_loc pre z = zpre ->
  reach Reserved (perm zpre) ->
  memory_write cids access_tag range tr = Some tr' ->
  exists post zpost, (
    tree_unique affected_tag tr' post
    /\ item_lazy_perm_at_loc post z = zpost
    /\ reach Disabled (perm zpost)
    /\ iprot post = iprot pre
  ).
Proof.
  intros ContainsAcc ContainsAff UniqueAff Nonrel cids range tr' z zpre WithinRange preLoc NonResMut Write.
  destruct (access_effect_per_loc_within_range _ _ _ _
    ContainsAcc ContainsAff UniqueAff
    AccessWrite cids range tr' z zpre WithinRange preLoc Write) as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  exists post, zpost.
  try repeat split; auto.
  destruct (naive_rel_dec _ _ _); [contradiction|].
  destruct zpre; destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: try inversion SpecPost.
  all: simpl; tauto.
Qed.

Lemma nonchild_read_active_to_frozen tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  ~ParentChildIn affected_tag access_tag tr ->
  forall cids range tr' z zpre,
  range_contains range z ->
  item_lazy_perm_at_loc pre z = zpre ->
  reach Active (perm zpre) ->
  memory_read cids access_tag range tr = Some tr' ->
  exists post zpost, (
    tree_unique affected_tag tr' post
    /\ item_lazy_perm_at_loc post z = zpost
    /\ reach Frozen (perm zpost)
    /\ reach (perm zpre) (perm zpost)
  ).
Proof.
  intros ContainsAcc ContainsAff UniqueAff Nonrel cids range tr' z zpre WithinRange preLoc NonResMut Read.
  destruct (access_effect_per_loc_within_range _ _ _ _
    ContainsAcc ContainsAff UniqueAff
    AccessRead cids range tr' z zpre WithinRange preLoc Read) as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  exists post, zpost.
  try repeat split; auto.
  all: destruct (naive_rel_dec _ _ _); [contradiction|].
  all: destruct zpre; destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: try inversion SpecPost.
  all: simpl; tauto.
Qed.

Lemma child_write_frozen_to_ub tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  ParentChildIn affected_tag access_tag tr ->
  forall cids range tr' z zpre,
  range_contains range z ->
  item_lazy_perm_at_loc pre z = zpre ->
  reach Frozen (perm zpre) ->
  memory_write cids access_tag range tr = Some tr' ->
  False.
Proof.
  intros ContainsAcc ContainsAff UniqueAff Related cids range tr' z zpre WithinRange PermPre ReachFrz Write.
  destruct (access_effect_per_loc_within_range _ _ _ _
  ContainsAcc ContainsAff UniqueAff
  AccessWrite cids range tr' z zpre WithinRange PermPre Write) as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [|contradiction].
  destruct zpre; destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: try inversion SpecPost.
Qed.

Lemma child_read_disabled_to_ub tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  ParentChildIn affected_tag access_tag tr ->
  forall cids range tr' z zpre,
  range_contains range z ->
  item_lazy_perm_at_loc pre z = zpre ->
  reach Disabled (perm zpre) ->
  memory_read cids access_tag range tr = Some tr' ->
  False.
Proof.
  intros ContainsAcc ContainsAff UniqueAff Related cids range tr' z zpre WithinRange PermPre ReachFrz Read.
  destruct (access_effect_per_loc_within_range _ _ _ _
    ContainsAcc ContainsAff UniqueAff
    AccessRead cids range tr' z zpre WithinRange PermPre Read) as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [|contradiction].
  destruct zpre; destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: try inversion SpecPost.
Qed.

Lemma child_write_any_to_init_active tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  ParentChildIn affected_tag access_tag tr ->
  forall cids range tr' z,
  range_contains range z ->
  memory_write cids access_tag range tr = Some tr' ->
  exists post zpost, (
    tree_unique affected_tag tr' post
    /\ item_lazy_perm_at_loc post z = zpost
    /\ perm zpost = Active
    /\ iprot post = iprot pre
    /\ initialized zpost = true
  ).
Proof.
  intros ContainsAcc ContainsAff UniqueAff Related cids range tr' z WithinRange Write.
  destruct (access_effect_per_loc_within_range _ _ _ _
    ContainsAcc ContainsAff UniqueAff
    AccessWrite cids range tr' z
    (item_lazy_perm_at_loc pre z) WithinRange ltac:(reflexivity) Write) as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [|contradiction].
  exists post, zpost.
  try repeat split; try assumption.
  all: destruct (item_lazy_perm_at_loc _ _); destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: unfold apply_access_perm in SpecPost; simpl in *.
  all: try inversion SpecPost.
  all: injection SpecPost; intro H; destruct zpost; injection H; intros; subst; simpl; reflexivity.
Qed.

Lemma child_read_any_to_init_nondis tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  ParentChildIn affected_tag access_tag tr ->
  forall cids range tr' z,
  range_contains range z ->
  memory_read cids access_tag range tr = Some tr' ->
  exists post zpost, (
    tree_unique affected_tag tr' post
    /\ item_lazy_perm_at_loc post z = zpost
    /\ ~reach Disabled (perm zpost)
    /\ iprot post = iprot pre
    /\ initialized zpost = true
  ).
Proof.
  intros ContainsAcc ContainsAff UniqueAff Related cids range tr' z WithinRange Read.
  destruct (access_effect_per_loc_within_range _ _ _ _
    ContainsAcc ContainsAff UniqueAff
    AccessRead cids range tr' z
    (item_lazy_perm_at_loc pre z) WithinRange ltac:(reflexivity) Read) as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [|contradiction].
  exists post, zpost.
  try repeat split; try assumption.
  all: destruct (item_lazy_perm_at_loc _ _); destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: unfold apply_access_perm in SpecPost; simpl in *.
  all: try inversion SpecPost.
  all: injection SpecPost; intro H; destruct zpost; simpl; tauto.
Qed.

Lemma protected_nonchild_write_initialized_to_ub tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  ~ParentChildIn affected_tag access_tag tr ->
  forall cids range tr' z,
  is_active_protector cids (iprot pre) ->
  initialized (item_lazy_perm_at_loc pre z) = true ->
  ~reach Disabled (perm (item_lazy_perm_at_loc pre z)) ->
  range_contains range z ->
  memory_write cids access_tag range tr = Some tr' ->
  False.
Proof.
  move=> ContainsAcc ContainsAff UniqueAff Unrelated ???? Protected Initialized NonDis WithinRange Write.
  destruct (access_effect_per_loc_within_range _ _ _ _
    ContainsAcc ContainsAff UniqueAff
    AccessWrite _ _ _ _ _ WithinRange
    ltac:(reflexivity) Write) as [post [zpost [SpecPost [UniquePost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [contradiction|].
  rewrite bool_decide_eq_true_2 in SpecPost; [|assumption].
  destruct (item_lazy_perm_at_loc _ _); simpl in Initialized; subst.
  destruct perm; unfold apply_access_perm in SpecPost; simpl in SpecPost.
  all: inversion SpecPost.
  (* One case remaining: was already Disabled *)
  apply NonDis; simpl; tauto.
Qed.

Lemma protected_nonchild_read_initialized_active_to_ub tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  ~ParentChildIn affected_tag access_tag tr ->
  forall cids range tr' z,
  is_active_protector cids (iprot pre) ->
  initialized (item_lazy_perm_at_loc pre z) = true ->
  perm (item_lazy_perm_at_loc pre z) = Active ->
  range_contains range z ->
  memory_read cids access_tag range tr = Some tr' ->
  False.
Proof.
  move=> ContainsAcc ContainsAff UniqueAff Unrelated ???? Protected Initialized Active WithinRange Read.
  destruct (access_effect_per_loc_within_range _ _ _ _
    ContainsAcc ContainsAff UniqueAff
    AccessRead _ _ _ _ _ WithinRange
    ltac:(reflexivity) Read) as [post [zpost [SpecPost [UniquePost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [contradiction|].
  rewrite bool_decide_eq_true_2 in SpecPost; [|assumption].
  destruct (item_lazy_perm_at_loc _ _); simpl in Initialized; subst.
  destruct perm; unfold apply_access_perm in SpecPost; simpl in SpecPost.
  all: try inversion Active.
  inversion SpecPost.
Qed.

Lemma protected_nonchild_read_any_to_frozen tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  ~ParentChildIn affected_tag access_tag tr ->
  forall cids range tr' z,
  is_active_protector cids (iprot pre) ->
  range_contains range z ->
  memory_read cids access_tag range tr = Some tr' ->
  exists post zpost, (
    tree_unique affected_tag tr' post
    /\ item_lazy_perm_at_loc post z = zpost
    /\ reach Frozen (perm zpost)
  ).
Proof.
  move=> ContainsAcc ContainsAff UniqueAff Unrelated ???? Protected WithinRange Read.
  destruct (access_effect_per_loc_within_range _ _ _ _
    ContainsAcc ContainsAff UniqueAff
    AccessRead _ _ _ _ _ WithinRange
    ltac:(reflexivity) Read) as [post [zpost [SpecPost [UniquePost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [contradiction|].
  rewrite bool_decide_eq_true_2 in SpecPost; [|assumption].
  eexists. eexists.
  try repeat split; [exact UniquePost|].
  destruct (item_lazy_perm_at_loc pre _); simpl in SpecPost; subst.
  destruct (item_lazy_perm_at_loc post _); simpl in SpecPost; subst.
  destruct perm; destruct initialized; simpl.
  all: unfold apply_access_perm in SpecPost; simpl in SpecPost.
  all: try injection SpecPost; intros; subst; try tauto.
  all: inversion SpecPost.
Qed.

Lemma create_child_unique tr tgp newp tg :
  tree_contains tgp tr ->
  ~tree_contains tg tr ->
  forall cids tr',
  create_child cids tgp tg newp tr = Some tr' ->
  (
    tree_contains tg tr'
    /\ tree_unique tg tr' (create_new_item tg newp)
  ).
Proof.
  intros ContainsTgp FreshTg cids tr' CreateChild.
  pose proof (create_child_isSome _ _ _ _ _ _ CreateChild) as Insertion.
  subst.
  pose ins := create_new_item tg newp.
  assert (itag ins = tg) as TgIns by (apply new_item_has_tag).
  rewrite <- TgIns.
  split.
  - eapply insert_true_produces_exists; [auto|assumption].
  - eapply inserted_unique; simpl. assumption.
Qed.

Lemma create_new_item_uniform_perm tg newp z :
  item_lazy_perm_at_loc (create_new_item tg newp) z = {|
    initialized := false;
    perm := newp.(initial_state)
  |}.
Proof.
  unfold item_lazy_perm_at_loc.
  unfold create_new_item; simpl.
  unfold init_perms.
  rewrite lookup_empty; simpl.
  reflexivity.
Qed.

Lemma create_new_item_perm_prop prop tg newp z :
  prop (initial_state newp) ->
  prop (perm (item_lazy_perm_at_loc (create_new_item tg newp) z)).
Proof. rewrite create_new_item_uniform_perm; simpl; tauto. Qed.

Lemma create_new_item_prot_prop prop tg newp :
  prop (new_protector newp) ->
  prop (iprot (create_new_item tg newp)).
Proof. simpl; tauto. Qed.

Ltac migrate prop dest :=
  lazymatch type of prop with
  (* Migrate a tree_contains *)
  | tree_contains ?tg ?tr =>
    idtac "found" tg;
    match goal with
    | ACC: memory_write _ _ _ ?tr = Some _ |- _ =>
      idtac "passing through write";
      pose proof (proj1 (access_preserves_tags _ _ _ _ _ _ _ _ (item_apply_access_preserves_tag AccessWrite) ACC) prop) as dest
    | ACC: memory_read _ _ _ ?tr = Some _ |- _ =>
      idtac "passing through read";
      pose proof (proj1 (access_preserves_tags _ _ _ _ _ _ _ _ (item_apply_access_preserves_tag AccessRead) ACC) prop) as dest
    | ACC: create_child _ _ _ _ _ = Some _ |- _ =>
      idtac "passing through insertion";
      pose proof (insertion_preserves_tags _ _ _ _ _ _ _ prop ACC) as dest
    end
  (* Migrate a parent-child relation *)
  | context [ParentChildIn ?tg ?tg' ?tr] =>
    match goal with
    | ACC: memory_write _ _ _ ?tr = Some _ |- _ =>
      rewrite (access_eqv_rel _ _ _ _ _ _ _ _ _ (item_apply_access_preserves_tag AccessWrite) ACC) in prop;
      rename prop into dest
    | ACC: memory_read _ _ _ ?tr = Some _ |- _ =>
      rewrite (access_eqv_rel _ _ _ _ _ _ _ _ _ (item_apply_access_preserves_tag AccessRead) ACC) in prop;
      rename prop into dest
    end
  (* Migrate info on a protector *)
  | context [is_active_protector _ ?old] =>
    match goal with
    | ACC: ?old = ?new |- _ =>
      rewrite <- ACC in prop; rename prop into dest
    | ACC: ?new = ?old |- _ =>
      rewrite ACC in prop; rename prop into dest
    end
  (* failed *)
  | ?other =>
    idtac prop " of type " other " cannot be migrated"
  end.

Ltac forget x :=
  repeat match goal with
  | H: context [x] |- _ => clear H
  end.

Ltac created_unique tg bindEx bindUnq :=
  match goal with
  | Rebor: create_child _ ?tgp tg _ ?tr = Some _,
    Ex: tree_contains ?tgp ?tr,
    Fresh: ~tree_contains tg ?tr
    |- _ =>
      pose proof (create_child_unique _ _ _ _ Ex Fresh _ _ Rebor) as [bindEx bindUnq]
  end.

Lemma fwrite_cwrite_disjoint tg tg' newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cids0 cids1 cids2,
  tree_contains tg tr0 ->
  tree_contains tgp tr0 ->
  ~tree_contains tg' tr0 ->
  reach Reserved (initial_state newp) ->
  create_child cids0 tgp tg' newp tr0 = Some tr1 ->
  memory_write cids1 tg range1 tr1 = Some tr2 ->
  memory_write cids2 tg' range2 tr2 = Some tr3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ???.
  intros TgEx0 TgpEx0 Tg'Fresh0 NonResMut Rebor Write12 Write23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created_unique tg' Tg'Ex1 Tg'Unique1.
  migrate TgEx0 TgEx1.
  pose proof (insertion_order_nonchild _ _ _ TgEx0 Tg'Fresh0 _ _ _ _ TgpEx0 Rebor) as Unrelated1.
  forget tr0.

  (* write step 1 *)
  destruct (nonchild_write_reserved_to_disabled _ _ _ _
    TgEx1 Tg'Ex1 Tg'Unique1
    Unrelated1 _ _ _ _ _
    RContains1 eq_refl
    ltac:(apply create_new_item_perm_prop; auto) Write12) as [post [zpost [Unique'Post2 [PermPost2 [DisPost ProtPost]]]]].
  migrate Tg'Ex1 Tg'Ex2.
  forget tr1.

  (* write step 2 *)
  destruct (child_write_frozen_to_ub _ _ _ _
    Tg'Ex2 Tg'Ex2 Unique'Post2
    ltac:(left; reflexivity) _ _ _ _ _
    RContains2 PermPost2
    ltac:(eapply (reach_transitive Frozen Disabled (perm zpost)); [done|exact DisPost])
    Write23).
Qed.

Lemma fwrite_cread_disjoint tg tg' newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cids0 cids1 cids2,
  tree_contains tg tr0 ->
  tree_contains tgp tr0 ->
  ~tree_contains tg' tr0 ->
  reach Reserved (initial_state newp) ->
  create_child cids0 tgp tg' newp tr0 = Some tr1 ->
  memory_write cids1 tg range1 tr1 = Some tr2 ->
  memory_read cids2 tg' range2 tr2 = Some tr3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ??? TgEx0 TgpEx0 Tg'Fresh0 ReachRes Rebor Write12 Read23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created_unique tg' Tg'Ex1 Tg'Unique1.
  migrate TgEx0 TgEx1.
  pose proof (insertion_order_nonchild _ _ _ TgEx0 Tg'Fresh0 _ _ _ _ TgpEx0 Rebor) as Unrelated1.
  forget tr0.

  (* write step 1 *)
  destruct (nonchild_write_reserved_to_disabled _ _ _ _
    TgEx1 Tg'Ex1 Tg'Unique1
    Unrelated1
    _ _ _ _ _ RContains1 eq_refl
    ltac:(apply create_new_item_perm_prop; auto) Write12) as [post [zpost [Unique'Post2 [PermPost2 [DisPost ProtPost]]]]].
  migrate Tg'Ex1 Tg'Ex2.
  forget tr1.

  (* read step 2 *)
  destruct (child_read_disabled_to_ub _ _ _ _
    Tg'Ex2 Tg'Ex2 Unique'Post2
    ltac:(left; reflexivity) _ _ _ _ _
    RContains2 PermPost2
    DisPost
    Read23).
Qed.

Lemma activated_fread_cwrite_disjoint tg tg' newp range1 range2 range3:
  forall tgp tr0 tr1 tr2 tr3 tr4 cids0 cids1 cids2 cids3,
  tree_contains tg tr0 ->
  tree_contains tgp tr0 ->
  ~tree_contains tg' tr0 ->
  create_child cids0 tgp tg' newp tr0 = Some tr1 ->
  memory_write cids1 tg' range1 tr1 = Some tr2 ->
  memory_read cids2 tg range2 tr2 = Some tr3 ->
  memory_write cids3 tg' range3 tr3 = Some tr4 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z /\ range_contains range3 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 tr4 ???? TgEx0 TgpEx0 Tg'Fresh0 Rebor Write12 Read23 Write34 [z [RContains1 [RContains2 RContains3]]].
  (* reborrow step *)
  created_unique tg' Tg'Ex1 Tg'Unique1.
  migrate TgEx0 TgEx1.
  pose proof (insertion_order_nonchild _ _ _ TgEx0 Tg'Fresh0 _ _ _ _ TgpEx0 Rebor) as Unrelated1.
  forget tr0.

  (* write step 1 *)
  destruct (child_write_any_to_init_active _ _ _ _
    Tg'Ex1 Tg'Ex1 Tg'Unique1
    ltac:(left; reflexivity)
    _ _ _ _ RContains1 Write12
    ) as [post1 [zpost1 [Post'Unique2 [PostPerm [PostActive _]]]]].
  migrate Tg'Ex1 Tg'Ex2.
  migrate TgEx1 TgEx2.
  migrate Unrelated1 Unrelated2.
  forget tr1.

  (* read step 2 *)
  destruct (nonchild_read_active_to_frozen _ _ _ _
    TgEx2 Tg'Ex2 Post'Unique2
    Unrelated2
    _ _ _ _ _ RContains2 PostPerm
    ltac:(rewrite PostActive; apply reach_reflexive)
    Read23) as [post2 [zpost2 [Tg'Unique3 [PermPost2 [ReachFrzPost2 ReachPost1Post2]]]]].
  migrate Tg'Ex2 Tg'Ex3.
  forget tr2.

  (* write step 3 *)
  destruct (child_write_frozen_to_ub _ _ _ _
    Tg'Ex3 Tg'Ex3 Tg'Unique3
    ltac:(left; reflexivity) _ _ _ _ _
    RContains3 PermPost2
    ReachFrzPost2
    Write34).
Qed.

Lemma protected_cwrite_fwrite_disjoint tg tg' newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cids0 cids1 cids2,
  tree_contains tg tr0 ->
  tree_contains tgp tr0 ->
  ~tree_contains tg' tr0 ->
  create_child cids0 tgp tg' newp tr0 = Some tr1 ->
  memory_write cids1 tg' range1 tr1 = Some tr2 ->
  is_active_protector cids2 (new_protector newp) ->
  memory_write cids2 tg range2 tr2 = Some tr3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ??? TgEx0 TgpEx0 Tg'Fresh0 Rebor Write12 Protected Write23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created_unique tg' Tg'Ex1 Tg'Unique1.
  pose proof (insertion_order_nonchild _ _ _ TgEx0 Tg'Fresh0 _ _ _ _ TgpEx0 Rebor) as Unrelated1.
  pose proof (create_new_item_prot_prop _ tg' _ Protected) as Protected1.
  migrate TgEx0 TgEx1.
  forget tr0.

  (* write step 1 *)
  destruct (child_write_any_to_init_active _ _ _ _
    Tg'Ex1 Tg'Ex1 Tg'Unique1 ltac:(left; reflexivity)
    _ _ _ _ RContains1 Write12) as [post [zpost [Post'Unique2 [PostPerm [PostActive [PostProt PostInit]]]]]].
  migrate TgEx1 TgEx2.
  migrate Tg'Ex1 Tg'Ex2.
  migrate Unrelated1 Unrelated2.
  migrate Protected1 Protected2.
  forget tr1.

  subst.
  destruct (protected_nonchild_write_initialized_to_ub _ _ _ _
    TgEx2 Tg'Ex2 Post'Unique2 Unrelated2
    _ _ _ _ Protected2 PostInit ltac:(rewrite PostActive; tauto) RContains2 Write23).
Qed.

Lemma protected_cread_fwrite_disjoint tg tg' newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cids0 cids1 cids2,
  tree_contains tg tr0 ->
  tree_contains tgp tr0 ->
  ~tree_contains tg' tr0 ->
  create_child cids0 tgp tg' newp tr0 = Some tr1 ->
  memory_read cids1 tg' range1 tr1 = Some tr2 ->
  is_active_protector cids2 (new_protector newp) ->
  memory_write cids2 tg range2 tr2 = Some tr3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ??? TgEx0 TgpEx0 Tg'Fresh0 Rebor Read12 Protected Write23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created_unique tg' Tg'Ex1 Tg'Unique1.
  pose proof (insertion_order_nonchild _ _ _ TgEx0 Tg'Fresh0 _ _ _ _ TgpEx0 Rebor) as Unrelated1.
  pose proof (create_new_item_prot_prop _ tg' _ Protected) as Protected1.
  migrate TgEx0 TgEx1.
  forget tr0.

  (* write step 1 *)
  destruct (child_read_any_to_init_nondis _ _ _ _
    Tg'Ex1 Tg'Ex1 Tg'Unique1 ltac:(left; reflexivity)
    _ _ _ _ RContains1 Read12) as [post [zpost [Post'Unique2 [PostPerm [PostNonDis [PostProt PostInit]]]]]].
  migrate TgEx1 TgEx2.
  migrate Tg'Ex1 Tg'Ex2.
  migrate Unrelated1 Unrelated2.
  migrate Protected1 Protected2.
  forget tr1.

  subst.
  destruct (protected_nonchild_write_initialized_to_ub _ _ _ _
    TgEx2 Tg'Ex2 Post'Unique2 Unrelated2
    _ _ _ _ Protected2 PostInit PostNonDis RContains2 Write23).
Qed.

Lemma protected_cwrite_fread_disjoint tg tg' newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cids0 cids1 cids2,
  tree_contains tg tr0 ->
  tree_contains tgp tr0 ->
  ~tree_contains tg' tr0 ->
  create_child cids0 tgp tg' newp tr0 = Some tr1 ->
  memory_write cids1 tg' range1 tr1 = Some tr2 ->
  is_active_protector cids2 (new_protector newp) ->
  memory_read cids2 tg range2 tr2 = Some tr3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ??? TgEx0 TgpEx0 Tg'Fresh0 Rebor Write12 Protected Read23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created_unique tg' Tg'Ex1 Tg'Unique1.
  pose proof (insertion_order_nonchild _ _ _ TgEx0 Tg'Fresh0 _ _ _ _ TgpEx0 Rebor) as Unrelated1.
  pose proof (create_new_item_prot_prop _ tg' _ Protected) as Protected1.
  migrate TgEx0 TgEx1.
  forget tr0.

  (* write step 1 *)
  destruct (child_write_any_to_init_active _ _ _ _
    Tg'Ex1 Tg'Ex1 Tg'Unique1 ltac:(left; reflexivity)
    _ _ _ _ RContains1 Write12) as [post [zpost [Post'Unique2 [PostPerm [PostNonDis [PostProt PostInit]]]]]].
  migrate TgEx1 TgEx2.
  migrate Tg'Ex1 Tg'Ex2.
  migrate Unrelated1 Unrelated2.
  migrate Protected1 Protected2.
  forget tr1.

  subst.
  destruct (protected_nonchild_read_initialized_active_to_ub _ _ _ _
    TgEx2 Tg'Ex2 Post'Unique2 Unrelated2
    _ _ _ _ Protected2 PostInit PostNonDis RContains2 Read23).
Qed.

Lemma protected_fread_cwrite_disjoint tg tg' newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cids0 cids1 cids2,
  tree_contains tg tr0 ->
  tree_contains tgp tr0 ->
  ~tree_contains tg' tr0 ->
  create_child cids0 tgp tg' newp tr0 = Some tr1 ->
  is_active_protector cids1 (new_protector newp) ->
  memory_read cids1 tg range1 tr1 = Some tr2 ->
  memory_write cids2 tg' range2 tr2 = Some tr3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ??? TgEx0 TgpEx0 Tg'Fresh0 Rebor Protected Read12 Write23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created_unique tg' Tg'Ex1 Tg'Unique1.
  migrate TgEx0 TgEx1.
  pose proof (insertion_order_nonchild _ _ _ TgEx0 Tg'Fresh0 _ _ _ _ TgpEx0 Rebor) as Unrelated1.
  pose proof (create_new_item_prot_prop _ tg' _ Protected) as Protected1.
  forget tr0.

  (* write step 1 *)
  destruct (protected_nonchild_read_any_to_frozen _ _ _ _
    TgEx1 Tg'Ex1 Tg'Unique1
    Unrelated1
    _ _ _ _ Protected1 RContains1 Read12) as [post [zpost [Unique'Post2 [PermPost2 FrzPost]]]].
  migrate Tg'Ex1 Tg'Ex2.
  forget tr1.

  (* read step 2 *)
  destruct (child_write_frozen_to_ub _ _ _ _
    Tg'Ex2 Tg'Ex2 Unique'Post2
    ltac:(left; reflexivity) _ _ _ _ _
    RContains2 PermPost2
    FrzPost
    Write23).
Qed.


