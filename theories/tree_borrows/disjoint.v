From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas.

Lemma insert_eqv_rel t t' (ins:item) (tr:tree item) (search:Tprop item)
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
  - apply insert_eqv_rel; auto.
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

Lemma inserted_not_parent (t:tag) (ins:item) (tr:tree item) :
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
  forall cids range tr' newp,
  create_child cids tgp range tgc newp tr = Some tr' ->
    (exists tr'', memory_read cids tgp range tr = Some tr''
    /\ tr' = insert_child_at tr'' (create_new_item tgc newp range) (IsTag tgp)).
Proof.
  move=> ?? tr' ? CreateChild.
  unfold create_child in CreateChild.
  destruct (memory_read _ tgp _ tr); simpl in *; inversion CreateChild.
  injection CreateChild; intros; subst.
  exists t.
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
  forall perm range,
  IsTag tg (create_new_item tg perm range).
Proof.
  move=> ??.
  unfold create_new_item.
  unfold IsTag; simpl; reflexivity.
Qed.

Lemma insertion_contains tr tgp tgc :
  forall cids range tr' newp,
  tree_contains tgp tr ->
  create_child cids tgp range tgc newp tr = Some tr' ->
  tree_contains tgc tr'.
Proof.
  move=> ?? tr' ? ContainsParent CreateChild.
  unfold tree_contains in *.
  destruct (create_child_isSome tr tgp tgc _ _ _ _ CreateChild) as [tr'' [Read Insert]].
  rewrite Insert.
  apply insert_true_produces_exists.
  - apply new_item_has_tag.
  - apply (access_preserves_tags _ _ _ _ _ _ _ _ (item_apply_access_preserves_tag _) Read).
    exact ContainsParent.
Qed.

Lemma insertion_preserves_tags tr tg :
  forall tgp tgc cids range tr' newp,
  tree_contains tg tr ->
  create_child cids tgp range tgc newp tr = Some tr' ->
  tree_contains tg tr'.
Proof.
  move=> ???? tr' ? Contains CreateChild.
  unfold tree_contains in *.
  destruct (create_child_isSome tr _ _ _ _ _ _ CreateChild) as [tr'' [Read Insert]].
  rewrite Insert.
  apply insert_preserves_exists.
  apply (access_preserves_tags _ _ _ _ _ _ _ _ (item_apply_access_preserves_tag _) Read).
  exact Contains.
Qed.

Lemma insertion_order_nonchild tr tg tg' :
  tree_contains tg' tr ->
  ~tree_contains tg tr ->
  forall tgp cids range newp tr',
  tree_contains tgp tr ->
  create_child cids tgp range tg newp tr = Some tr' ->
  ~StrictParentChildIn tg tg' tr'.
Proof.
  move=> Present Fresh tgp ??? tr' ParentPresent Insert Contra.
  unfold create_child in Insert.
  remember (memory_read _ _ _ _) as tr''.
  destruct tr'' as [tr''|]; simpl in *; try (inversion Insert; done).
  injection Insert; intros; subst; clear Insert.
  symmetry in Heqtr''.
  assert (tree_contains tg' tr'') as Present'. {
    erewrite <- access_preserves_tags.
    - apply Present.
    - apply item_apply_access_preserves_tag.
    - exact Heqtr''.
  } clear Present.
  assert (~tree_contains tg tr'') as Fresh'. {
    intro Invert; apply Fresh; erewrite access_preserves_tags.
    - apply Invert.
    - apply item_apply_access_preserves_tag.
    - exact Heqtr''.
  } clear Fresh.
  assert (tree_contains tgp tr'') as ParentPresent'. {
    erewrite <- access_preserves_tags.
    - apply ParentPresent.
    - apply item_apply_access_preserves_tag.
    - exact Heqtr''.
  } clear ParentPresent.
  eapply inserted_not_parent with (ins := (create_new_item tg _ _)).
  - apply ParentPresent'.
  - simpl; apply Fresh'.
  - apply Present'.
  - apply Contra.
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
    /\ tree_unique affected_tag tr' post.
Proof.
  intros Contains Contains' TgSpec fn cids range tr' dyn_rel FnPreservesTag Success.
  (* Grab the success condition of every node separately *)
  pose proof (proj1 (join_success_condition _) (mk_is_Some _ _ Success)) as SuccessCond.
  rewrite every_node_map in SuccessCond; rewrite every_node_eqv_universal in SuccessCond.
  pose proof (exists_unique_exists _ _ _ Contains' TgSpec) as Expre.
  pose proof (SuccessCond pre Expre) as [post postSpec].
  unfold tree_unique in TgSpec. rewrite every_node_eqv_universal in TgSpec.
  (* Now do some transformations to get to the node level *)
  unfold tree_unique.
  exists post.
  split; [symmetry; auto|].
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

Lemma option_bind_success_step {T U} (ox:option T) (f:T -> option U) (r:U) :
  ((x ← ox; f x) = Some r) -> exists x, ox = Some x /\ f x = Some r.
Proof.
  intro H.
  destruct ox; simpl in *; [|inversion H].
  eexists. split; [reflexivity|assumption].
Qed.

(* Key lemma: converts the entire traversal to a per-node level.
   This is applicable to every permission in the accessed range, all that's needed
   to complement it should be preservation of permissions outside of said range. *)
Lemma access_effect_per_loc tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  forall kind cids range tr' z zpre,
  range_contains range z ->
  every_node (fun it =>
    IsTag affected_tag it ->
    item_lazy_perm_at_loc it z = zpre
  ) tr ->
  tree_apply_access (item_apply_access kind) cids access_tag range tr (naive_rel_dec tr) = Some tr' ->
  exists zpost, (
    let rel := if naive_rel_dec tr affected_tag access_tag then AccessChild else AccessForeign in
    let prot := bool_decide (is_active_protector cids pre.(iprot)) in
    apply_access_perm kind rel prot zpre = Some zpost /\
    every_node (fun it =>
      IsTag affected_tag it ->
      item_lazy_perm_at_loc it z = zpost
    ) tr'
  ).
Proof.
  intros ContainsAcc ContainsAff UniqueAff kind cids range tr' z zpre WithinRange IsPre Success.
  (* use apply_access_spec_per_node to get info on the post permission *)
  destruct (apply_access_spec_per_node _ _ _ _
    ContainsAcc ContainsAff UniqueAff
    (item_apply_access kind) cids range tr' (naive_rel_dec tr)
    (item_apply_access_preserves_tag kind) Success) as [post [postSpec postUnique]].
  clear Success.
  (* and then it's per-tag work *)
  rewrite (tree_unique_specifies_tag _ _ _ ContainsAff UniqueAff) in postSpec.
  symmetry in postSpec.
  destruct (option_bind_success_step _ _ _  postSpec) as [tmpperm [tmpSpec tmpRes]].
  injection tmpRes; intro H; subst; clear tmpRes.
  (* now down to per-location *)
  pose proof (range_foreach_spec _ _ z _ _ tmpSpec) as ForeachSpec.
  rewrite (decide_True _ _ WithinRange) in ForeachSpec.
  destruct ForeachSpec as [lazy_perm [PermExists ForeachSpec]].
  assert (unwrap {| initialized := false; perm := initp pre |} (iperm pre !! z) = item_lazy_perm_at_loc pre z) as InitPerm. {
    unfold item_lazy_perm_at_loc. destruct (iperm pre !! z); simpl; reflexivity.
  } rewrite InitPerm in ForeachSpec.
  rewrite every_node_eqv_universal in IsPre.
  rewrite IsPre in ForeachSpec; [
    |apply (exists_unique_exists _ _ _ ContainsAff UniqueAff)
    |apply (tree_unique_specifies_tag _ _ _ ContainsAff UniqueAff)
  ].
  eexists; split; [exact ForeachSpec|].
  (* Now we have to prove that tr' is indeed the per-node mapping of apply_access_perm, which is not too hard *)
  rewrite every_node_eqv_universal; intros post Expost Tagpost.
  unfold tree_unique in postUnique; rewrite every_node_eqv_universal in postUnique.
  rewrite (postUnique post Expost Tagpost).
  unfold item_lazy_perm_at_loc; simpl; rewrite PermExists; simpl; reflexivity.
Qed.

Lemma nonchild_write_disables tr affected_tag access_tag pre :
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  tree_unique affected_tag tr pre ->
  ~ParentChildIn affected_tag access_tag tr ->
  forall cids range tr' z zpre,
  range_contains range z ->
  every_node (fun it =>
    IsTag affected_tag it ->
    item_lazy_perm_at_loc it z = zpre
  ) tr ->
  perm zpre ≠ ReservedMut ->
  memory_write cids access_tag range tr = Some tr' ->
  exists zpost, (
    every_node (fun it =>
      IsTag affected_tag it ->
      item_lazy_perm_at_loc it z = zpost
    ) tr'
    /\
    perm zpost = Disabled
  ).
Proof.
  intros ContainsAcc ContainsAff UniqueAff Nonrel cids range tr' z zpre WithinRange preLoc NonResMut Write.
  destruct (access_effect_per_loc _ _ _ _
    ContainsAcc ContainsAff UniqueAff
    AccessWrite cids range tr' z zpre WithinRange preLoc Write) as [zpost [postSpec postLoc]].
  exists zpost.
  split; [exact postLoc|].
  clear postLoc Write WithinRange preLoc ContainsAcc ContainsAff UniqueAff.
  destruct (naive_rel_dec _ _ _); [contradiction|].
  destruct zpre; destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: try inversion postSpec.
  all: simpl; reflexivity.
Qed.


