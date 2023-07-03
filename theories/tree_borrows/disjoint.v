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

Lemma item_apply_access_preserves_tag kind it :
  forall cids rel range it',
  item_apply_access kind cids rel range it = Some it' ->
  itag it = itag it'.
Proof.
  move=> ??? it'.
  unfold item_apply_access.
  destruct (permissions_foreach); simpl; [|intro H; inversion H].
  intro H; injection H; intros; subst.
  simpl; reflexivity.
Qed.

Lemma access_preserves_tags tr tg :
  forall tr' tg' app cids range dyn_rel,
  (forall it cids rel range it', app cids rel range it = Some it' -> itag it = itag it') ->
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

Lemma apply_access_spec_per_node tr affected_tag access_tag pre:
  tree_contains access_tag tr ->
  tree_contains affected_tag tr ->
  every_node (fun it => IsTag affected_tag it -> it = pre) tr ->
  forall fn cids range tr' dyn_rel,
  (forall it it' rel, fn cids rel range it = Some it' -> itag it = itag it') ->
  tree_apply_access fn cids access_tag range tr dyn_rel = Some tr' ->
  every_node (fun it => IsTag affected_tag it ->
    Some it = fn cids (if dyn_rel access_tag pre.(itag) then AccessChild else AccessForeign) range pre
  ) tr'.
Proof.
  intros Contains Contains' TgSpec fn cids range tr' dyn_rel FnPreservesTag Success.
  (* Grab the success condition of every node separately *)
  pose proof (proj1 (join_success_condition _) (mk_is_Some _ _ Success)) as SuccessCond.
  rewrite every_node_map in SuccessCond; rewrite every_node_eqv_universal in SuccessCond.
  (* Also ensure unicity of affected_tag *)
  rewrite every_node_eqv_universal in TgSpec.
  (* Now do some transformations to get to the node level *)
  rewrite join_project_every; [|exact Success].
  rewrite every_node_map.
  unfold compose.
  rewrite every_node_eqv_universal.
  intros n Exn.
  pose proof (SuccessCond n Exn) as PerNodeSuccess.
  pose proof (TgSpec n Exn) as PerNodeEqual.
  (* Phew. Clean up a bit. *)
  clear Success Contains SuccessCond TgSpec Contains' Exn.
  destruct PerNodeSuccess as [res resSpec].
  exists res.
  split; [exact resSpec|].
  intro resTg.
  rewrite <- resSpec.
  rewrite PerNodeEqual; [auto|].
  f_equal.
  unfold IsTag in *.
  erewrite FnPreservesTag; [exact resTg|exact resSpec].
Qed.

Lemma nonchild_write_disables tr tg tg' :
  tree_contains tg' tr ->
  tree_contains tg tr ->
  ~ParentChildIn tg tg' tr ->
  forall range tr',
  memory_write fn.






