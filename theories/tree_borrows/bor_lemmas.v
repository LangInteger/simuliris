From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas.
From iris.prelude Require Import options.

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


