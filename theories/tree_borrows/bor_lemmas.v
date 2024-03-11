From iris.prelude Require Import prelude options.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas.
From iris.prelude Require Import options.

Lemma unique_somewhere
  {a b} :
  a + b = 1 -> (a = 1 /\ b = 0) \/ (b = 1 /\ a = 0).
Proof. lia. Qed.

Lemma unique_somewhere_3way
  {a b c} :
  a + b + c = 1 -> (a = 1 /\ b = 0 /\ c = 0)
                \/ (a = 0 /\ b = 1 /\ c = 0)
                \/ (a = 0 /\ b = 0 /\ c = 1).
Proof. lia. Qed.

Lemma unique_found_here
  {a b} :
  1 + a + b = 1 -> a = 0 /\ b = 0.
Proof. lia. Qed.

Lemma absent_nowhere
  {a b c} :
  a + b + c = 0 <-> a = 0 /\ b = 0 /\ c = 0.
Proof. lia. Qed.

Lemma exists_somewhere
  {a b c} :
  a + b + c ≥ 1 <-> a ≥ 1 \/ b ≥ 1 \/ c ≥ 1.
Proof. lia. Qed.

Lemma unique_exists {tr tg} :
  tree_unique tg tr ->
  tree_contains tg tr.
Proof.
  rewrite /tree_unique /tree_count_tg /has_tag.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [discriminate|].
  rewrite /IsTag.
  destruct (decide (itag data = tg)).
  - rewrite bool_decide_eq_true_2; [auto|assumption].
  - rewrite bool_decide_eq_false_2; [|assumption].
    simpl.
    intro Somewhere.
    right.
    destruct (unique_somewhere Somewhere) as [[]|[]].
    + left. apply IHtr1. assumption.
    + right. apply IHtr2. assumption.
Qed.

Lemma count_gt0_exists {tr tg} :
  tree_count_tg tg tr >= 1 <->
  tree_contains tg tr.
Proof.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [lia|].
  rewrite exists_somewhere. 
  rewrite IHtr1.
  rewrite IHtr2.
  rewrite /has_tag.
  destruct (decide (IsTag tg data)) as [Tg|nTg].
  - rewrite bool_decide_eq_true_2; [|assumption].
    apply ZifyClasses.or_morph; [split; auto|].
    reflexivity.
  - rewrite bool_decide_eq_false_2; [|assumption].
    apply ZifyClasses.or_morph; [split; intro; [lia|contradiction]|].
    reflexivity.
Qed.


Lemma count_0_not_exists tr tg :
  tree_count_tg tg tr = 0
  <-> ~tree_contains tg tr.
Proof.
  rewrite /tree_count_tg /has_tag.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [tauto|].
  rewrite /IsTag.
  split.
  - intro Nowhere.
    destruct (proj1 absent_nowhere Nowhere) as [?[??]].
    destruct (decide (itag data = tg)).
    + rewrite bool_decide_eq_true_2 in Nowhere; [|assumption].
      simpl in *; discriminate.
    + intros [|[|]].
      * contradiction.
      * apply IHtr1; assumption.
      * apply IHtr2; assumption.
  - intro nEx.
    apply absent_nowhere.
    split; [|split].
    + destruct (decide (itag data = tg)).
      * exfalso. apply nEx. auto.
      * rewrite bool_decide_eq_false_2; auto.
    + apply IHtr1. auto.
    + apply IHtr2. auto.
Qed.

Lemma absent_determined tr tg :
  tree_count_tg tg tr = 0 ->
  forall it, tree_item_determined tg it tr.
Proof.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [auto|].
  rewrite absent_nowhere.
  intros [Absent0 [Absent1 Absent2]] it.
  split; [|split].
  + intro. rewrite /has_tag bool_decide_eq_true_2 in Absent0; [discriminate|assumption].
  + apply IHtr1. assumption.
  + apply IHtr2. assumption.
Qed.

Lemma unique_lookup tr tg :
  tree_unique tg tr ->
  exists it, tree_item_determined tg it tr.
Proof.
  rewrite /tree_unique.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [intro; discriminate|].
  rewrite /has_tag.
  destruct (decide (IsTag tg data)).
  - rewrite bool_decide_eq_true_2; [|assumption].
    intro Found. destruct (unique_found_here Found).
    exists data; split; [|split].
    + tauto.
    + apply absent_determined. assumption.
    + apply absent_determined. assumption.
  - rewrite bool_decide_eq_false_2; [|assumption].
    simpl.
    intro Find. destruct (unique_somewhere Find) as [[Found ?]|[Found ?]].
    + destruct (IHtr1 Found) as [it ?].
      exists it; split; [|split].
      * tauto.
      * assumption.
      * apply absent_determined. assumption.
    + destruct (IHtr2 Found) as [it ?].
      exists it; split; [|split].
      * tauto.
      * apply absent_determined. assumption.
      * assumption.
Qed.

Lemma exists_determined_exists tr tg it :
  tree_contains tg tr ->
  tree_item_determined tg it tr ->
  exists_node (eq it) tr.
Proof.
  move=> Contains Det.
  induction tr; simpl in *; auto.
  destruct Det as [?[??]].
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
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; auto.
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
  induction tr as [|data ? IHtr1 ? IHtr2]; intros tr' Success; simpl in *.
  - inversion Success; auto.
  - destruct (destruct_joined _ _ _ _ Success) as [data' [tr1' [tr2' [EqTr' [EqData' [EqTr1' EqTr2']]]]]].
    rewrite IHtr1; [|eapply EqTr1'].
    rewrite IHtr2; [|eapply EqTr2'].
    subst; simpl.
    split; intro H; destruct H as [H[??]]; try repeat split; try assumption.
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

Lemma join_map_eqv_rel
  {t t' tr tr' fn}
  (PreservesTags : forall it it', fn it = Some it' -> itag it = itag it')
  (Success : join_nodes (map_nodes fn tr) = Some tr')
  : ParentChildIn t t' tr <-> ParentChildIn t t' tr'.
Proof.
  unfold ParentChildIn.
  rewrite join_map_eqv_strict_rel; eauto.
Qed.

Lemma insert_produces_StrictParentChild t (ins:item) (tr:tree item) :
  ~IsTag t ins ->
  StrictParentChildIn t ins.(itag) (insert_child_at tr ins (IsTag t)).
Proof.
  intro Nott.
  unfold StrictParentChildIn.
  induction tr as [|data ????]; simpl; auto.
destruct (decide (IsTag t data)) eqn:Found; simpl.
  - try repeat split; auto.
    intro H; left; easy.
  - try repeat split; auto.
    intro H; contradiction.
Qed.

Lemma insert_produces_ParentChild t tg (ins:item) (tr:tree item) :
  IsTag tg ins ->
  tg ≠ t ->
  ParentChildIn t tg (insert_child_at tr ins (IsTag t)).
Proof.
  move=> Tg Ne.
  right.
  assert (~IsTag t ins) as NotTg by (intro H; rewrite <- H in Ne; rewrite <- Tg in Ne; contradiction).
  pose proof (insert_produces_StrictParentChild _ _ tr NotTg) as H.
  rewrite Tg in H; assumption.
Qed.

Lemma StrictParentChild_transitive t t' t'' (tr:tree item) :
  StrictParentChildIn t t' tr ->
  StrictParentChildIn t' t'' tr ->
  StrictParentChildIn t t'' tr.
Proof.
  rewrite /StrictParentChildIn /HasStrictChildTag.
  induction tr as [|?? IHtr1 tr2 IHtr2]; simpl; auto.
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
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; auto.
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
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; auto.
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

Lemma inserted_determined (tgp tg:tag) (ins:item) (tr:tree item) :
  IsTag tg ins ->
  ~tree_contains tg tr ->
  tree_item_determined tg ins (insert_child_at tr ins (IsTag tgp)).
Proof.
  intros Tg Fresh.
  unfold tree_item_determined.
  unfold tree_contains in Fresh; rewrite <- every_not_eqv_not_exists in Fresh.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl in *; auto.
  destruct Fresh as [?[??]].
  destruct (decide (IsTag tgp data)).
  - try repeat split; [|apply IHtr1; assumption|apply IHtr2; assumption].
    simpl; intro; contradiction.
  - try repeat split; [|apply IHtr1; assumption|apply IHtr2; assumption].
    simpl; intro; contradiction.
Qed.

Lemma inserted_count_sum (tgp tg : tag) (ins : item) (tr : tree item) :
  IsTag tg ins ->
  tg ≠ tgp ->
  tree_count_tg tg (insert_child_at tr ins (IsTag tgp))
  = tree_count_tg tg tr + tree_count_tg tgp tr.
Proof.
  intros Tg Ne.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [auto|].
  destruct (decide _) as [Tgp|nTgp]; simpl.
  + rewrite IHtr1.
    rewrite IHtr2.
    rewrite /has_tag.
    rewrite (bool_decide_eq_true_2 _ Tgp).
    assert (~IsTag tg data) as nTgd. { intro Tgd. apply Ne. unfold IsTag in *. congruence. }
    rewrite (bool_decide_eq_false_2 _ nTgd).
    rewrite (bool_decide_eq_true_2 _ Tg).
    lia.
  + rewrite IHtr1.
    rewrite IHtr2.
    rewrite /has_tag.
    rewrite (bool_decide_eq_false_2 _ nTgp).
    lia.
Qed.

Lemma inserted_unique (tgp tg : tag) (ins : item) (tr : tree item) :
  IsTag tg ins ->
  ~tree_contains tg tr ->
  tree_unique tgp tr ->
  tree_unique tg (insert_child_at tr ins (IsTag tgp)).
Proof.
  intros Tg nEx Unq.
  rewrite /tree_unique in Unq |- *.
  rewrite <- count_0_not_exists in nEx.
  rewrite inserted_count_sum.
  + lia.
  + assumption.
  + intro Eq. rewrite Eq in nEx. congruence.
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
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl in *; try contradiction.
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

Lemma create_child_isSome tr tgp tgc pk rk cid :
  forall cids tr',
  create_child cids tgp tgc pk rk cid tr = Some tr' ->
  tr' = insert_child_at tr (create_new_item tgc pk rk cid) (IsTag tgp).
Proof.
  move=> ? tr' CreateChild.
  unfold create_child in CreateChild.
  injection CreateChild.
  auto.
Qed.

Lemma new_item_has_tag tg pk rk cid :
  IsTag tg (create_new_item tg pk rk cid).
Proof.
  unfold create_new_item.
  unfold IsTag; simpl; reflexivity.
Qed.

Lemma insertion_contains tr tgp tgc pk rk cid :
  forall cids tr',
  tree_contains tgp tr ->
  create_child cids tgp tgc pk rk cid tr = Some tr' ->
  tree_contains tgc tr'.
Proof.
  move=> ? tr' ContainsParent CreateChild.
  unfold tree_contains in *.
  pose proof (create_child_isSome tr tgp tgc _ _ _ _ _ CreateChild) as Insert.
  rewrite Insert.
  apply insert_true_produces_exists.
  - apply new_item_has_tag.
  - exact ContainsParent.
Qed.

Lemma insertion_order_nonstrictparent tr tg tg' :
  tree_contains tg' tr ->
  ~tree_contains tg tr ->
  forall tgp cids pk rk cid tr',
  tree_contains tgp tr ->
  create_child cids tgp tg pk rk cid tr = Some tr' ->
  ~StrictParentChildIn tg tg' tr'.
Proof.
  move=> Present Fresh tgp ???? tr' ParentPresent Insert Contra.
  unfold create_child in Insert.
  injection Insert; intros; subst; clear Insert.
  eapply inserted_not_strict_parent with (ins := (create_new_item tg _ _ _)).
  - apply ParentPresent.
  - simpl; apply Fresh.
  - apply Present.
  - apply Contra.
Qed.

Lemma insertion_order_nonparent tr tg tg' :
  tree_contains tg' tr ->
  ~tree_contains tg tr ->
  forall tgp cids pk rk cid tr',
  tree_contains tgp tr ->
  create_child cids tgp tg pk rk cid tr = Some tr' ->
  ~ParentChildIn tg tg' tr'.
Proof.
  intros; intro Related.
  destruct Related.
  - subst; contradiction.
  - eapply (insertion_order_nonstrictparent _ tg tg'); eauto.
Qed.

Lemma tree_determined_specifies_tag tr tg it :
  tree_contains tg tr ->
  tree_item_determined tg it tr ->
  itag it = tg.
Proof.
  rewrite /tree_contains /tree_item_determined.
  rewrite exists_node_eqv_existential.
  rewrite every_node_eqv_universal.
  intros [n [Exn Tgn]] Every.
  rewrite <- (Every n); auto.
Qed.


Lemma create_child_determined tr tgp pk rk cid tg :
  tree_contains tgp tr ->
  ~tree_contains tg tr ->
  forall cids tr',
  create_child cids tgp tg pk rk cid tr = Some tr' ->
  (
    tree_contains tg tr'
    /\ tree_item_determined tg (create_new_item tg pk rk cid) tr'
  ).
Proof.
  intros ContainsTgp FreshTg cids tr' CreateChild.
  pose proof (create_child_isSome _ _ _ _ _ _ _ _ CreateChild) as Insertion.
  subst.
  pose ins := create_new_item tg pk rk cid.
  assert (itag ins = tg) as TgIns by (apply new_item_has_tag).
  rewrite <- TgIns.
  split.
  - eapply insert_true_produces_exists; [auto|assumption].
  - eapply inserted_determined; simpl; assumption.
Qed.

Lemma create_new_item_uniform_perm tg pk rk cid z :
  item_lazy_perm_at_loc (create_new_item tg pk rk cid) z = {|
    initialized := PermLazy;
    perm := pointer_kind_to_perm pk
  |}.
Proof.
  unfold item_lazy_perm_at_loc.
  unfold create_new_item; simpl.
  unfold init_perms.
  rewrite lookup_empty; simpl.
  reflexivity.
Qed.

Lemma create_new_item_perm_prop prop tg pk rk cid z :
  prop (pointer_kind_to_perm pk) ->
  prop (perm (item_lazy_perm_at_loc (create_new_item tg pk rk cid) z)).
Proof. rewrite create_new_item_uniform_perm; simpl; tauto. Qed.

Lemma create_new_item_prot_prop prop tg pk rk cid :
  let s := pointer_kind_to_strength pk in
  let prot := retag_kind_to_prot cid rk s in
  prop (prot) ->
  prop (iprot (create_new_item tg pk rk cid)).
Proof. simpl; tauto. Qed.

Lemma create_child_preserves_determined tg it tr tr':
  forall tg' cids tgp pk rk cid,
  tg ≠ tg' ->
  tree_item_determined tg it tr ->
  create_child cids tgp tg' pk rk cid tr = Some tr' ->
  tree_item_determined tg it tr'.
Proof.
  move=> ?????? Ne.
  rewrite /tree_item_determined every_node_eqv_universal every_node_eqv_universal.
  move=> Unq CreateChild.
  injection CreateChild; intro; subst.
  intro n; specialize Unq with n.
  move=> Unq' Tg; apply Unq; [|assumption].
  eapply insert_false_infer_exists; [|exact Unq'].
  assert (forall it it', itag it ≠ itag it' -> it ≠ it') as Deterministic. {
    clear; intros it it'; destruct it; destruct it'; simpl.
    intros NEq Eq; injection Eq; intros; contradiction.
  } apply Deterministic.
  rewrite new_item_has_tag.
  rewrite Tg.
  assumption.
Qed.


Lemma create_child_preserves_count tg tr tr':
  forall tg' cids tgp pk rk cid,
  tg ≠ tg' ->
  create_child cids tgp tg' pk rk cid tr = Some tr' ->
  tree_count_tg tg tr = tree_count_tg tg tr'.
Proof.
  intros tg' cids tgp pk rk cid Ne.
  generalize dependent tr'.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl in *; intros tr' Create; inversion Create; [reflexivity|].
  destruct (decide (IsTag tgp data)).
  + simpl.
    rewrite /has_tag.
    assert (~IsTag tg (create_new_item tg' pk rk cid)) as NotTg. {
      rewrite /create_new_item /IsTag //=.
    }
    erewrite IHtr1; [|reflexivity].
    erewrite IHtr2; [|reflexivity].
    rewrite (bool_decide_eq_false_2 _ NotTg).
    lia.
  + simpl.
    erewrite IHtr1; [|reflexivity].
    erewrite IHtr2; [|reflexivity].
    reflexivity.
Qed.

Lemma tree_determined_unify
  {tg tr it it'}
  (Ex : tree_contains tg tr)
  (Unq : tree_item_determined tg it tr)
  (Unq' : tree_item_determined tg it' tr)
  : it = it'.
Proof.
  rewrite /tree_item_determined /tree_contains in Ex, Unq, Unq'.
  repeat rewrite every_node_eqv_universal in Ex, Unq, Unq'.
  repeat rewrite exists_node_eqv_existential in Ex, Unq, Unq'.
  destruct Ex as [it0 [??]].
  assert (it0 = it) by (apply Unq; assumption).
  assert (it0 = it') by (apply Unq'; assumption).
  subst; reflexivity.
Qed.

Lemma tree_apply_access_only_cares_about_rel
  {tr} {fn : call_id_set -> rel_pos -> Z * nat -> tree.app item} {cids access_tag range}
  {tr1 tr2}
  (Agree : forall tg tg', ParentChildIn tg tg' tr1 <-> ParentChildIn tg tg' tr2)
  : join_nodes (map_nodes (fun it => fn cids (rel_dec tr1 access_tag it.(itag)) range it) tr)
  = join_nodes (map_nodes (fun it => fn cids (rel_dec tr2 access_tag it.(itag)) range it) tr).
Proof.
  induction tr as [|data sibling IHsibling child IHchild]; [simpl; reflexivity|].
  simpl.
  rewrite IHsibling; clear IHsibling.
  rewrite IHchild; clear IHchild.
  unfold rel_dec.
  f_equal. f_equal.
  destruct (decide (ParentChildIn _ _ _)) as [R1|R1].
  all: destruct (decide (ParentChildIn _ _ _)) as [R1'|R1'].
  all: destruct (decide (ParentChildIn _ _ _)) as [R2|R2].
  all: destruct (decide (ParentChildIn _ _ _)) as [R2'|R2'].
  all: try reflexivity.
  all: rewrite <- Agree in R2'; auto; try contradiction.
  all: rewrite <- Agree in R2; auto; try contradiction.
  all: apply Subtree; left; simpl.
Qed.

Lemma not_strict_parent_of_self
  {tg tr} :
  tree_contains tg tr ->
  ~StrictParentChildIn tg tg tr.
Proof.
  rewrite /StrictParentChildIn.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; intros Ex; [tauto|].
  intros [Here [Sub1 Sub2]].
  destruct Ex as [Ex0|[Ex1|Ex2]].
  + apply IHtr2; [|assumption]. apply Here. assumption.
  + apply IHtr1; [|assumption]. apply Ex1.
  + apply IHtr2; [|assumption]. apply Ex2.
Qed.

Lemma cousins_different
  {tr} tg1 tg2 :
  rel_dec tr tg1 tg2 = Cousin ->
  tg1 ≠ tg2.
Proof.
  rewrite /rel_dec.
  destruct (decide _), (decide _) as [|nRel].
  all: try congruence.
  intros _ Eq. subst.
  apply nRel.
  left. reflexivity.
Qed.

Lemma exists_subtree_increasing
  {X} {tr : tree X} {P Q} :
  (forall br, P br -> Q br) ->
  exists_subtree P tr ->
  exists_subtree Q tr.
Proof.
  induction tr as [|?? IHtr1 ? IHtr2]; simpl; [tauto|].
  intros Impl [Here|[Ex1|Ex2]].
  - left. apply Impl. assumption.
  - right. left. apply IHtr1; assumption.
  - right. right. apply IHtr2; assumption.
Qed.


Lemma find_unique_subtree
  {tr tg} :
  tree_unique tg tr ->
  exists br,
    exists_subtree (eq br) tr
    /\ IsTag tg (root br).
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; [rewrite /tree_unique /=; discriminate|].
  intros Unq.
  rewrite /tree_unique /= in Unq.
  destruct (unique_somewhere_3way Unq) as [ [H0 _] |[ [_ [H1 _]] | [_ [_ H2]] ]].
  - exists (data, tr1, tr2).
    split; [left; reflexivity|].
    simpl. rewrite /has_tag in H0.
    destruct (decide (IsTag tg data)); [assumption|].
    rewrite bool_decide_eq_false_2 in H0; [discriminate|assumption].
  - destruct (IHtr1 H1) as [br1 [??]].
    exists br1. split; [|assumption]. right; left; assumption.
  - destruct (IHtr2 H2) as [br2 [??]].
    exists br2. split; [|assumption]. right; right; assumption.
Qed.

(* FIXME: these proofs ane absolutely horrible, refactor them. *)
Lemma unique_only_one_subtree
  {tr tg br1 br2} :
  tree_unique tg tr ->
  exists_subtree (eq br1) tr ->
  exists_subtree (eq br2) tr ->
  IsTag tg (root br1) ->
  IsTag tg (root br2) ->
  br1 = br2.
Proof.
  induction tr as [|data tr1 IHtr1 tr2 IHtr2]; simpl; [tauto|].
  intros Unq Sub1 Sub2 Tg1 Tg2.
  destruct Sub1 as [Here1|[Sub11|Sub12]], Sub2 as [Here2|[Sub21|Sub22]].
  - (* easy *) congruence.
  - (* too many tags: one here, one in tr1 *)
    assert ((if has_tag tg data then 1 else 0) = 1). {
      rewrite /has_tag. rewrite bool_decide_eq_true_2; subst; auto.
    }
    assert (tree_count_tg tg tr1 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr1) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq.
    lia.
  - (* too many tags: one here, one in tr2 *)
    assert ((if has_tag tg data then 1 else 0) = 1). {
      rewrite /has_tag. rewrite bool_decide_eq_true_2; subst; auto.
    }
    assert (tree_count_tg tg tr2 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr2) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq.
    lia.
  - (* too many tags: one in tr1, one here *)
    assert ((if has_tag tg data then 1 else 0) = 1). {
      rewrite /has_tag. rewrite bool_decide_eq_true_2; subst; auto.
    }
    assert (tree_count_tg tg tr1 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr1) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq.
    lia.
  - (* recurse left *)
    assert (tree_count_tg tg tr1 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr1) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq.
    assert (tree_count_tg tg tr1 = 1) by lia.
    apply IHtr1; assumption.
  - (* too many tags: one in tr1, one in tr2 *)
    assert (tree_count_tg tg tr1 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr1) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    assert (tree_count_tg tg tr2 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr2) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq. lia.
  - (* too many tags: one in tr2, one here *)
    assert ((if has_tag tg data then 1 else 0) = 1). {
      rewrite /has_tag. rewrite bool_decide_eq_true_2; subst; auto.
    }
    assert (tree_count_tg tg tr2 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr2) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq.
    lia.
  - (* too many tags: one in tr2, one in tr1 *)
    assert (tree_count_tg tg tr1 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr1) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    assert (tree_count_tg tg tr2 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr2) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq. lia.
  - (* recurse right *)
    assert (tree_count_tg tg tr2 ≥ 1). {
      rewrite count_gt0_exists.
      enough (exists_subtree (compose (IsTag tg) root) tr2) as Root.
      + rewrite -exists_node_iff_exists_root in Root. assumption.
      + eapply exists_subtree_increasing; [|eassumption].
        intros; subst. assumption.
    }
    rewrite /tree_unique /= in Unq.
    assert (tree_count_tg tg tr2 = 1) by lia.
    apply IHtr2; assumption.
Qed.

Lemma unique_exists_iff_unique
  {tr prop} tg :
  tree_unique tg tr ->
  exists_subtree (fun br => IsTag tg (root br) /\ prop br) tr
  <-> every_subtree (fun br => IsTag tg (root br) -> prop br) tr.
Proof.
  intros Unq. split.
  - intros Ex.
    rewrite every_subtree_eqv_universal.
    rewrite exists_subtree_eqv_existential in Ex.
    intros br Sub Tg.
    destruct Ex as [br' [Ex' [Tg' Prop']]].
    assert (br = br'). { eapply unique_only_one_subtree; eauto. }
    subst. assumption.
  - intros All.
    rewrite every_subtree_eqv_universal in All.
    rewrite exists_subtree_eqv_existential.
    destruct (find_unique_subtree Unq) as [br [Sub Tg]].
    exists br.
    specialize (All br Sub Tg).
    split; last split; assumption.
Qed.

Lemma unique_found_branch_1
  {data tr1 tr2} tg :
  tree_unique tg (branch data tr1 tr2) ->
  tree_unique tg tr1 ->
  ~tree_contains tg tr2 /\ ~IsTag tg data.
Proof.
  rewrite /tree_unique.
  intros Unq Unq'.
  simpl in Unq.
  destruct (unique_somewhere_3way Unq) as [ [?[??]] |[ [H[??]] | [?[??]] ]]; [congruence| |congruence].
  split; first (rewrite <- count_0_not_exists; assumption).
  intro Tg. rewrite /has_tag in H.
  rewrite bool_decide_eq_true_2 in H; [|assumption].
  congruence.
Qed.

Lemma unique_found_branch_2
  {data tr1 tr2} tg :
  tree_unique tg (branch data tr1 tr2) ->
  tree_unique tg tr2 ->
  ~tree_contains tg tr1 /\ ~IsTag tg data.
Proof.
  rewrite /tree_unique.
  intros Unq Unq'.
  simpl in Unq.
  destruct (unique_somewhere_3way Unq) as [ [?[??]] |[ [?[??]] | [H[??]] ]]; [congruence|congruence| ].
  split; first (rewrite <- count_0_not_exists; assumption).
  intro Tg. rewrite /has_tag in H.
  rewrite bool_decide_eq_true_2 in H; [|assumption].
  congruence.
Qed.

Lemma unique_strict_parent_child_focus_1
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr1 ->
  tree_unique tg2 tr1 ->
  StrictParentChildIn tg1 tg2 tr1
  <-> StrictParentChildIn tg1 tg2 (branch data tr1 tr2).
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /StrictParentChildIn.
  simpl; split.
  + intro P1.
    destruct (unique_found_branch_1 _ Unq1 Unq1') as [Absent NotTg].
    try repeat split.
    - intro; contradiction.
    - assumption.
    - rewrite every_subtree_eqv_universal.
      intros br Sub Tg.
      exfalso.
      apply Absent.
      enough (exists_subtree (compose (IsTag tg1) root) tr2) as FoundTg.
      * rewrite <- exists_node_iff_exists_root in FoundTg.
        exact FoundTg.
      * eapply exists_subtree_increasing; [|eassumption].
        simpl. intros. subst. auto.
  + intro P1.
    apply P1.
Qed.

Lemma unique_strict_parent_child_focus_2
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr2 ->
  tree_unique tg2 tr2 ->
  StrictParentChildIn tg1 tg2 tr2
  <-> StrictParentChildIn tg1 tg2 (branch data tr1 tr2).
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /StrictParentChildIn.
  simpl; split.
  + intro P1.
    destruct (unique_found_branch_2 _ Unq1 Unq1') as [Absent NotTg].
    try repeat split.
    - intro; contradiction.
    - rewrite every_subtree_eqv_universal.
      intros br Sub Tg.
      exfalso.
      apply Absent.
      enough (exists_subtree (compose (IsTag tg1) root) tr1) as FoundTg.
      * rewrite <- exists_node_iff_exists_root in FoundTg.
        exact FoundTg.
      * eapply exists_subtree_increasing; [|eassumption].
        simpl. intros. subst. auto.
    - assumption.
  + intro P1.
    apply P1.
Qed.

Lemma unique_parent_child_focus_1
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr1 ->
  tree_unique tg2 tr1 ->
  ParentChildIn tg1 tg2 tr1
  <-> ParentChildIn tg1 tg2 (branch data tr1 tr2).
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /ParentChildIn.
  rewrite unique_strict_parent_child_focus_1; first reflexivity; assumption.
Qed.

Lemma unique_parent_child_focus_2
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr2 ->
  tree_unique tg2 tr2 ->
  ParentChildIn tg1 tg2 tr2
  <-> ParentChildIn tg1 tg2 (branch data tr1 tr2).
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /ParentChildIn.
  rewrite unique_strict_parent_child_focus_2; first reflexivity; assumption.
Qed.


Lemma cousins_in_branch_1
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr1 ->
  tree_unique tg2 tr1 ->
  rel_dec (branch data tr1 tr2) tg1 tg2 = Cousin
  <-> rel_dec tr1 tg1 tg2 = Cousin.
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /rel_dec.
  pose proof (unique_parent_child_focus_1 _ _ Unq1 Unq2 Unq1' Unq2') as [].
  pose proof (unique_parent_child_focus_1 _ _ Unq2 Unq1 Unq2' Unq1') as [].
  repeat destruct (decide _); try tauto.
Qed.

Lemma cousins_in_branch_2
  {data tr1 tr2} tg1 tg2 :
  tree_unique tg1 (branch data tr1 tr2) ->
  tree_unique tg2 (branch data tr1 tr2) ->
  tree_unique tg1 tr2 ->
  tree_unique tg2 tr2 ->
  rel_dec (branch data tr1 tr2) tg1 tg2 = Cousin
  <-> rel_dec tr2 tg1 tg2 = Cousin.
Proof.
  intros Unq1 Unq2 Unq1' Unq2'.
  rewrite /rel_dec.
  pose proof (unique_parent_child_focus_2 _ _ Unq1 Unq2 Unq1' Unq2') as [].
  pose proof (unique_parent_child_focus_2 _ _ Unq2 Unq1 Unq2' Unq1') as [].
  repeat destruct (decide _); try tauto.
Qed.

Lemma cousins_find_common_ancestor
  {tr} tg1 tg2 :
  tree_unique tg1 tr ->
  tree_unique tg2 tr ->
  rel_dec tr tg1 tg2 = Cousin ->
  exists_subtree (fun '(data, tr1, tr2) =>
    (tree_contains tg1 tr1 /\ tree_contains tg2 tr2)
    \/ (tree_contains tg2 tr1 /\ tree_contains tg1 tr2)
    \/ (IsTag tg1 data /\ tree_contains tg2 tr1)
    \/ (IsTag tg2 data /\ tree_contains tg1 tr1)
  ) tr.
Proof.
  rewrite /tree_unique.
  intros Unq1 Unq2 Rel.

  assert (every_subtree (fun '(root, _, br2) => IsTag tg1 root -> ~tree_contains tg2 br2) tr)
    as Unrel1. {
      rewrite /rel_dec in Rel.
      destruct (decide _) as [|nRel1], (decide _); try discriminate.
      rewrite every_subtree_eqv_universal.
      intros [[data tr1] tr2] Sub Tg Ex.
      apply nRel1.
      rewrite /ParentChildIn. right. rewrite /StrictParentChildIn.
      rewrite <- unique_exists_iff_unique; [|assumption].
      rewrite exists_subtree_eqv_existential.
      eexists; split; [eassumption|auto].
  }

  assert (every_subtree (fun '(root, _, br2) => IsTag tg2 root -> ~tree_contains tg1 br2) tr)
    as Unrel2. {
      rewrite /rel_dec in Rel.
      destruct (decide _), (decide _) as [|nRel2]; try discriminate.
      rewrite every_subtree_eqv_universal.
      intros [[data tr1] tr2] Sub Tg Ex.
      apply nRel2.
      rewrite /ParentChildIn. right. rewrite /StrictParentChildIn.
      rewrite <- unique_exists_iff_unique; [|assumption].
      rewrite exists_subtree_eqv_existential.
      eexists; split; [eassumption|auto].
  }

  induction tr as [|data ? IHtr1 ? IHtr2]; simpl in *; [discriminate|].
  rewrite /has_tag in Unq1, Unq2.
  destruct (decide (IsTag tg1 data)), (decide (IsTag tg2 data)).
  - exfalso. eapply cousins_different; [eassumption|].
    unfold IsTag in *; congruence.
  - rewrite bool_decide_eq_false_2 /= in Unq2; [|assumption].
    destruct (unique_somewhere Unq2) as [[Unq21 _] | [Unq22 _]].
    + left. right. right. left.
      split; [assumption|].
      apply unique_exists.
      assumption.
    + (* absurd because they would be related *)
      exfalso.
      apply Unrel1; [assumption|].
      apply unique_exists.
      assumption.
  - rewrite bool_decide_eq_false_2 /= in Unq1; [|assumption].
    destruct (unique_somewhere Unq1) as [[Unq11 _] | [Unq12 _]].
    + left. right. right. right.
      split; [assumption|].
      apply unique_exists.
      assumption.
    + (* absurd because they would be related *)
      exfalso.
      apply Unrel2; [assumption|].
      apply unique_exists.
      assumption.
  - pose proof Unq1 as Unq1_remember.
    pose proof Unq2 as Unq2_remember.
    rewrite bool_decide_eq_false_2 /= in Unq1; [|assumption].
    rewrite bool_decide_eq_false_2 /= in Unq2; [|assumption].
    destruct (unique_somewhere Unq1) as [[Unq11 _] | [Unq12 _]],
             (unique_somewhere Unq2) as [[Unq21 _] | [Unq22 _]].
    + (* recurse left *)
      right. left.
      apply IHtr1.
      * apply Unq11.
      * apply Unq21.
      * eapply cousins_in_branch_1; eassumption.
      * apply Unrel1.
      * apply Unrel2.
    + (* found the common ancestor *)
      left. left. split; apply unique_exists; assumption.
    + (* found the common ancestor *)
      left. right. left. split; apply unique_exists; assumption.
    + (* recurse right *)
      right. right.
      apply IHtr2.
      * apply Unq12.
      * apply Unq22.
      * eapply cousins_in_branch_2; eassumption.
      * apply Unrel1.
      * apply Unrel2.
Qed.

Lemma subtree_count_lower_bound
  tr tg :
  every_subtree (fun '(data, tr1, tr2) =>
    tree_count_tg tg tr ≥ tree_count_tg tg tr1 + tree_count_tg tg tr2
  ) tr.
Proof.
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [tauto|].
  split; last split.
  - lia.
  - rewrite every_subtree_eqv_universal in IHtr1.
    rewrite every_subtree_eqv_universal.
    intros br Sub. specialize (IHtr1 br Sub).
    destruct br as [[??]?].
    lia.
  - rewrite every_subtree_eqv_universal in IHtr2.
    rewrite every_subtree_eqv_universal.
    intros br Sub. specialize (IHtr2 br Sub).
    destruct br as [[??]?].
    lia.
Qed.

Lemma contains_child
  {tr tg tg'} :
  ParentChildIn tg tg' tr ->
  tree_contains tg tr ->
  tree_contains tg' tr.
Proof.
  intros [Eq|Strict]; [subst; tauto|].
  induction tr as [|data ? IHtr1 ? IHtr2]; simpl; [tauto|].
  intros [Here|[Ex1|Ex2]].
  - simpl in Strict. right; right.
    apply Strict. assumption.
  - right; left. apply IHtr1; [|assumption].
    apply Strict.
  - right; right. apply IHtr2; [|assumption].
    apply Strict.
Qed.

Lemma strict_child_in_subtree
  {tg tg' tr data tr1 tr2} :
  StrictParentChildIn tg tg' tr ->
  exists_subtree (eq (data, tr1, tr2)) tr ->
  StrictParentChildIn tg tg' tr1 /\ StrictParentChildIn tg tg' tr2.
Proof.
  rewrite /StrictParentChildIn.
  repeat rewrite every_subtree_eqv_universal.
  intros Child Sub.
  split; intros br Sub' Root.
  all: apply Child; [|eassumption].
  all: eapply exists_subtree_transitive; [eassumption|].
  - simpl; right; left; assumption.
  - simpl; right; right; assumption.
Qed.

Lemma cousins_have_disjoint_strict_children
  {tr tg} tg1 tg2 :
  tree_unique tg tr ->
  tree_unique tg1 tr ->
  tree_unique tg2 tr ->
  rel_dec tr tg1 tg2 = Cousin ->
  StrictParentChildIn tg1 tg tr ->
  StrictParentChildIn tg2 tg tr ->
  False.
Proof.
  intros Unique Ex1 Ex2 Cousins Strict1 Strict2.
  pose proof (cousins_find_common_ancestor _ _ Ex1 Ex2 Cousins) as CommonAncestor.
  rewrite exists_subtree_eqv_existential in CommonAncestor.
  destruct CommonAncestor as [[[data tr1] tr2] [EqSub Separate]].
  pose proof (subtree_count_lower_bound tr tg) as CountAtAncestor.
  rewrite every_subtree_eqv_universal in CountAtAncestor.
  specialize (CountAtAncestor (data, tr1, tr2) EqSub).
  simpl in *.
  assert (tree_count_tg tg tr1 ≥ 1). {
    destruct Separate as [[Ex1' _] | [[Ex2' _]| [[_ Ex2']|[_ Ex1']]]].
    + rewrite count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict1 EqSub).
    + apply count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict2 EqSub).
    + apply count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict2 EqSub).
    + apply count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict1 EqSub).
  }
  assert (tree_count_tg tg tr2 ≥ 1). {
    destruct Separate as [[_ Ex1'] | [[_ Ex2']|[[Ex2' _] | [Ex1' _]]]].
    + rewrite count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict2 EqSub).
    + apply count_gt0_exists.
      eapply contains_child; [right|eassumption].
      apply (strict_child_in_subtree Strict1 EqSub).
    + apply count_gt0_exists.
      unfold StrictParentChildIn in *.
      rewrite every_subtree_eqv_universal in Strict1.
      apply (Strict1 (data, tr1, tr2) EqSub Ex2').
    + apply count_gt0_exists.
      unfold StrictParentChildIn in *.
      rewrite every_subtree_eqv_universal in Strict2.
      apply (Strict2 (data, tr1, tr2) EqSub Ex1').
  }
  assert (tree_count_tg tg tr ≥ 2) as Twice by lia.
  rewrite Unique in Twice.
  lia.
Qed.

Lemma StrictParentChild_ParentChild
  {tr tg1 tg2 tg3} :
  StrictParentChildIn tg1 tg2 tr ->
  ParentChildIn tg2 tg3 tr ->
  StrictParentChildIn tg1 tg3 tr.
Proof.
  intros Strict12 [Eq|Strict23].
  + subst. assumption.
  + eapply StrictParentChild_transitive; eassumption.
Qed.

Lemma ParentChild_StrictParentChild
  {tr tg1 tg2 tg3} :
  ParentChildIn tg1 tg2 tr ->
  StrictParentChildIn tg2 tg3 tr ->
  StrictParentChildIn tg1 tg3 tr.
Proof.
  intros [Eq|Strict12] Strict23.
  + subst. assumption.
  + eapply StrictParentChild_transitive; eassumption.
Qed.


Lemma cousins_have_disjoint_children
  {tr tg} tg1 tg2
  :
  tree_unique tg tr ->
  tree_unique tg1 tr ->
  tree_unique tg2 tr ->
  rel_dec tr tg1 tg2 = Cousin ->
  ParentChildIn tg1 tg tr ->
  ParentChildIn tg2 tg tr ->
  False.
Proof.
  intros Unique Ex1 Ex2 Cousins Parent1 Parent2.
  assert (tg1 ≠ tg2). { eapply cousins_different. eassumption. }
  unfold ParentChildIn in *.
  destruct Parent1, Parent2; subst.
  + congruence.
  + rewrite /rel_dec in Cousins.
    destruct (decide _). 1: {
      eapply not_strict_parent_of_self; [eapply unique_exists; eassumption|].
      eapply StrictParentChild_ParentChild; eassumption.
    }
    destruct (decide _) as [|nRel]. 1: congruence.
    apply nRel.
    right. assumption.
  + rewrite /rel_dec in Cousins.
    destruct (decide _) as [|nRel]. 1: destruct (decide _); discriminate.
    destruct (decide _). 1: discriminate.
    apply nRel.
    right. assumption.
  + eapply cousins_have_disjoint_strict_children with (tg1 := tg1) (tg2 := tg2).
    2,3,4,5,6: eassumption.
    eassumption.
Qed.

