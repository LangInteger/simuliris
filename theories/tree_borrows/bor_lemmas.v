From iris.prelude Require Import prelude options.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas.
From iris.prelude Require Import options.

Lemma unique_somewhere
  {a b} :
  a + b = 1 -> (a = 1 /\ b = 0) \/ (b = 1 /\ a = 0).
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

Lemma insertion_order_nonstrictparent tr tg tg' :
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

Lemma insertion_order_nonparent tr tg tg' :
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


Lemma create_child_determined tr tgp newp tg :
  tree_contains tgp tr ->
  ~tree_contains tg tr ->
  forall cids tr',
  create_child cids tgp tg newp tr = Some tr' ->
  (
    tree_contains tg tr'
    /\ tree_item_determined tg (create_new_item tg newp) tr'
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
  - eapply inserted_determined; simpl; assumption.
Qed.

Lemma create_new_item_uniform_perm tg newp z :
  item_lazy_perm_at_loc (create_new_item tg newp) z = {|
    initialized := PermLazy;
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

Lemma create_child_preserves_determined tg it tr tr':
  forall tg' cids tgp newp,
  tg ≠ tg' ->
  tree_item_determined tg it tr ->
  create_child cids tgp tg' newp tr = Some tr' ->
  tree_item_determined tg it tr'.
Proof.
  move=> ???? Ne.
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
  forall tg' cids tgp newp,
  tg ≠ tg' ->
  create_child cids tgp tg' newp tr = Some tr' ->
  tree_count_tg tg tr = tree_count_tg tg tr'.
Proof.
Admitted.


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


