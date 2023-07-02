From simuliris.tree_borrows Require Import lang_base notation bor_semantics.

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

Lemma item_apply_access_preserves_tag it :
  forall kind cids rel range it',
  item_apply_access kind cids rel range it = Some it' ->
  itag it = itag it'.
Proof.
  move=> ???? it'.
  unfold item_apply_access.
  destruct (permissions_foreach _); simpl; [|intro H; inversion H].
  intro H; injection H; intros; subst.
  simpl; reflexivity.
Qed.

Lemma join_project_Exists {X} tr prop :
  forall tr',
  tree_join tr = Some tr' ->
  tree_Exists prop tr' <-> tree_Exists (fun x => exists (v:X), x = Some v /\ prop v) tr.
Proof.
  induction tr; intros tr' JoinSome.
  - simpl in JoinSome; injection JoinSome; intros; subst; tauto.
  - simpl in JoinSome.
    destruct data; simpl in *; [|inversion JoinSome].
    destruct (tree_join tr1); simpl in *; [|inversion JoinSome].
    destruct (tree_join tr2); simpl in *; [|inversion JoinSome].
    injection JoinSome; intros; subst.
    simpl.
    split; intro H; destruct H as [H0 | [H1 | H2]].
    * left. exists x; tauto.
    * right; left. rewrite <- IHtr1; [exact H1|auto].
    * right; right. rewrite <- IHtr2; [exact H2|auto].
    * left. destruct H0 as [v [SomeV Pv]]; injection SomeV; intros; subst; auto.
    * right; left. rewrite IHtr1; auto.
    * right; right. rewrite IHtr2; auto.
Qed.

Lemma tree_Exists_increasing {X} (prop prop':Tprop X) tr :
  tree_Exists prop tr ->
  (forall x, prop x -> prop' x) ->
  tree_Exists prop' tr.
Proof.
  induction tr; simpl; [tauto|].
  intros H Impl; destruct H as [H0 | [H1 | H2]].
  - left; apply Impl; auto.
  - right; left; apply IHtr1; auto.
  - right; right; apply IHtr2; auto.
Qed.

Lemma access_preserves_tags tr tg :
  forall tr' app cids range rel,
  tree_contains tg tr ->
  tree_apply_access app cids tg range tr rel = Some tr' ->
  tree_contains tg tr'.
Proof.
  move=> tr' app ??? Contains Access.
  unfold tree_apply_access in Access.
  unfold tree_contains in *.
  rewrite join_project_Exists.
  2: exact Access.
  rewrite tree_Exists_map.
  unfold compose.
  apply (tree_Exists_increasing _ _ _ Contains).




  generalize dependent tr'.
  induction tr; [inversion Contains|].
  intros tr' Access.
  unfold tree_apply_access in *.
  remember ( _ _ _ _ data) as newit.
  remember (tree_join (tree_map _ tr1)) as new1.
  remember (tree_join (tree_map _ tr2)) as new2.
  destruct newit; simpl in Read; [|inversion Read].
  destruct new1; simpl in Read; [|inversion Read].
  destruct new2; simpl in Read; [|inversion Read].
  injection Read; intros; subst.
  destruct Contains as [C0 | [C1 | C2]].
  - left.
    unfold IsTag in *; subst.
    symmetry in Heqnewit.
    rewrite (item_apply_access_preserves_tag _ _ _ _ _ _ Heqnewit).
    reflexivity.
  - right; left.
    symmetry in Heqnew1.
    apply (IHtr1 _ _ _ _ Heqnew1).


      + destruct (tree_join _); simpl in *; [|inversion H0].
        injection H0; intros; subst.
        destruct (item_apply_access _ _ _ _ data); simpl in *.
        injection Read; intros; subst.

  unfold memory_read in Read; unfold tree_apply_access in Read.


Lemma new_item_has_tag tg :
  forall perm range,
  IsTag tg (create_new_item tg perm range).
Proof.
  move=> ??.
  unfold create_new_item.
  unfold IsTag; simpl; reflexivity.
Qed.

(* fresh t -> fresh t' -> insert t -> insert t' -> ~child t t' *)
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
  apply insert_True_produces_Exists.
  - apply new_item_has_tag.
  - 

Lemma insertion_order_nonchild tr tg tg' :
  ~tree_contains tg tr ->
  ~tree_contains tg' tr ->

