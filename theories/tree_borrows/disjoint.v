From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas bor_lemmas steps_preserve.
From iris.prelude Require Import options.

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


