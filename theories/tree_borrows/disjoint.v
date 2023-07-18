From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas bor_lemmas steps_preserve.
From iris.prelude Require Import options.

(* Key lemma: converts the entire traversal to a per-node level.
   This is applicable to every permission in the accessed range, all that's needed
   to complement it should be preservation of permissions outside of said range. *)
Lemma access_effect_per_loc_within_range
  tr affected_tag access_tag pre
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  kind strong cids cids' range tr' z zpre
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt kind strong access_tag range) tr' cids')
  : exists post zpost, (
    let rel := if naive_rel_dec tr affected_tag access_tag then AccessChild else AccessForeign in
    let isprot := bool_decide (protector_is_active cids pre.(iprot)) in
    let isstrong := bool_decide (strong = ProtStrong \/ protector_is_strong pre.(iprot)) in
    apply_access_perm kind rel isprot isstrong zpre = Some zpost
    /\ tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ iprot post = iprot pre
  ).
Proof.
  inversion Step; subst.
  (* use apply_access_spec_per_node to get info on the post permission *)
  destruct (apply_access_spec_per_node _ _ _ _
    EXISTS_TAG Ex Unq
    (item_apply_access _ _) cids' range tr' (naive_rel_dec tr)
    (item_apply_access_preserves_tag _ _) ACC) as [post [SpecPost [ContainsPost UniquePost]]].
  (* and then it's per-tag work *)
  rewrite (tree_unique_specifies_tag _ _ _ Ex Unq) in SpecPost.
  symmetry in SpecPost.
  destruct (option_bind_success_step _ _ _  SpecPost) as [tmpperm [tmpSpec tmpRes]].
  injection tmpRes; intro H; subst; clear tmpRes.
  (* now down to per-location *)
  pose proof (range_foreach_spec _ _ z _ _ tmpSpec) as ForeachSpec.
  rewrite (decide_True _ _ Within) in ForeachSpec.
  destruct ForeachSpec as [lazy_perm [PermExists ForeachSpec]].
  assert (unwrap {| initialized := PermLazy; perm := initp pre |} (iperm pre !! z) = item_lazy_perm_at_loc pre z) as InitPerm. {
    unfold item_lazy_perm_at_loc. destruct (iperm pre !! z); simpl; reflexivity.
  } rewrite InitPerm in ForeachSpec.
  eexists. eexists.
  split; [|split; [|split]]; [|exact UniquePost|reflexivity|reflexivity].
  rewrite ForeachSpec.
  unfold item_lazy_perm_at_loc.
  rewrite PermExists; simpl; reflexivity.
Qed.
Arguments access_effect_per_loc_within_range {_ _ _ _} Ex Unq {_ _ _ _ _ _ _ _} Within IsPre Step.

Lemma access_effect_per_loc_outside_range
  tr affected_tag access_tag pre
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  kind strong cids cids' range tr' z zpre
  (Outside : ~range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt kind strong access_tag range) tr' cids')
  : exists post, (
    tree_unique affected_tag post tr
    /\ item_lazy_perm_at_loc post z = zpre
    /\ iprot post = iprot pre
  ).
Proof.
  inversion Step; subst.
  destruct (apply_access_spec_per_node _ _ _ _
    EXISTS_TAG Ex Unq _ _ _ _ _
    (item_apply_access_preserves_tag _ _)
    ACC) as [post [SpecPost [ContainsPost UniquePost]]].
  (* We now show that
     (1) post has zpre at loc z
     (2) post is equal to whatever item the goal refers to *)
  assert (item_lazy_perm_at_loc post z = item_lazy_perm_at_loc pre z) as SamePerm. {
    symmetry in SpecPost.
    destruct (option_bind_success_step _ _ _ SpecPost) as [perms [SpecPerms Injectable]].
    injection Injectable; intros; subst; clear Injectable.
    pose proof (range_foreach_spec _ _ z _ _ SpecPerms) as RangeForeach.
    rewrite (decide_False _ _ Outside) in RangeForeach.
    unfold item_lazy_perm_at_loc; simpl.
    rewrite RangeForeach; reflexivity.
  }
  eexists.
  split; [|split]; [exact Unq|reflexivity|reflexivity].
Qed.
Arguments access_effect_per_loc_outside_range {_ _ _ _} Ex Unq {_ _ _ _ _ _ _ _} Outside IsPre Step.

Lemma nonchild_write_reserved_to_disabled
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Reach : reach Reserved (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessWrite ProtStrong access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ reach Disabled (perm zpost)
    /\ iprot post = iprot pre
  ).
Proof.
  destruct (access_effect_per_loc_within_range Ex Unq Within IsPre Step)
    as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  exists post, zpost.
  try repeat split; auto.
  destruct (naive_rel_dec _ _ _); [contradiction|].
  destruct zpre; destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: try inversion SpecPost.
  all: simpl; tauto.
Qed.

Lemma nonchild_read_active_to_frozen
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Reach : reach Active (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead ProtStrong access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ reach Frozen (perm zpost)
    /\ reach (perm zpre) (perm zpost)
  ).
Proof.
  destruct (access_effect_per_loc_within_range Ex Unq Within IsPre Step)
    as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  exists post, zpost.
  try repeat split; auto.
  all: destruct (naive_rel_dec _ _ _); [contradiction|].
  all: destruct zpre; destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: try inversion SpecPost.
  all: simpl; tauto.
Qed.

Lemma child_write_frozen_to_ub
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Child : ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Reach : reach Frozen (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessWrite ProtStrong access_tag range) tr' cids')
  : False.
Proof.
  destruct (access_effect_per_loc_within_range Ex Unq Within IsPre Step)
    as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [|contradiction].
  destruct zpre; destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: try inversion SpecPost.
Qed.

Lemma child_read_disabled_to_ub
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Child : ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Reach : reach Disabled (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead ProtStrong access_tag range) tr' cids')
  : False.
Proof.
  destruct (access_effect_per_loc_within_range Ex Unq Within IsPre Step)
    as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [|contradiction].
  destruct zpre; destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: try inversion SpecPost.
Qed.

Lemma child_write_any_to_init_active
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Child : ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt AccessWrite ProtStrong access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ perm zpost = Active
    /\ iprot post = iprot pre
    /\ initialized zpost = PermInit
  ).
Proof.
  destruct (access_effect_per_loc_within_range Ex Unq Within IsPre Step)
    as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [|contradiction].
  exists post, zpost.
  try repeat split; try assumption.
  all: destruct (item_lazy_perm_at_loc _ _); destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: unfold apply_access_perm in SpecPost; simpl in *.
  all: destruct (perm zpre); simpl in *.
  all: destruct (initialized zpre); simpl in *.
  all: try inversion SpecPost.
  all: injection SpecPost; intro H; destruct zpost; injection H; intros; subst; simpl; reflexivity.
Qed.

Lemma child_read_any_to_init_nondis
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Child : ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead ProtStrong access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ ~reach Disabled (perm zpost)
    /\ iprot post = iprot pre
    /\ initialized zpost = PermInit
  ).
Proof.
  destruct (access_effect_per_loc_within_range Ex Unq Within IsPre Step)
    as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [|contradiction].
  exists post, zpost.
  try repeat split; try assumption.
  all: destruct (item_lazy_perm_at_loc _ _); destruct initialized; destruct perm; try contradiction.
  all: destruct (bool_decide _); simpl in *.
  all: unfold apply_access_perm in SpecPost; simpl in *.
  all: destruct (perm zpre); simpl in *.
  all: destruct (initialized zpre); simpl in *.
  all: try inversion SpecPost.
  all: injection SpecPost; intro H; destruct zpost; simpl; tauto.
Qed.


Lemma protected_nonchild_write_initialized_to_ub
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Protected : protector_is_active cids (iprot pre))
  (Initialized : initialized (item_lazy_perm_at_loc pre z) = PermInit)
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (NonDis : ~reach Disabled (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessWrite ProtStrong access_tag range) tr' cids')
  : False.
Proof.
  destruct (access_effect_per_loc_within_range Ex Unq Within IsPre Step)
    as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [contradiction|].
  rewrite bool_decide_eq_true_2 in SpecPost; [|assumption].
  destruct (item_lazy_perm_at_loc _ _); simpl in Initialized; subst.
  destruct perm; unfold apply_access_perm in SpecPost; simpl in SpecPost.
  all: inversion SpecPost.
  (* One case remaining: was already Disabled *)
  apply NonDis; simpl; tauto.
Qed.

Lemma protected_nonchild_read_initialized_active_to_ub
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Protected : protector_is_active cids (iprot pre))
  (Initialized : initialized (item_lazy_perm_at_loc pre z) = PermInit)
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Activated : perm zpre = Active)
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead ProtStrong access_tag range) tr' cids')
  : False.
Proof.
  destruct (access_effect_per_loc_within_range Ex Unq Within IsPre Step)
    as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [contradiction|].
  rewrite bool_decide_eq_true_2 in SpecPost; [|assumption].
  destruct (item_lazy_perm_at_loc _ _); simpl in Initialized; subst.
  destruct perm; unfold apply_access_perm in SpecPost; simpl in SpecPost.
  all: try inversion Activated.
  inversion SpecPost.
Qed.

Lemma protected_nonchild_read_any_to_frozen
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Protected : protector_is_active cids (iprot pre))
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead ProtStrong access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ reach Frozen (perm zpost)
  ).
Proof.
  destruct (access_effect_per_loc_within_range Ex Unq Within IsPre Step)
    as [post [zpost [SpecPost [UniqPost [PermPost ProtPost]]]]].
  destruct (naive_rel_dec _ _ _); [contradiction|].
  rewrite bool_decide_eq_true_2 in SpecPost; [|assumption].
  eexists. eexists.
  try repeat split; [exact UniqPost|].
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
    lazymatch goal with
    | Step: bor_local_step tr _ _ _ _ |- _ =>
      pose proof (bor_local_step_preserves_contains prop Step) as dest
    end
  (* Migrate a parent-child relation *)
  | context [ParentChildIn ?tg ?tg' ?tr] =>
    lazymatch goal with
    | Step : bor_local_step tr _ _ _ _,
      Ex : tree_contains tg tr,
      Ex' : tree_contains tg' tr
      |- _ =>
      pose proof prop as dest;
      rewrite (bor_local_step_eqv_rel Ex Ex' Step) in dest
    end
  (* Migrate info on a protector *)
  | context [protector_is_for_call ?old _] =>
    match goal with
    | ACC: ?old = ?new |- _ =>
      pose proof prop as dest;
      rewrite <- ACC in dest
    | ACC: ?new = ?old |- _ =>
      pose proof prop as dest;
      rewrite ACC in prop
    end
  (* failed *)
  | ?other =>
    idtac prop " of type " other " cannot be migrated"
  end.

Tactic Notation "migrate" constr(prop) "as" ident(dest) :=
  migrate prop dest.
Tactic Notation "migrate" constr(prop) :=
  let tmp := fresh "tmp" in
  migrate prop as tmp;
  clear prop;
  rename tmp into prop.


Ltac forget x :=
  repeat match goal with
  | H: context [x] |- _ => clear H
  end.

Ltac created_unique tg bindEx bindUnq :=
  match goal with
  | Rebor : bor_local_step ?tr _ (RetagBLEvt _ tg _ _) _ _ |- _ =>
    pose proof (bor_local_step_retag_produces_contains_unique Rebor) as [bindEx bindUnq]
  end.

Tactic Notation "created" constr(tg) "unique" "as" "[" ident(ex) ident(uq) "]" :=
  created_unique tg ex uq.
Tactic Notation "created" constr(tg) "unique" :=
  let ex := fresh "Exists" in
  let uq := fresh "Unique" in
  created_unique tg ex uq.

Ltac created_protected tg dest :=
  let newp := fresh "newp" in
  lazymatch goal with
  | H : protector_is_for_call (new_protector ?newp) ?cid,
    _ : context [create_new_item tg ?newp]
    |- _ =>
    assert (protector_is_for_call (iprot (create_new_item tg newp)) cid) as dest by (simpl; exact H)
  end.

Tactic Notation "created" constr(tg) "protected" "as" ident(prot) :=
  created_protected tg prot.
Tactic Notation "created" constr(tg) "protected" :=
  let prot := fresh "Protected" in
  created_protected tg prot.

Ltac created_nonparent tg other dest :=
  match goal with
  | Rebor : bor_local_step ?tr _ (RetagBLEvt _ tg _ _) _ _,
    Exother : tree_contains other ?tr
    |- _ =>
    pose proof (bor_local_step_retag_order_nonparent Exother Rebor) as dest
  end.

Tactic Notation "created" constr(tg) "nonparent" "of" constr(other) "as" ident(dest) :=
  created_nonparent tg other dest.
Tactic Notation "created" constr(tg) "nonparent" "of" constr(other) :=
  let unrel := fresh "Unrelated" in
  created_nonparent tg other unrel.

Ltac solve_reachability :=
  let p := fresh "perm" in
  multimatch goal with
  | |- reach _ _ => assumption
  | |- reach _ _ => eapply reach_reflexive; done
  | |- reach _ (perm (item_lazy_perm_at_loc (create_new_item _ _) _)) => eapply create_new_item_perm_prop
  | |- reach Frozen ?p => apply (reach_transitive Frozen Disabled p); [done|]
  end.

Lemma fwrite_cwrite_disjoint tg tg' newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cid cids0 cids1 cids2 cids3,
  tree_contains tg tr0 ->
  reach Reserved (initial_state newp) ->
  bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr1 cids1 ->
  bor_local_step tr1 cids1 (AccessBLEvt AccessWrite ProtStrong tg range1) tr2 cids2 ->
  bor_local_step tr2 cids2 (AccessBLEvt AccessWrite ProtStrong tg' range2) tr3 cids3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ?????.
  intros TgEx NonResMut Rebor Write12 Write23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Tg'Ex Tg'Unique].
  Check (bor_local_step_retag_order_nonparent ).
  created tg' nonparent of tg as Unrelated.
  forget tr0.

  (* write step 1 *)
  destruct (nonchild_write_reserved_to_disabled Tg'Ex Tg'Unique Unrelated RContains1 eq_refl ltac:(solve_reachability) Write12)
    as [post [zpost [Unique'Post [PermPost [DisPost ProtPost]]]]].
  migrate Tg'Ex.
  forget tr1.

  (* write step 2 *)
  destruct (child_write_frozen_to_ub Tg'Ex Unique'Post ltac:(left; done) RContains2 PermPost ltac:(repeat solve_reachability) Write23).
Qed.

Lemma fwrite_cread_disjoint tg tg' newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cid cids0 cids1 cids2 cids3,
  tree_contains tg tr0 ->
  reach Reserved (initial_state newp) ->
  bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr1 cids1 ->
  bor_local_step tr1 cids1 (AccessBLEvt AccessWrite ProtStrong tg range1) tr2 cids2 ->
  bor_local_step tr2 cids2 (AccessBLEvt AccessRead ProtStrong tg' range2) tr3 cids3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ????? TgEx ReachRes Rebor Write12 Read23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Tg'Ex Tg'Unique].
  created tg' nonparent of tg as Unrelated.
  migrate TgEx.
  forget tr0.

  (* write step 1 *)
  destruct (nonchild_write_reserved_to_disabled
    Tg'Ex Tg'Unique
    Unrelated
    RContains1 eq_refl
    ltac:(solve_reachability)
    Write12
  ) as [post [zpost [Unique'Post [PermPost [DisPost ProtPost]]]]].
  migrate Tg'Ex.
  forget tr1.

  (* read step 2 *)
  destruct (child_read_disabled_to_ub
    Tg'Ex Unique'Post
    ltac:(left; reflexivity)
    RContains2 PermPost
    ltac:(solve_reachability)
    Read23).
Qed.

Lemma activated_fread_cwrite_disjoint tg tg' newp range1 range2 range3:
  forall tgp tr0 tr1 tr2 tr3 tr4 cid cids0 cids1 cids2 cids3 cids4,
  tree_contains tg tr0 ->
  bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr1 cids1 ->
  bor_local_step tr1 cids1 (AccessBLEvt AccessWrite ProtStrong tg' range1) tr2 cids2 ->
  bor_local_step tr2 cids2 (AccessBLEvt AccessRead ProtStrong tg range2) tr3 cids3 ->
  bor_local_step tr3 cids3 (AccessBLEvt AccessWrite ProtStrong tg' range3) tr4 cids4 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z /\ range_contains range3 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 tr4 ?????? TgEx Rebor Write12 Read23 Write34 [z [RContains1 [RContains2 RContains3]]].
  (* reborrow step *)
  created tg' unique as [Tg'Ex Tg'Unique].
  created tg' nonparent of tg as Unrelated.
  migrate TgEx.
  forget tr0.

  (* write step 1 *)
  destruct (child_write_any_to_init_active
    Tg'Ex Tg'Unique
    ltac:(left; reflexivity)
    RContains1 eq_refl
    Write12
  ) as [post [zpost [Post'Unique [PostPerm [PostActive _]]]]].
  migrate Unrelated.
  migrate Tg'Ex.
  migrate TgEx.
  forget tr1.

  (* read step 2 *)
  rename post into pre, zpost into zpre.
  rename PostPerm into PrePerm, PostActive into PreActive.
  destruct (nonchild_read_active_to_frozen
    Tg'Ex Post'Unique
    Unrelated
    RContains2 PrePerm
    ltac:(solve_reachability)
    Read23) as [post [zpost [Tg'Unique [PostPerm [ReachFrzPost ReachPrePost]]]]].
  migrate Tg'Ex.
  forget tr2.

  (* write step 3 *)
  destruct (child_write_frozen_to_ub
    Tg'Ex Tg'Unique
    ltac:(left; reflexivity)
    RContains3 PostPerm
    ltac:(solve_reachability)
    Write34).
Qed.

Lemma protected_cwrite_fwrite_disjoint tg tg' cid newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cids0 cids1 cids2 cids3,
  tree_contains tg tr0 ->
  protector_is_for_call (new_protector newp) cid ->
  bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr1 cids1 ->
  bor_local_step tr1 cids1 (AccessBLEvt AccessWrite ProtStrong tg' range1) tr2 cids2 ->
  call_is_active cids2 cid ->
  bor_local_step tr2 cids2 (AccessBLEvt AccessWrite ProtStrong tg range2) tr3 cids3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ??? cids2 TgEx ProtCall Rebor Write12 CallAct Write23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Tg'Ex Tg'Unique].
  created tg' protected as Protected.
  created tg' nonparent of tg as Unrelated.
  migrate TgEx.
  forget tr0.

  (* write step 1 *)
  destruct (child_write_any_to_init_active
    Tg'Ex Tg'Unique ltac:(left; reflexivity)
    RContains1 eq_refl
    Write12
  ) as [post [zpost [Post'Unique [PostPerm [PostActive [PostProt PostInit]]]]]].
  migrate Unrelated.
  migrate TgEx.
  migrate Tg'Ex.
  migrate Protected.
  forget tr1.

  subst.
  destruct (protected_nonchild_write_initialized_to_ub
    Tg'Ex Post'Unique Unrelated
    ltac:(eexists; split; [exact Protected|exact CallAct])
    PostInit
    RContains2 eq_refl
    ltac:(rewrite PostActive; eauto)
    Write23).
Qed.

Lemma protected_cread_fwrite_disjoint tg tg' cid newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cids0 cids1 cids2 cids3,
  tree_contains tg tr0 ->
  protector_is_for_call (new_protector newp) cid ->
  bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr1 cids1 ->
  bor_local_step tr1 cids1 (AccessBLEvt AccessRead ProtStrong tg' range1) tr2 cids2 ->
  call_is_active cids2 cid ->
  bor_local_step tr2 cids2 (AccessBLEvt AccessWrite ProtStrong tg range2) tr3 cids3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ???? TgEx ProtCall Rebor Read12 CallAct Write23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Tg'Ex Tg'Unique].
  created tg' protected as Protected.
  created tg' nonparent of tg as Unrelated.
  migrate TgEx.
  forget tr0.

  (* write step 1 *)
  destruct (child_read_any_to_init_nondis
    Tg'Ex Tg'Unique ltac:(left; reflexivity)
    RContains1 eq_refl Read12
  ) as [post [zpost [Post'Unique [PostPerm [PostNonDis [PostProt PostInit]]]]]].
  migrate Unrelated.
  migrate TgEx.
  migrate Tg'Ex.
  migrate Protected.
  forget tr1.

  subst.
  destruct (protected_nonchild_write_initialized_to_ub
    Tg'Ex Post'Unique Unrelated
    ltac:(eexists; split; [exact Protected|exact CallAct])
    PostInit RContains2 eq_refl PostNonDis Write23).
Qed.

Lemma protected_cwrite_fread_disjoint tg tg' cid newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cids0 cids1 cids2 cids3,
  tree_contains tg tr0 ->
  protector_is_for_call (new_protector newp) cid ->
  bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr1 cids1 ->
  bor_local_step tr1 cids1 (AccessBLEvt AccessWrite ProtStrong tg' range1) tr2 cids2 ->
  call_is_active cids2 cid ->
  bor_local_step tr2 cids2 (AccessBLEvt AccessRead ProtStrong tg range2) tr3 cids3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ???? TgEx ProtCall Rebor Write12 CallAct Read23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Tg'Ex Tg'Unique].
  created tg' protected as Protected.
  created tg' nonparent of tg as Unrelated.
  migrate TgEx.
  forget tr0.

  (* write step 1 *)
  destruct (child_write_any_to_init_active
    Tg'Ex Tg'Unique ltac:(left; reflexivity)
    RContains1 eq_refl Write12) as [post [zpost [Post'Unique [PostPerm [PostNonDis [PostProt PostInit]]]]]].
  migrate Unrelated.
  migrate TgEx.
  migrate Tg'Ex.
  migrate Protected.
  forget tr1.

  subst.
  destruct (protected_nonchild_read_initialized_active_to_ub
    Tg'Ex Post'Unique Unrelated
    ltac:(eexists; split; [exact Protected|exact CallAct])
    PostInit RContains2 eq_refl PostNonDis Read23).
Qed.

Lemma protected_fread_cwrite_disjoint tg tg' cid newp range1 range2 :
  forall tgp tr0 tr1 tr2 tr3 cids0 cids1 cids2 cids3,
  tree_contains tg tr0 ->
  protector_is_for_call (new_protector newp) cid ->
  bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr1 cids1 ->
  call_is_active cids1 cid ->
  bor_local_step tr1 cids1 (AccessBLEvt AccessRead ProtStrong tg range1) tr2 cids2 ->
  bor_local_step tr2 cids2 (AccessBLEvt AccessWrite ProtStrong tg' range2) tr3 cids3 ->
  ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> ? tr0 tr1 tr2 tr3 ???? TgEx ProtCall Rebor CallAct Read12 Write23 [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Tg'Ex Tg'Unique].
  created tg' protected as Protected.
  created tg' nonparent of tg as Unrelated.
  migrate TgEx.
  forget tr0.

  (* write step 1 *)
  destruct (protected_nonchild_read_any_to_frozen
    Tg'Ex Tg'Unique
    Unrelated
    ltac:(eexists; split; [exact Protected|exact CallAct])
    RContains1 eq_refl Read12
  ) as [post [zpost [Unique'Post [PermPost FrzPost]]]].
  migrate Tg'Ex.
  forget tr1.

  (* read step 2 *)
  destruct (child_write_frozen_to_ub
    Tg'Ex Unique'Post
    ltac:(left; reflexivity)
    RContains2 PermPost
    ltac:(solve_reachability)
    Write23).
Qed.


