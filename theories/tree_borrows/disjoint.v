From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Import lang_base notation bor_semantics tree tree_lemmas bor_lemmas steps_preserve.
From iris.prelude Require Import options.

(* Key lemma: converts the entire traversal to a per-node level.
   This is applicable to every permission in the accessed range, all that's needed
   to complement it should be preservation of permissions outside of said range. *)
Lemma access_effect_per_loc_within_range
  {tr affected_tag access_tag pre kind cids cids' range tr' z zpre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt kind access_tag range) tr' cids')
  : exists post zpost, (
    let rel := if naive_rel_dec tr affected_tag access_tag then AccessChild else AccessForeign in
    let isprot := bool_decide (protector_is_active pre.(iprot) cids) in
    apply_access_perm kind rel isprot true zpre = Some zpost
    /\ tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ iprot post = iprot pre
  ).
Proof.
  inversion Step; subst.
  (* use apply_access_spec_per_node to get info on the post permission *)
  destruct (apply_access_spec_per_node
    EXISTS_TAG Ex Unq
    (item_apply_access_preserves_tag _ _) ACC) as [post [SpecPost [ContainsPost UniquePost]]].
  (* and then it's per-tag work *)
  rewrite (tree_unique_specifies_tag _ _ _ Ex Unq) in SpecPost.
  option step in SpecPost as ?:tmpSpec.
  injection SpecPost; intro H; subst; clear SpecPost.
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

Lemma access_effect_per_loc_outside_range
  {tr affected_tag access_tag pre kind cids cids' range tr' z zpre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Outside : ~range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt kind access_tag range) tr' cids')
  : exists post, (
    tree_unique affected_tag post tr
    /\ item_lazy_perm_at_loc post z = zpre
    /\ iprot post = iprot pre
  ).
Proof.
  inversion Step; subst.
  destruct (apply_access_spec_per_node
    EXISTS_TAG Ex Unq
    (item_apply_access_preserves_tag _ _)
    ACC) as [post [SpecPost [ContainsPost UniquePost]]].
  (* We now show that
     (1) post has zpre at loc z
     (2) post is equal to whatever item the goal refers to *)
  assert (item_lazy_perm_at_loc post z = item_lazy_perm_at_loc pre z) as SamePerm. {
    option step in SpecPost as ?:SpecPerms.
    injection SpecPost; intros; subst; clear SpecPost.
    pose proof (range_foreach_spec _ _ z _ _ SpecPerms) as RangeForeach.
    rewrite (decide_False _ _ Outside) in RangeForeach.
    unfold item_lazy_perm_at_loc; simpl.
    rewrite RangeForeach; reflexivity.
  }
  eexists.
  split; [|split]; [exact Unq|reflexivity|reflexivity].
Qed.

(* Strategy for lemmas of the form

Lemma _
  (Ex : tree_contains ?aff ?tr)
  (Unq : tree_unique ?aff ?pre ?tr)
  (Within : range_contains ?range ?z)

  optional: (Nonchild : ~ParentChildIn ?aff ?acc ?tr)
  optional: (Child : ParentChildIn ?aff ?acc ?tr)
  optional: restrictions on (perm ?pre), e.g. reachability
  optional: protector_is_active (iprot ?pre) ?cids

  (Step : bor_local_step ?tr ?cids (AccessBLEvt _ ?acc ?range) ?tr' _)
  : _.

Where the conclusion can be either
* there is UB:
  : False.
* there is some item in the new tree that is related to ?pre:
  : exists post zpost, (
    tree_unique ?aff post ?tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ iprot post = iprot pre
    /\ ...
      optional: restrictions on reachability of (perm zpost),
      e.g. reach (perm ?pre) ?(perm zpost)
  ).

These lemmas can be solved by a case analysis on ?pre, which the following tactic performs *)
Ltac auto_access_event_within_range :=
  match goal with
  (* First off, if we see an access step, we apply the key per-location lemma *)
  | Ex : tree_contains ?aff ?tr,
    Unq : tree_unique ?aff ?pre ?tr,
    Within : range_contains ?range ?z,
    Step : bor_local_step ?tr _ (AccessBLEvt _ _ ?range) _ _
    |- exists _ _, _ =>
    destruct (access_effect_per_loc_within_range Ex Unq Within eq_refl Step) as [post[zpost[?[?[??]]]]];
    exists post, zpost;
    clear Step Unq Within Ex
  | Ex : tree_contains ?aff ?tr,
    Unq : tree_unique ?aff ?pre ?tr,
    Within : range_contains ?range ?z,
    Step : bor_local_step ?tr _ (AccessBLEvt _ _ ?range) _ _
    |- _ =>
    destruct (access_effect_per_loc_within_range Ex Unq Within eq_refl Step) as [post[zpost[?[?[??]]]]];
    clear Step Unq Within Ex
  (* if we need to solve a naive_rel_dec, we look for a known one *)
  | H : context[naive_rel_dec ?tr ?aff ?acc],
    Rel : ParentChildIn ?aff ?acc ?tr
    |- _ => destruct (naive_rel_dec _ _ _); [|contradiction]; clear Rel
  | H : context[naive_rel_dec ?tr ?aff ?acc],
    Rel : ~ParentChildIn ?aff ?acc ?tr
    |- _ => destruct (naive_rel_dec _ _ _); [contradiction|]; clear Rel
  (* we might need to decide protectors *)
  | H : context[bool_decide (protector_is_active ?p ?cids)],
    P : protector_is_active ?p ?cids
    |- _ => rewrite (bool_decide_eq_true_2 _ P) in H
  | H : context[bool_decide (protector_is_active ?p ?cids)]
    |- _ => destruct (bool_decide (protector_is_active _ _))
  (* we'd always rather work on permissions directly than item_lazy_perm_at_loc *)
  | E : item_lazy_perm_at_loc ?x ?z = _,
    H : context[item_lazy_perm_at_loc ?x ?z]
    |- _ => rewrite E in H
  (* and then big case analysis *)
  | x : lazy_permission |- _ => destruct x; simpl in *
  | p : permission |- _ => destruct p; simpl in *
  | i : perm_init |- _ => destruct i; simpl in *
  | H : apply_access_perm _ _ _ _ _ = Some _ |- _ => try (inversion H; done); clear H
  (* when all the rest is done, you can split and auto *)
  | |- _ => subst; try repeat split; eauto
  end
  .

Lemma nonchild_write_reserved_to_disabled
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Reach : reach Reserved (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessWrite access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ reach Disabled (perm zpost)
    /\ iprot post = iprot pre
  ).
Proof. do 11 auto_access_event_within_range. Qed.

Lemma nonchild_write_any_protected_to_disabled
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Protected : protector_is_active (iprot pre) cids)
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt AccessWrite access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ reach Disabled (perm zpost)
    /\ iprot post = iprot pre
  ).
Proof. do 11 auto_access_event_within_range. Qed.

Lemma nonchild_read_active_to_frozen
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Reach : reach Active (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ reach Frozen (perm zpost)
    /\ reach (perm zpre) (perm zpost)
  ).
Proof. do 11 auto_access_event_within_range. Qed.

Lemma child_write_frozen_to_ub
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Child : ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Reach : reach Frozen (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessWrite access_tag range) tr' cids')
  : False.
Proof. do 11 auto_access_event_within_range. Qed.

Lemma child_read_disabled_to_ub
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Child : ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Reach : reach Disabled (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead access_tag range) tr' cids')
  : False.
Proof. do 11 auto_access_event_within_range. Qed.

Lemma child_write_any_to_init_active
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Child : ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt AccessWrite access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ perm zpost = Active
    /\ iprot post = iprot pre
    /\ initialized zpost = PermInit
  ).
Proof. do 11 auto_access_event_within_range. Qed.

Lemma child_read_any_to_init_nondis
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Child : ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ ~reach Disabled (perm zpost)
    /\ iprot post = iprot pre
    /\ initialized zpost = PermInit
  ).
Proof. do 15 auto_access_event_within_range. Qed.


Lemma protected_nonchild_write_initialized_to_ub
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Protected : protector_is_active (iprot pre) cids)
  (Initialized : initialized (item_lazy_perm_at_loc pre z) = PermInit)
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (NonDis : ~reach Disabled (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessWrite access_tag range) tr' cids')
  : False.
Proof. do 15 auto_access_event_within_range. Qed.

Lemma protected_nonchild_read_initialized_active_to_ub
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Protected : protector_is_active (iprot pre) cids)
  (Initialized : initialized (item_lazy_perm_at_loc pre z) = PermInit)
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Activated : perm zpre = Active)
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead access_tag range) tr' cids')
  : False.
Proof. do 15 auto_access_event_within_range. Qed.

Lemma protected_nonchild_read_any_to_frozen
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Protected : protector_is_active (iprot pre) cids)
  (Within : range_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ item_lazy_perm_at_loc post z = zpost
    /\ reach Frozen (perm zpost)
  ).
Proof. do 15 auto_access_event_within_range. Qed.

(* `migrate` facilitates moving hypotheses across borrow steps.
   Usage:
     migrate P.
     migrate P as Q.
   Moves common preserved hypotheses across borrow steps.
   E.g.: tree_contains is a property that is preserved by borrow steps:
         `forall tg, tree_contains tg ?tr -> bor_step ?tr _ _ ?tr' _ -> tree_contains tg ?tr'`.
         If you have a `H : tree_contains tg ?tr`, you can move it across the `bor_step`
         using `migrate H`.

   Handles hypotheses :
   - tree_contains
   - ParentChildIn
   - protector_is_for_call
   - tree_unique

   through steps:
   - bor_step
   - bor_seq
*)
Ltac migrate prop dest :=
  lazymatch type of prop with
  (* Migrate a tree_contains *)
  | tree_contains ?tg ?tr =>
    lazymatch goal with
    | Step: bor_local_step tr _ _ _ _ |- _ =>
      pose proof (bor_local_step_preserves_contains prop Step) as dest
    | Seq : bor_local_seq _ _  tr _ _ _ _ |- _ =>
      pose proof (bor_local_seq_last_contains prop (bor_local_seq_forget Seq)) as dest
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
    | Seq : bor_local_seq _ _  tr _ _ _ _,
      Ex : tree_contains tg tr,
      Ex' : tree_contains tg' tr
      |- _ =>
      pose proof prop as dest;
      rewrite (bor_local_seq_last_eqv_rel Ex Ex' (bor_local_seq_forget Seq)) in dest
    end
  (* Migrate info on a protector *)
  | context [protector_is_for_call _ ?old] =>
    lazymatch goal with
    | ACC: old = ?new |- _ =>
      pose proof prop as dest;
      rewrite ACC in dest
    | ACC: ?new = old |- _ =>
      pose proof prop as dest;
      rewrite <- ACC in prop
    end
  (* Migrate a tree_unique (lossy) *)
  | tree_unique ?tg _ ?tr =>
    lazymatch goal with
    | Seq : bor_local_seq _ _  tr _ _ _ _,
      Ex : tree_contains tg tr
      |- _ =>
      pose proof (bor_local_seq_last_unique Ex prop (bor_local_seq_forget Seq)) as dest
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

(* `forget` makes a name fresh again
   Usage:
     forget x.
*)
Ltac forget x :=
  repeat match goal with
  | H: context [x] |- _ => clear H
  end;
  clear x.

(* `created_unique`, `created_protected`, and `created_nonparent` know the properties of items produced by `create_new_item`
   Usage:
      created tg unique as [tgExists tgUnique].
      created tg protected as tgProtected.
      created tg nonparent of tg' as Unrelated.
   If you have sufficient hypotheses, these will produce proofs for
   - tree_contains tg ?tr
   - tree_unique tg (create_new_item tg _) ?tr
   - protector_is_for_call (iprot (create_new_item tg _)) _
   - ~ParentChildIn tg tg' ?tr
   respectively.
*)
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
  | H : protector_is_for_call ?cid (new_protector ?newp),
    _ : context [create_new_item tg ?newp]
    |- _ =>
    assert (protector_is_for_call cid (iprot (create_new_item tg newp))) as dest by (simpl; exact H)
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

(* Incomplete heuristics to derive `reach _ _` *)
Ltac solve_reachability :=
  let p := fresh "perm" in
  multimatch goal with
  | |- reach _ _ => assumption
  | |- reach _ _ => eapply reach_reflexive; done
  | |- reach _ (perm (item_lazy_perm_at_loc (create_new_item _ _) _)) => eapply create_new_item_perm_prop
  (* transitivity hints  *)
  | |- reach Frozen ?p => apply (reach_transitive Frozen Disabled p); [done|]
  end.

(* `specialize` on steroids.
   `pose replace` is a generalization of `specialize`:
    `pose replace H with @ x` is mostly equivalent to `specialize H with x`.

   What it offers in addition is
   - specialization of Prop arguments
   - arbitrary order of arguments (if the one you need is not there, add it below as a Tactic Notation)

   `pose replace H with P Q @ R`
   will replace the hypothesis `H` with `(P Q H R)`
*)
Ltac squash new old := try clear old; rename new into old.
Ltac xspecialize name term :=
  let tmp := fresh "tmp" in
  pose proof term as tmp;
  squash tmp name.
Tactic Notation "pose" "replace" constr(target) "with" uconstr(a) uconstr(b) := xspecialize target (a b).
Tactic Notation "pose" "replace" constr(target) "with" "@" uconstr(b) := xspecialize target (target b).
Tactic Notation "pose" "replace" constr(target) "with" "@" uconstr(b) uconstr(c) := xspecialize target (target b c).
Tactic Notation "pose" "replace" constr(target) "with" uconstr(a) uconstr(b) uconstr(c) uconstr(d) "@" := xspecialize target (a b c d target).
Tactic Notation "pose" "replace" constr(target) "with" uconstr(a) uconstr(b) uconstr(c) "@" uconstr(d) := xspecialize target (a b c target d).
Tactic Notation "pose" "replace" constr(target) "with" uconstr(a) uconstr(b) uconstr(c) uconstr(d) "@" uconstr(f) := xspecialize target (a b c d target f).
Tactic Notation "pose" "replace" constr(target) "with" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) "@" uconstr(g) := xspecialize target (a b c d e target g).

Lemma fwrite_cwrite_disjoint
  {tg tg' newp range1 range2 tgp tr0 tr0' tr1 tr1' tr2 tr2' cid cids0 cids0' cids1 cids1' cids2 cids2'}
  (Ex : tree_contains tg tr0)
  (ResReach : reach Reserved (initial_state newp))
  (Retag0 : bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr0' cids0')
  (Seq01 : exists l, bor_local_seq ignore ignore tr0' cids0' l tr1 cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq ignore ignore tr1' cids1' l tr2 cids2)
  (Write2 : bor_local_step tr2 cids2 (AccessBLEvt AccessWrite tg' range2) tr2' cids2')
  : ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  intros [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Ex' Unq'].
  created tg' nonparent of tg as Unrelated.
  migrate Ex.
  forget tr0.

  (* opaque seq *)
  destruct Seq01 as [evts01 Seq01].
  assert (reach Reserved (perm (item_lazy_perm_at_loc (create_new_item tg' newp) z))) as ResReach1 by solve_reachability.
  migrate Unrelated.
  pose replace ResReach1 with bor_local_seq_last_backward_reach Ex' Unq' @ Seq01.
  migrate Unq'; destruct Unq' as [post [Unq' _]].
  pose replace ResReach1 with @ post Unq'.
  migrate Ex'.
  forget tr0'.

  (* write step 1 *)
  rename post into pre.
  destruct (nonchild_write_reserved_to_disabled Ex' Unq' Unrelated RContains1 eq_refl ltac:(solve_reachability) Write1)
    as [post [zpost [Unq'Post [PermPost [DisPost ProtPost]]]]].
  migrate Ex'.
  forget tr1.
  forget pre.

  (* opaque seq *)
  subst.
  rename Unq'Post into Unq'.
  rename post into pre.
  destruct Seq12 as [evts12 Seq12].
  pose replace DisPost with bor_local_seq_last_backward_reach Ex' Unq' @ Seq12.
  migrate Unq'; destruct Unq' as [post [Unq' _]].
  pose replace DisPost with @ post Unq'.
  migrate Ex'.

  (* write step 2 *)
  destruct (child_write_frozen_to_ub Ex' Unq' ltac:(left; done) RContains2 eq_refl ltac:(repeat solve_reachability) Write2).
Qed.

Lemma fwrite_cread_disjoint
  {tg tg' newp range1 range2 tgp tr0 tr0' tr1 tr1' tr2 tr2' cid cids0 cids0' cids1 cids1' cids2 cids2'}
  (Ex : tree_contains tg tr0)
  (ResReach : reach Reserved (initial_state newp))
  (Retag0 : bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr0' cids0')
  (Seq01 : exists l, bor_local_seq ignore ignore tr0' cids0' l tr1 cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq ignore ignore tr1' cids1' l tr2 cids2)
  (Read2 : bor_local_step tr2 cids2 (AccessBLEvt AccessRead tg' range2) tr2' cids2')
  : ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Ex' Unq'].
  created tg' nonparent of tg as Unrelated.
  migrate Ex.
  forget tr0.

  (* opaque seq *)
  destruct Seq01 as [evts01 Seq01].
  assert (reach Reserved (perm (item_lazy_perm_at_loc (create_new_item tg' newp) z))) as ResReach1 by solve_reachability.
  migrate Unrelated.
  pose replace ResReach1 with bor_local_seq_last_backward_reach Ex' Unq' @ Seq01.
  migrate Unq'; destruct Unq' as [post [Unq' _]].
  pose replace ResReach1 with @ post Unq'.
  migrate Ex'.
  forget tr0'.

  (* write step 1 *)
  rename post into pre.
  destruct (nonchild_write_reserved_to_disabled
    Ex' Unq'
    Unrelated
    RContains1 eq_refl
    ltac:(solve_reachability)
    Write1
  ) as [post [zpost [Unq'Post [PermPost [DisPost ProtPost]]]]].
  migrate Ex'.
  forget tr1.
  forget pre.

  (* opaque seq *)
  subst.
  rename Unq'Post into Unq'.
  rename post into pre.
  destruct Seq12 as [evts12 Seq12].
  pose replace DisPost with bor_local_seq_last_backward_reach Ex' Unq' @ Seq12.
  migrate Unq'; destruct Unq' as [post [Unq' _]].
  pose replace DisPost with @ post Unq'.
  migrate Ex'.

  (* read step 2 *)
  destruct (child_read_disabled_to_ub
    Ex' Unq'
    ltac:(left; reflexivity)
    RContains2 eq_refl
    ltac:(solve_reachability)
    Read2).
Qed.

Lemma protected_fwrite_cwrite_disjoint
  {tg tg' newp range1 range2 tgp tr0 tr0' tr1 tr1' tr2 tr2' cid cids0 cids0' cids1 cids1' cids2 cids2'}
  (Ex : tree_contains tg tr0)
  (Prot : protector_is_for_call cid (new_protector newp))
  (Retag0 : bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr0' cids0')
  (Seq01 : exists l, bor_local_seq ignore ignore tr0' cids0' l tr1 cids1)
  (Call : call_is_active cid cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq ignore ignore tr1' cids1' l tr2 cids2)
  (Write2 : bor_local_step tr2 cids2 (AccessBLEvt AccessWrite tg' range2) tr2' cids2')
  : ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  intros [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Ex' Unq'].
  created tg' nonparent of tg as Unrelated.
  migrate Ex.
  forget tr0.

  (* opaque seq *)
  destruct Seq01 as [evts01 Seq01].
  migrate Unrelated.
  migrate Unq'; destruct Unq' as [post [Unq' Prot']].
  migrate Ex'.
  forget tr0'.

  (* write step 1 *)
  rename post into pre.
  assert (protector_is_active (iprot pre) cids1) as Protected by (eexists; split; [rewrite <- Prot'; simpl|]; eassumption).
  destruct (nonchild_write_any_protected_to_disabled Ex' Unq' Unrelated Protected RContains1 eq_refl Write1)
    as [post [zpost [Unq'Post [PermPost [DisPost ProtPost]]]]].
  migrate Ex'.
  forget tr1.
  forget pre.

  (* opaque seq *)
  subst.
  rename Unq'Post into Unq'.
  rename post into pre.
  destruct Seq12 as [evts12 Seq12].
  pose replace DisPost with bor_local_seq_last_backward_reach Ex' Unq' @ Seq12.
  migrate Unq'; destruct Unq' as [post [Unq' _]].
  pose replace DisPost with @ post Unq'.
  migrate Ex'.

  (* write step 2 *)
  destruct (child_write_frozen_to_ub Ex' Unq' ltac:(left; done) RContains2 eq_refl ltac:(repeat solve_reachability) Write2).
Qed.

Lemma protected_fwrite_cread_disjoint
  {tg tg' newp range1 range2 tgp tr0 tr0' tr1 tr1' tr2 tr2' cid cids0 cids0' cids1 cids1' cids2 cids2'}
  (Ex : tree_contains tg tr0)
  (Prot : protector_is_for_call cid (new_protector newp))
  (Retag0 : bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr0' cids0')
  (Seq01 : exists l, bor_local_seq ignore ignore tr0' cids0' l tr1 cids1)
  (Call : call_is_active cid cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq ignore ignore tr1' cids1' l tr2 cids2)
  (Read2 : bor_local_step tr2 cids2 (AccessBLEvt AccessRead tg' range2) tr2' cids2')
  : ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Ex' Unq'].
  created tg' nonparent of tg as Unrelated.
  migrate Ex.
  forget tr0.

  (* opaque seq *)
  destruct Seq01 as [evts01 Seq01].
  migrate Unrelated.
  migrate Unq'; destruct Unq' as [post [Unq' Prot']].
  migrate Ex'.
  forget tr0'.

  (* write step 1 *)
  rename post into pre.
  assert (protector_is_active (iprot pre) cids1) as Protected by (eexists; split; [rewrite <- Prot'; simpl|]; eassumption).
  destruct (nonchild_write_any_protected_to_disabled
    Ex' Unq'
    Unrelated
    Protected RContains1
    eq_refl
    Write1
  ) as [post [zpost [Unq'Post [PermPost [DisPost ProtPost]]]]].
  migrate Ex'.
  forget tr1.
  forget pre.

  (* opaque seq *)
  subst.
  rename Unq'Post into Unq'.
  rename post into pre.
  destruct Seq12 as [evts12 Seq12].
  pose replace DisPost with bor_local_seq_last_backward_reach Ex' Unq' @ Seq12.
  migrate Unq'; destruct Unq' as [post [Unq' _]].
  pose replace DisPost with @ post Unq'.
  migrate Ex'.

  (* read step 2 *)
  destruct (child_read_disabled_to_ub
    Ex' Unq'
    ltac:(left; reflexivity)
    RContains2 eq_refl
    ltac:(solve_reachability)
    Read2).
Qed.


Lemma activated_fread_cwrite_disjoint
  {tg tg' newp range1 range2 range3 tgp tr0 tr0' tr1 tr1' tr2 tr2' tr3 tr3' cid cids0 cids0' cids1 cids1' cids2 cids2' cids3 cids3'}
  (Ex : tree_contains tg tr0)
  (Retag0 : bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr0' cids0')
  (Seq01 : exists l, bor_local_seq ignore ignore tr0' cids0' l tr1 cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg' range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq ignore ignore tr1' cids1' l tr2 cids2)
  (Read2 : bor_local_step tr2 cids2 (AccessBLEvt AccessRead tg range2) tr2' cids2')
  (Seq23 : exists l, bor_local_seq ignore ignore tr2' cids2' l tr3 cids3)
  (Write3 : bor_local_step tr3 cids3 (AccessBLEvt AccessWrite tg' range3) tr3' cids3')
  : ~exists z, range_contains range1 z /\ range_contains range2 z /\ range_contains range3 z.
Proof.
  move=> [z [RContains1 [RContains2 RContains3]]].
  (* reborrow step *)
  created tg' unique as [Ex' Unq'].
  created tg' nonparent of tg as Unrelated.
  migrate Ex.
  forget tr0.

 (* opaque seq *)
  destruct Seq01 as [evts01 Seq01].
  migrate Unrelated.
  migrate Unq'; destruct Unq' as [post [Unq' _]].
  migrate Ex'.
  migrate Ex.
  forget tr0'.

  (* write step 1 *)
  rename post into pre.
  destruct (child_write_any_to_init_active
    Ex' Unq'
    ltac:(left; reflexivity)
    RContains1 eq_refl
    Write1
  ) as [post [zpost [Unq'Post [PermPost [ActPost _]]]]].
  migrate Unrelated.
  migrate Ex'.
  migrate Ex.
  forget tr1.
  forget pre.
  assert (reach Active (perm zpost)) as ActReachPost by solve_reachability.

  (* opaque seq *)
  subst.
  rename Unq'Post into Unq'.
  rename post into pre.
  destruct Seq12 as [evts12 Seq12].
  migrate Unrelated.
  pose replace ActReachPost with bor_local_seq_last_backward_reach Ex' Unq' @ Seq12.
  migrate Unq'; destruct Unq' as [post [Unq' _]].
  pose replace ActReachPost with @ post Unq'.
  migrate Ex'.
  forget pre.

  (* read step 2 *)
  rename post into pre.
  rename ActReachPost into ActReachPre.
  destruct (nonchild_read_active_to_frozen
    Ex' Unq'
    Unrelated
    RContains2 eq_refl
    ltac:(solve_reachability)
    Read2) as [post [zpost [Unq'Post [PermPost [FrzReachPost PreReachPost]]]]].
  migrate Ex'.
  forget tr2.
  forget pre.

  (* opaque seq *)
  subst.
  rename Unq'Post into Unq'.
  rename post into pre.
  destruct Seq23 as [evts23 Seq23].
  pose replace FrzReachPost with bor_local_seq_last_backward_reach Ex' Unq' @ Seq23.
  migrate Unq'; destruct Unq' as [post [Unq' _]].
  pose replace FrzReachPost with @ post Unq'.
  migrate Ex'.

  (* write step 3 *)
  destruct (child_write_frozen_to_ub
    Ex' Unq'
    ltac:(left; reflexivity)
    RContains3 eq_refl
    ltac:(solve_reachability)
    Write3).
Qed.

Lemma protected_cwrite_fwrite_disjoint
  {tg tg' cid newp range1 range2 tgp tr0 tr0' tr1 tr1' tr2 tr2' cids0 cids0' cids1 cids1' cids2 cids2'}
  (Ex : tree_contains tg tr0)
  (Prot : protector_is_for_call cid (new_protector newp))
  (Retag0 : bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr0' cids0')
  (Seq01 : exists l, bor_local_seq ignore ignore tr0' cids0' l tr1 cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg' range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq
    (fun tr => forall it z,
      tree_unique tg' it tr ->
      range_contains range1 z ->
      initialized (item_lazy_perm_at_loc it z) = PermInit)
    (call_is_active cid)
    tr1' cids1' l tr2 cids2)
  (Write2 : bor_local_step tr2 cids2 (AccessBLEvt AccessWrite tg range2) tr2' cids2')
  : ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Ex' Unq'].
  created tg' protected as Protected.
  created tg' nonparent of tg as Unrelated.
  migrate Ex.
  forget tr0.

 (* opaque seq *)
  destruct Seq01 as [evts01 Seq01].
  migrate Unrelated.
  migrate Unq'; destruct Unq' as [post [Unq' Prot']].
  migrate Ex'.
  migrate Ex.
  forget tr0'.

  (* write step 1 *)
  subst.
  rename post into pre.
  destruct (child_write_any_to_init_active
    Ex' Unq' ltac:(left; reflexivity)
    RContains1 eq_refl
    Write1
  ) as [post [zpost [Unq'Post [PermPost [ActPost [ProtPost InitPost]]]]]].
  migrate Unrelated.
  migrate Ex.
  migrate Ex'.
  migrate Protected.
  rewrite <- ProtPost in Protected.
  forget tr1.
  forget pre.

  (* opaque seq *)
  subst.
  rename Unq'Post into Unq'.
  rename post into pre.
  destruct Seq12 as [evts12 Seq12].
  migrate Unrelated.
  assert (bor_local_seq
    (fun tr => forall it,
      tree_unique tg' it tr ->
      initialized (item_lazy_perm_at_loc it z) = PermInit)
    (call_is_active cid)
    tr1' cids1' evts12 tr2 cids2) as GenActPost. {
    eapply seq_always_build_weaken; [|done|exact Seq12].
    simpl. move=> ? H ??. apply H; auto.
  }
  pose replace ActPost with protected_during_seq_last_stays_active Ex' Unq' eq_refl Protected @ GenActPost.
  migrate Unq'; destruct Unq' as [post [Unq' ProtPost]].
  pose replace ActPost with @ post Unq'.
  migrate Ex'.
  migrate Protected.
  forget pre.

  (* write step 2 *)
  subst.
  pose proof (seq_always_destruct_last GenActPost) as [Init Call].
  destruct (protected_nonchild_write_initialized_to_ub
    Ex' Unq' Unrelated
    ltac:(eexists; split; [exact Protected|exact Call])
    (Init _ Unq')
    RContains2 eq_refl
    ltac:(rewrite ActPost; eauto)
    Write2).
Qed.

Lemma protected_cread_fwrite_disjoint
  {tg tg' cid newp range1 range2 tgp tr0 tr0' tr1 tr1' tr2 tr2' cids0 cids0' cids1 cids1' cids2 cids2'}
  (Ex : tree_contains tg tr0)
  (Prot : protector_is_for_call cid (new_protector newp))
  (Retag0 : bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr0' cids0')
  (Seq01 : exists l, bor_local_seq ignore ignore tr0' cids0' l tr1 cids1)
  (Read1 : bor_local_step tr1 cids1 (AccessBLEvt AccessRead tg' range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq
    (fun tr => forall it z,
      tree_unique tg' it tr ->
      range_contains range1 z ->
      initialized (item_lazy_perm_at_loc it z) = PermInit)
    (call_is_active cid)
    tr1' cids1' l tr2 cids2)
  (Write2 : bor_local_step tr2 cids2 (AccessBLEvt AccessWrite tg range2) tr2' cids2')
  : ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Ex' Unq'].
  created tg' protected as Protected.
  created tg' nonparent of tg as Unrelated.
  migrate Ex.
  forget tr0.

 (* opaque seq *)
  destruct Seq01 as [evts01 Seq01].
  migrate Unrelated.
  migrate Unq'; destruct Unq' as [post [Unq' Prot']].
  migrate Ex'.
  migrate Ex.
  forget tr0'.

  (* write step 1 *)
  subst.
  rename post into pre.
  destruct (child_read_any_to_init_nondis
    Ex' Unq' ltac:(left; reflexivity)
    RContains1 eq_refl Read1
  ) as [post [zpost [Unq'Post [PermPost [DisUnreachPost [ProtPost InitPost]]]]]].
  migrate Unrelated.
  migrate Ex.
  migrate Ex'.
  migrate Protected.
  rewrite <- ProtPost in Protected.
  forget tr1.
  forget pre.

  (* opaque seq *)
  subst.
  rename Unq'Post into Unq'.
  rename post into pre.
  destruct Seq12 as [evts12 Seq12].
  migrate Unrelated.
  assert (bor_local_seq
    (fun tr => forall it,
      tree_unique tg' it tr ->
      initialized (item_lazy_perm_at_loc it z) = PermInit)
    (call_is_active cid)
    tr1' cids1' evts12 tr2 cids2) as GenNonDisPost. {
    eapply seq_always_build_weaken; [|done|exact Seq12].
    simpl. move=> ? H ??. apply H; auto.
  }
  pose replace DisUnreachPost with protected_during_seq_last_stays_nondis Ex' Unq' eq_refl Protected @ GenNonDisPost.
  migrate Unq'; destruct Unq' as [post [Unq' ProtPost]].
  pose replace DisUnreachPost with @ post Unq'.
  migrate Ex'.
  migrate Protected.
  forget pre.

  subst.
  pose proof (seq_always_destruct_last GenNonDisPost) as [Init Call].
  destruct (protected_nonchild_write_initialized_to_ub
    Ex' Unq' Unrelated
    ltac:(eexists; split; [exact Protected|exact Call])
    (Init _ Unq') RContains2 eq_refl DisUnreachPost Write2).
Qed.

Lemma protected_cwrite_fread_disjoint
  {tg tg' cid newp range1 range2 tgp tr0 tr0' tr1 tr1' tr2 tr2' cids0 cids0' cids1 cids1' cids2 cids2'}
  (Ex : tree_contains tg tr0)
  (Prot : protector_is_for_call cid (new_protector newp))
  (Retag0 : bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr0' cids0')
  (Seq01 : exists l, bor_local_seq ignore ignore tr0' cids0' l tr1 cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg' range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq
    (fun tr => forall it z,
      tree_unique tg' it tr ->
      range_contains range1 z ->
      initialized (item_lazy_perm_at_loc it z) = PermInit)
    (call_is_active cid)
    tr1' cids1' l tr2 cids2)
  (Read2 : bor_local_step tr2 cids2 (AccessBLEvt AccessRead tg range2) tr2' cids2')
  : ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Ex' Unq'].
  created tg' protected as Protected.
  created tg' nonparent of tg as Unrelated.
  migrate Ex.
  forget tr0.

 (* opaque seq *)
  destruct Seq01 as [evts01 Seq01].
  migrate Unrelated.
  migrate Unq'; destruct Unq' as [post [Unq' Prot']].
  migrate Ex'.
  migrate Ex.
  forget tr0'.

  (* write step 1 *)
  subst.
  rename post into pre.
  destruct (child_write_any_to_init_active
    Ex' Unq' ltac:(left; reflexivity)
    RContains1 eq_refl Write1) as [post [zpost [Unq'Post [PermPost [ActPost [ProtPost PostInit]]]]]].
  migrate Unrelated.
  migrate Ex.
  migrate Ex'.
  migrate Protected.
  rewrite <- ProtPost in Protected.
  forget tr1.
  forget pre.

  (* opaque seq *)
  subst.
  rename Unq'Post into Unq'.
  rename post into pre.
  destruct Seq12 as [evts12 Seq12].
  migrate Unrelated.
  assert (bor_local_seq
    (fun tr => forall it,
      tree_unique tg' it tr ->
      initialized (item_lazy_perm_at_loc it z) = PermInit)
    (call_is_active cid)
    tr1' cids1' evts12 tr2 cids2) as GenActPost. {
    eapply seq_always_build_weaken; [|done|exact Seq12].
    simpl. move=> ? H ??. apply H; auto.
  }
  pose replace ActPost with protected_during_seq_last_stays_active Ex' Unq' eq_refl Protected @ GenActPost.
  migrate Unq'; destruct Unq' as [post [Unq' ProtPost]].
  pose replace ActPost with @ post Unq'.
  migrate Ex'.
  migrate Protected.
  forget pre.

  (* read step 2 *)
  subst.
  pose proof (seq_always_destruct_last GenActPost) as [Init Call].
  destruct (protected_nonchild_read_initialized_active_to_ub
    Ex' Unq' Unrelated
    ltac:(eexists; split; [exact Protected|exact Call])
    (Init _ Unq') RContains2 eq_refl ActPost Read2).
Qed.

Lemma protected_fread_cwrite_disjoint
  {tg tg' cid newp range1 range2 tgp tr0 tr0' tr1 tr1' tr2 tr2' cids0 cids0' cids1 cids1' cids2 cids2'}
  (Ex : tree_contains tg tr0)
  (Prot : protector_is_for_call cid (new_protector newp))
  (Retag0 : bor_local_step tr0 cids0 (RetagBLEvt tgp tg' newp cid) tr0' cids0')
  (Seq01 : exists l, bor_local_seq ignore ignore tr0' cids0' l tr1 cids1)
  (Call1 : call_is_active cid cids1)
  (Read1 : bor_local_step tr1 cids1 (AccessBLEvt AccessRead tg range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq ignore ignore tr1' cids0' l tr2 cids2)
  (Write2 : bor_local_step tr2 cids2 (AccessBLEvt AccessWrite tg' range2) tr2' cids2')
  : ~exists z, range_contains range1 z /\ range_contains range2 z.
Proof.
  move=> [z [RContains1 RContains2]].
  (* reborrow step *)
  created tg' unique as [Ex' Unq'].
  created tg' protected as Protected.
  created tg' nonparent of tg as Unrelated.
  migrate Ex.
  forget tr0.

 (* opaque seq *)
  destruct Seq01 as [evts01 Seq01].
  migrate Unrelated.
  migrate Unq'; destruct Unq' as [post [Unq' Prot']].
  migrate Protected.
  migrate Ex'.
  migrate Ex.
  forget tr0'.

  (* write step 1 *)
  subst.
  rename post into pre.
  destruct (protected_nonchild_read_any_to_frozen
    Ex' Unq'
    Unrelated
    ltac:(eexists; split; [exact Protected|exact Call1])
    RContains1 eq_refl Read1
  ) as [post [zpost [Unq'Post [PermPost FrzReachPost]]]].
  migrate Ex'.
  forget tr1.
  forget pre.

  (* opaque seq *)
  subst.
  rename Unq'Post into Unq'.
  rename post into pre.
  destruct Seq12 as [evts12 Seq12].
  pose replace FrzReachPost with bor_local_seq_last_backward_reach Ex' Unq' @ Seq12.
  migrate Unq'; destruct Unq' as [post [Unq' _]].
  pose replace FrzReachPost with @ post Unq'.
  migrate Ex'.

  (* read step 2 *)
  destruct (child_write_frozen_to_ub
    Ex' Unq'
    ltac:(left; reflexivity)
    RContains2 eq_refl
    ltac:(solve_reachability)
    Write2).
Qed.

(* reorder two arbitrary reads and reach the same borrow state *)
(* rename bor_local_seq: bor_local_steps *)
(* backwards reach is tricky: it prevents us from doing nontermination. don't rely on an EndCall later, assume no EndCall for the particular cid at every step *)
(* ghost state, ressource algebras, invariants *)
