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
  (Within : range'_contains range z)
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
  pose proof (range'_foreach_spec _ _ z _ _ tmpSpec) as ForeachSpec.
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
  (Outside : ~range'_contains range z)
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
    pose proof (range'_foreach_spec _ _ z _ _ SpecPerms) as RangeForeach.
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
    Within : range'_contains ?range ?z,
    Step : bor_local_step ?tr _ (AccessBLEvt _ _ ?range) _ _
    |- exists _ _, _ =>
    destruct (access_effect_per_loc_within_range Ex Unq Within eq_refl Step) as [post[zpost[?[?[??]]]]];
    exists post, zpost;
    clear Step Unq Within Ex
  | Ex : tree_contains ?aff ?tr,
    Unq : tree_unique ?aff ?pre ?tr,
    Within : range'_contains ?range ?z,
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
  (Within : range'_contains range z)
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
  (Within : range'_contains range z)
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
  (Within : range'_contains range z)
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
  (Within : range'_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Reach : reach Frozen (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessWrite access_tag range) tr' cids')
  : False.
Proof. do 11 auto_access_event_within_range. Qed.

Lemma child_write_protected_freeze_like_to_ub
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Child : ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range'_contains range z)
  (Protected : protector_is_active (iprot pre) cids)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (FrzLike : freeze_like (perm zpre))
  (Step : bor_local_step tr cids (AccessBLEvt AccessWrite access_tag range) tr' cids')
  : False.
Proof.
  unfold freeze_like in FrzLike.
  destruct FrzLike as [?|[?|?]].
  all: do 11 auto_access_event_within_range.
Qed.

Lemma child_read_disabled_to_ub
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Child : ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Within : range'_contains range z)
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
  (Within : range'_contains range z)
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
  (Within : range'_contains range z)
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
  (Within : range'_contains range z)
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
  (Within : range'_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Activated : perm zpre = Active)
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead access_tag range) tr' cids')
  : False.
Proof. do 15 auto_access_event_within_range. Qed.

(*
Definition freeze_like p : Prop :=
  reach Frozen p \/ p = ReservedConfl \/ p = ReservedConflMut.
*)

Lemma protected_nonchild_read_any_to_conflicted
  {tr affected_tag access_tag pre}
  (Ex : tree_contains affected_tag tr)
  (Unq : tree_unique affected_tag pre tr)
  (Nonchild : ~ParentChildIn affected_tag access_tag tr)
  {cids cids' range tr' z zpre}
  (Protected : protector_is_active (iprot pre) cids)
  (Within : range'_contains range z)
  (IsPre : item_lazy_perm_at_loc pre z = zpre)
  (Step : bor_local_step tr cids (AccessBLEvt AccessRead access_tag range) tr' cids')
  : exists post zpost, (
    tree_unique affected_tag post tr'
    /\ iprot post = iprot pre
    /\ item_lazy_perm_at_loc post z = zpost
    /\ freeze_like (perm zpost)
  ).
Proof. unfold freeze_like. do 15 auto_access_event_within_range. Qed.

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
    | Seq : bor_local_seq _ tr _ _ _ _ |- _ =>
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
    | Seq : bor_local_seq _  tr _ _ _ _,
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
    | Seq : bor_local_seq _  tr _ _ _ _,
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
  (Seq01 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr0' cids0' l tr1 cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr1' cids1' l tr2 cids2)
  (Write2 : bor_local_step tr2 cids2 (AccessBLEvt AccessWrite tg' range2) tr2' cids2')
  : ~exists z, range'_contains range1 z /\ range'_contains range2 z.
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
  (Seq01 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr0' cids0' l tr1 cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr1' cids1' l tr2 cids2)
  (Read2 : bor_local_step tr2 cids2 (AccessBLEvt AccessRead tg' range2) tr2' cids2')
  : ~exists z, range'_contains range1 z /\ range'_contains range2 z.
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
  (Seq01 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr0' cids0' l tr1 cids1)
  (Call : call_is_active cid cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr1' cids1' l tr2 cids2)
  (Write2 : bor_local_step tr2 cids2 (AccessBLEvt AccessWrite tg' range2) tr2' cids2')
  : ~exists z, range'_contains range1 z /\ range'_contains range2 z.
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
  (Seq01 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr0' cids0' l tr1 cids1)
  (Call : call_is_active cid cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr1' cids1' l tr2 cids2)
  (Read2 : bor_local_step tr2 cids2 (AccessBLEvt AccessRead tg' range2) tr2' cids2')
  : ~exists z, range'_contains range1 z /\ range'_contains range2 z.
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
  (Seq01 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr0' cids0' l tr1 cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg' range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr1' cids1' l tr2 cids2)
  (Read2 : bor_local_step tr2 cids2 (AccessBLEvt AccessRead tg range2) tr2' cids2')
  (Seq23 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr2' cids2' l tr3 cids3)
  (Write3 : bor_local_step tr3 cids3 (AccessBLEvt AccessWrite tg' range3) tr3' cids3')
  : ~exists z, range'_contains range1 z /\ range'_contains range2 z /\ range'_contains range3 z.
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
  (Seq01 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr0' cids0' l tr1 cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg' range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq {|seq_inv:=fun _ cids => call_is_active cid cids|} tr1' cids1' l tr2 cids2)
  (Write2 : bor_local_step tr2 cids2 (AccessBLEvt AccessWrite tg range2) tr2' cids2')
  : ~exists z, range'_contains range1 z /\ range'_contains range2 z.
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
    {|seq_inv:=fun tr cids =>
      (forall it,
        tree_unique tg' it tr ->
        initialized (item_lazy_perm_at_loc it z) = PermInit)
      /\ call_is_active cid cids|}
    tr1' cids1' evts12 tr2 cids2) as GenActPost. {
    pose proof (bor_local_seq_always_perminit Ex' Unq' InitPost (bor_local_seq_forget Seq12)) as Seq12Init.
    eapply seq_always_build_weaken; [|exact (seq_always_merge Seq12Init Seq12)].
    simpl. move=> ?? H; split; edestruct H; eauto.
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
  (Seq01 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr0' cids0' l tr1 cids1)
  (Read1 : bor_local_step tr1 cids1 (AccessBLEvt AccessRead tg' range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq {|seq_inv:=fun _ cids => call_is_active cid cids|} tr1' cids1' l tr2 cids2)
  (Write2 : bor_local_step tr2 cids2 (AccessBLEvt AccessWrite tg range2) tr2' cids2')
  : ~exists z, range'_contains range1 z /\ range'_contains range2 z.
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
    {|seq_inv:=fun tr cids =>
      (forall it,
        tree_unique tg' it tr ->
        initialized (item_lazy_perm_at_loc it z) = PermInit)
      /\ call_is_active cid cids|}
    tr1' cids1' evts12 tr2 cids2) as GenNonDisPost. {
    pose proof (bor_local_seq_always_perminit Ex' Unq' InitPost (bor_local_seq_forget Seq12)) as Seq12Init.
    eapply seq_always_build_weaken; [|exact (seq_always_merge Seq12Init Seq12)].
    simpl. move=> ?? [??]; auto.
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
  (Seq01 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr0' cids0' l tr1 cids1)
  (Write1 : bor_local_step tr1 cids1 (AccessBLEvt AccessWrite tg' range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq {|seq_inv:=fun _ cids => call_is_active cid cids|} tr1' cids1' l tr2 cids2)
  (Read2 : bor_local_step tr2 cids2 (AccessBLEvt AccessRead tg range2) tr2' cids2')
  : ~exists z, range'_contains range1 z /\ range'_contains range2 z.
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
    RContains1 eq_refl Write1) as [post [zpost [Unq'Post [PermPost [ActPost [ProtPost InitPost]]]]]].
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
    {|seq_inv:=fun tr cids =>
      (forall it,
        tree_unique tg' it tr ->
        initialized (item_lazy_perm_at_loc it z) = PermInit)
      /\ call_is_active cid cids|}
    tr1' cids1' evts12 tr2 cids2) as GenActPost. {
    pose proof (bor_local_seq_always_perminit Ex' Unq' InitPost (bor_local_seq_forget Seq12)) as Seq12Init.
    eapply seq_always_build_weaken; [|exact (seq_always_merge Seq12Init Seq12)].
    simpl. move=> ?? [??]; auto.
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
  (Seq01 : exists l, bor_local_seq {|seq_inv:=fun _ _ => True|} tr0' cids0' l tr1 cids1)
  (Call1 : call_is_active cid cids1)
  (Read1 : bor_local_step tr1 cids1 (AccessBLEvt AccessRead tg range1) tr1' cids1')
  (Seq12 : exists l, bor_local_seq {|seq_inv:=fun _ cids => call_is_active cid cids|} tr1' cids1' l tr2 cids2)
  (Write2 : bor_local_step tr2 cids2 (AccessBLEvt AccessWrite tg' range2) tr2' cids2')
  : ~exists z, range'_contains range1 z /\ range'_contains range2 z.
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
  destruct (protected_nonchild_read_any_to_conflicted
    Ex' Unq'
    Unrelated
    ltac:(eexists; split; [exact Protected|exact Call1])
    RContains1 eq_refl Read1
  ) as [post [zpost [Unq'Post [ProtPost [PermPost FrzLikePost]]]]].
  migrate Ex'.
  rewrite <- ProtPost in Protected.
  forget tr1.
  forget pre.

  (* opaque seq *)
  subst.
  rename Unq'Post into Unq'.
  rename post into pre.
  destruct Seq12 as [evts12 Seq12].
  pose replace FrzLikePost with bor_local_seq_last_protected_freeze_like Ex' Unq' Protected @ Seq12.
  migrate Unq'; destruct Unq' as [post [Unq' Unq'Prot]].
  pose replace FrzLikePost with @ post Unq'.
  pose proof (seq_always_destruct_last Seq12) as Prot2; simpl in Prot2.
  destruct FrzLikePost as [ProtPost FrzLike].
  migrate Ex'.

  (* read step 2 *)
  destruct (child_write_protected_freeze_like_to_ub
    Ex' Unq'
    ltac:(left; reflexivity)
    RContains2 ltac:(exists cid; split; [exact ProtPost|exact Prot2]) eq_refl
    FrzLike
    Write2).
Qed.

(* rename bor_local_seq: bor_local_steps *)
(* ghost state, ressource algebras, invariants *)

Definition disjoint' range1 range2 := ~exists z, range'_contains range1 z /\ range'_contains range2 z.

Lemma llvm_retagx_opaque_writey_writex_disjoint
  {tg_x tg_y tg_xparent tr_initial tr_final cids_initial cids_final cid new_permission opaque range_x range_y}
  (Prot : is_Some (new_protector new_permission))
  (AlreadyExists_y : tree_contains tg_y tr_initial)
  (Seq : bor_local_seq
    {|seq_inv:=fun _ cids => call_is_active cid cids|}
    tr_initial cids_initial
    (
         [RetagBLEvt tg_xparent tg_x new_permission cid]
      ++ opaque
      ++ [AccessBLEvt AccessWrite tg_y range_y]
      ++ [AccessBLEvt AccessWrite tg_x range_x]
    )
    tr_final cids_final)
  : disjoint' range_y range_x.
Proof.
  destruct (proj1 bor_local_seq_split Seq) as [?[?[SeqRetag Seq']]]; clear Seq.
  destruct (proj1 bor_local_seq_split Seq') as [?[?[SeqOpaque Seq'']]]; clear Seq'.
  destruct (proj1 bor_local_seq_split Seq'') as [?[?[SeqWritey SeqWritex]]]; clear Seq''.
  inversion SeqRetag; subst.
  inversion SeqWritey; subst.
  inversion SeqWritex; subst.
  inversion REST; subst.
  inversion HEAD; subst.
  eapply protected_fwrite_cwrite_disjoint.
  - exact AlreadyExists_y.
  - eapply COMPAT_CID. exact Prot.
  - exact HEAD.
  - exists opaque. exact (bor_local_seq_forget SeqOpaque).
  - exact INV0.
  - exact HEAD0.
  - exists []. exact (bor_local_seq_forget REST0).
  - exact HEAD1.
Qed.

Lemma llvm_retagx_opaque_writey_readx_disjoint
  {tg_x tg_y tg_xparent tr_initial tr_final cids_initial cids_final cid new_permission opaque range_x range_y}
  (Prot : is_Some (new_protector new_permission))
  (AlreadyExists_y : tree_contains tg_y tr_initial)
  (Seq : bor_local_seq
    {|seq_inv:=fun _ cids => call_is_active cid cids|}
    tr_initial cids_initial
    (
         [RetagBLEvt tg_xparent tg_x new_permission cid]
      ++ opaque
      ++ [AccessBLEvt AccessWrite tg_y range_y]
      ++ [AccessBLEvt AccessRead tg_x range_x]
    )
    tr_final cids_final)
  : disjoint' range_y range_x.
Proof.
  destruct (proj1 bor_local_seq_split Seq) as [?[?[SeqRetag Seq']]]; clear Seq.
  destruct (proj1 bor_local_seq_split Seq') as [?[?[SeqOpaque Seq'']]]; clear Seq'.
  destruct (proj1 bor_local_seq_split Seq'') as [?[?[SeqWritey SeqReadx]]]; clear Seq''.
  inversion SeqRetag; subst.
  inversion SeqWritey; subst.
  inversion SeqReadx; subst.
  inversion REST; subst.
  inversion HEAD; subst.
  eapply protected_fwrite_cread_disjoint.
  - exact AlreadyExists_y.
  - eapply COMPAT_CID. exact Prot.
  - exact HEAD.
  - exists opaque. exact (bor_local_seq_forget SeqOpaque).
  - exact INV0.
  - exact HEAD0.
  - exists []. exact (bor_local_seq_forget REST0).
  - exact HEAD1.
Qed.

Lemma llvm_retagx_opaque_readx_writey_disjoint
  {tg_x tg_y tg_xparent tr_initial tr_final cids_initial cids_final cid new_permission opaque range_x range_y}
  (Prot : is_Some (new_protector new_permission))
  (AlreadyExists_y : tree_contains tg_y tr_initial)
  (Seq : bor_local_seq
    {|seq_inv:=fun _ cids => call_is_active cid cids|}
    tr_initial cids_initial
    (
         [RetagBLEvt tg_xparent tg_x new_permission cid]
      ++ opaque
      ++ [AccessBLEvt AccessRead tg_x range_x]
      ++ [AccessBLEvt AccessWrite tg_y range_y]
    )
    tr_final cids_final)
  : disjoint' range_x range_y.
Proof.
  destruct (proj1 bor_local_seq_split Seq) as [?[?[SeqRetag Seq']]]; clear Seq.
  destruct (proj1 bor_local_seq_split Seq') as [?[?[SeqOpaque Seq'']]]; clear Seq'.
  destruct (proj1 bor_local_seq_split Seq'') as [?[?[SeqWritey SeqReadx]]]; clear Seq''.
  inversion SeqRetag; subst.
  inversion SeqReadx; subst.
  inversion SeqWritey; subst.
  inversion REST; subst.
  inversion HEAD; subst.
  eapply protected_cread_fwrite_disjoint.
  - exact AlreadyExists_y.
  - eapply COMPAT_CID. exact Prot.
  - exact HEAD.
  - exists opaque. exact (bor_local_seq_forget SeqOpaque).
  - exact HEAD1.
  - exists []. exact REST1.
  - exact HEAD0.
Qed.

Lemma llvm_retagx_opaque_writex_writey_disjoint
  {tg_x tg_y tg_xparent tr_initial tr_final cids_initial cids_final cid new_permission opaque range_x range_y}
  (Prot : is_Some (new_protector new_permission))
  (AlreadyExists_y : tree_contains tg_y tr_initial)
  (Seq : bor_local_seq
    {|seq_inv:=fun _ cids => call_is_active cid cids|}
    tr_initial cids_initial
    (
         [RetagBLEvt tg_xparent tg_x new_permission cid]
      ++ opaque
      ++ [AccessBLEvt AccessWrite tg_x range_x]
      ++ [AccessBLEvt AccessWrite tg_y range_y]
    )
    tr_final cids_final)
  : disjoint' range_x range_y.
Proof.
  destruct (proj1 bor_local_seq_split Seq) as [?[?[SeqRetag Seq']]]; clear Seq.
  destruct (proj1 bor_local_seq_split Seq') as [?[?[SeqOpaque Seq'']]]; clear Seq'.
  destruct (proj1 bor_local_seq_split Seq'') as [?[?[SeqWritex SeqWritey]]]; clear Seq''.
  inversion SeqRetag; subst.
  inversion SeqWritey; subst.
  inversion SeqWritex; subst.
  inversion REST; subst.
  inversion HEAD; subst.
  eapply protected_cwrite_fwrite_disjoint.
  - exact AlreadyExists_y.
  - eapply COMPAT_CID. exact Prot.
  - exact HEAD.
  - exists opaque. exact (bor_local_seq_forget SeqOpaque).
  - exact HEAD1.
  - exists []. exact REST1.
  - exact HEAD0.
Qed.

Lemma llvm_retagx_opaque_writex_ready_disjoint
  {tg_x tg_y tg_xparent tr_initial tr_final cids_initial cids_final cid new_permission opaque range_x range_y}
  (Prot : is_Some (new_protector new_permission))
  (AlreadyExists_y : tree_contains tg_y tr_initial)
  (Seq : bor_local_seq
    {|seq_inv:=fun _ cids => call_is_active cid cids|}
    tr_initial cids_initial
    (
         [RetagBLEvt tg_xparent tg_x new_permission cid]
      ++ opaque
      ++ [AccessBLEvt AccessWrite tg_x range_x]
      ++ [AccessBLEvt AccessRead tg_y range_y]
    )
    tr_final cids_final)
  : disjoint' range_x range_y.
Proof.
  destruct (proj1 bor_local_seq_split Seq) as [?[?[SeqRetag Seq']]]; clear Seq.
  destruct (proj1 bor_local_seq_split Seq') as [?[?[SeqOpaque Seq'']]]; clear Seq'.
  destruct (proj1 bor_local_seq_split Seq'') as [?[?[SeqWritex SeqWritey]]]; clear Seq''.
  inversion SeqRetag; subst.
  inversion SeqWritey; subst.
  inversion SeqWritex; subst.
  inversion REST; subst.
  inversion HEAD; subst.
  eapply protected_cwrite_fread_disjoint.
  - exact AlreadyExists_y.
  - eapply COMPAT_CID. exact Prot.
  - exact HEAD.
  - exists opaque. exact (bor_local_seq_forget SeqOpaque).
  - exact HEAD1.
  - exists []. exact REST1.
  - exact HEAD0.
Qed.

Lemma llvm_retagx_opaque_ready_writex_disjoint
  {tg_x tg_y tg_xparent tr_initial tr_final cids_initial cids_final cid new_permission opaque range_x range_y}
  (Prot : is_Some (new_protector new_permission))
  (AlreadyExists_y : tree_contains tg_y tr_initial)
  (Seq : bor_local_seq
    {|seq_inv:=fun _ cids => call_is_active cid cids|}
    tr_initial cids_initial
    (
         [RetagBLEvt tg_xparent tg_x new_permission cid]
      ++ opaque
      ++ [AccessBLEvt AccessRead tg_y range_y]
      ++ [AccessBLEvt AccessWrite tg_x range_x]
    )
    tr_final cids_final)
  : disjoint' range_y range_x.
Proof.
  destruct (proj1 bor_local_seq_split Seq) as [?[?[SeqRetag Seq']]]; clear Seq.
  destruct (proj1 bor_local_seq_split Seq') as [?[?[SeqOpaque Seq'']]]; clear Seq'.
  destruct (proj1 bor_local_seq_split Seq'') as [?[?[SeqWritey SeqWritex]]]; clear Seq''.
  inversion SeqRetag; subst.
  inversion SeqWritey; subst.
  inversion SeqWritex; subst.
  inversion REST; subst.
  inversion HEAD; subst.
  eapply protected_fread_cwrite_disjoint.
  - exact AlreadyExists_y.
  - eapply COMPAT_CID. exact Prot.
  - exact HEAD.
  - exists opaque. exact (bor_local_seq_forget SeqOpaque).
  - exact INV0.
  - exact HEAD0.
  - exists []. exact REST0.
  - exact HEAD1.
Qed.



(* --- Reordering read-read --- *)

Lemma item_eq
  {it0 it1}
  (EQ_IPROT : iprot it0 = iprot it1)
  (EQ_INITP : initp it0 = initp it1)
  (EQ_ITAG : itag it0 = itag it1)
  (EQ_EVERY_IPERM : forall z, iperm it0 !! z = iperm it1 !! z)
  : it0 = it1.
Proof.
  destruct it0; destruct it1; simpl in *.
  f_equal; [assumption|assumption|assumption|].
  apply map_eq; assumption.
Qed.

Definition commutes {X}
  (fn1 fn2 : X -> option X)
  := forall x0 x1 x2,
  fn1 x0 = Some x1 ->
  fn2 x1 = Some x2 ->
  exists x1', (
    fn2 x0 = Some x1'
    /\ fn1 x1' = Some x2
  ).

Definition commutes_option {X}
  (fn1 fn2 : option X -> option X)
  := forall x0 x1 x2,
  fn1 x0 = Some x1 ->
  fn2 (Some x1) = Some x2 ->
  exists x1', (
    fn2 x0 = Some x1'
    /\ fn1 (Some x1') = Some x2
  ).

Lemma apply_access_perm_read_commutes
  {rel1 rel2 prot}
  : commutes
    (apply_access_perm AccessRead rel1 prot true)
    (apply_access_perm AccessRead rel2 prot true).
Proof.
  move=> p0 p1 p2 Step01 Step12.
  unfold apply_access_perm in *.
  all: destruct p0 as [[][]].
  all: destruct prot; simpl in *.
  all: destruct rel1; simpl in *.
  all: try (inversion Step01; done).
  all: injection Step01; intros; subst.
  all: simpl.
  all: destruct rel2; simpl in *.
  all: try (inversion Step12; done).
  all: injection Step12; intros; subst; simpl.
  all: try (eexists; split; [reflexivity|]); simpl.
  all: reflexivity.
Qed.

Lemma range'_foreach_success_condition
  {X} {fn : option X -> option X} {range mem}
  (ALL_SOME : forall z, range'_contains range z -> is_Some (fn (mem !! z)))
  : exists mem', range'_foreach fn range mem = Some mem'.
Proof.
  unfold range'_foreach.
  destruct range as [z sz]; simpl.
  generalize dependent z.
  induction sz; move=> z ALL_SOME.
  - eexists. simpl. reflexivity.
  - destruct (IHsz (z + 1)%Z
      ltac:(intros mem' H; apply ALL_SOME; unfold range'_contains; unfold range'_contains in H; simpl; simpl in H; lia))
      as [sub' Specsub'].
    destruct (ALL_SOME z ltac:(unfold range'_contains; simpl; lia)) as [fnz Specfnz].
    eexists (<[z:=fnz]>sub').
    unfold mem_foreach; simpl.
    unfold mem_foreach in Specsub'.
    rewrite Specfnz; simpl.
    rewrite Specsub'; simpl.
    reflexivity.
Qed.

Lemma range_foreach_success_specification
  {X} {fn : option X -> option X} {range mem mem'}
  (ALL_SOME : forall z, range'_contains range z -> exists x', fn (mem !! z) = Some x' /\ mem' !! z = Some x')
  (REST_SAME : forall z, ~range'_contains range z -> mem !! z = mem' !! z)
  : range'_foreach fn range mem = Some mem'.
Proof.
  assert (forall z, range'_contains range z -> is_Some (fn (mem !! z))) as ALL_SOME_weaker. {
    intros z R; destruct (ALL_SOME z R) as [?[??]]; auto.
  }
  destruct (range'_foreach_success_condition ALL_SOME_weaker) as [mem'' Spec''].
  rewrite Spec''; f_equal; apply map_eq.
  intro z.
  pose proof (range'_foreach_spec _ _ z _ _ Spec'') as Spec.
  destruct (decide (range'_contains range z)) as [R|nR].
  - destruct Spec as [v[vSpec fnvSpec]].
    destruct (ALL_SOME z R) as [v' [fnv'Spec v'Spec]].
    rewrite v'Spec.
    rewrite vSpec.
    rewrite <- fnv'Spec.
    rewrite <- fnvSpec.
    reflexivity.
  - rewrite <- (REST_SAME z nR).
    assumption.
Qed.

Lemma range_foreach_commutes
  {X}
  range1 range2
  (fn1 fn2 : option X -> option X)
  (FnCommutes : commutes_option fn1 fn2)
  : commutes
    (range'_foreach fn1 range1)
    (range'_foreach fn2 range2).
Proof.
  intros mem0 mem1 mem2 Success01 Success12.
  assert (forall z, range'_contains range2 z -> exists x1', fn2 (mem0 !! z) = Some x1') as fn2mem0. {
    intros z R2.
    pose proof (range'_foreach_spec _ _ z _ _ Success01) as Spec01.
    pose proof (range'_foreach_spec _ _ z _ _ Success12) as Spec12.
    destruct (decide (range'_contains range1 z)).
    - destruct Spec01 as [fn1z0 [z1Spec fn1z0Spec]].
      rewrite decide_True in Spec12; [|assumption].
      destruct Spec12 as [fn2z1 [z2Spec fn2z1Spec]].
      rewrite z1Spec in fn2z1Spec.
      destruct (FnCommutes _ _ _ fn1z0Spec fn2z1Spec) as [x1' [fn2z0Spec fn1x1'Spec]].
      exists x1'; assumption.
    - rewrite decide_True in Spec12; [|assumption].
      destruct Spec12 as [x2 [x2Spec fn2x1Spec]].
      exists x2; rewrite <- Spec01; assumption.
  }
  destruct (range'_foreach_success_condition fn2mem0) as [mem1' Success01'].
  exists mem1'.
  split; [assumption|].
  apply range_foreach_success_specification.
  - intros z R1.
    pose proof (range'_foreach_spec _ _ z _ _ Success01) as Spec01.
    pose proof (range'_foreach_spec _ _ z _ _ Success12) as Spec12.
    pose proof (range'_foreach_spec _ _ z _ _ Success01') as Spec01'.
    destruct (decide (range'_contains range2 z)).
    + rewrite decide_True in Spec01; [|assumption].
      destruct Spec01 as [fn1z0 [z1Spec fn1z0Spec]].
      destruct Spec12 as [fn2z1 [z2Spec fn2z1Spec]].
      destruct Spec01' as [fn2z0 [z1'Spec fn2z0Spec]].
      rewrite z1Spec in fn2z1Spec.
      destruct (FnCommutes _ _ _ fn1z0Spec fn2z1Spec) as [x2' [fn2z0'Spec fn1x2'Spec]].
      rewrite z1'Spec.
      rewrite <- fn2z0Spec.
      exists fn2z1.
      split; [|assumption].
      destruct (FnCommutes _ _ _ fn1z0Spec fn2z1Spec) as [x1' [fn2z0Spec' fn1x1'Spec]].
      rewrite fn2z0Spec'.
      rewrite fn1x1'Spec.
      reflexivity.
    + rewrite decide_True in Spec01; [|assumption].
      destruct Spec01 as [fn1z0 [z1Spec fn1z0Spec]].
      rewrite Spec01'.
      rewrite Spec12.
      exists fn1z0; split; assumption.
  - intros z nR1.
    pose proof (range'_foreach_spec _ _ z _ _ Success01) as Spec01.
    pose proof (range'_foreach_spec _ _ z _ _ Success01') as Spec01'.
    pose proof (range'_foreach_spec _ _ z _ _ Success12) as Spec12.
    destruct (decide (range'_contains range2 z)).
    + rewrite decide_False in Spec01; [|assumption].
      destruct Spec01' as [fn2z0 [z1'Spec fn2z0Spec]].
      destruct Spec12 as [fn2z1 [z2Spec fn2z1Spec]].
      rewrite z1'Spec.
      rewrite <- fn2z0Spec.
      rewrite <- Spec01.
      rewrite fn2z1Spec.
      rewrite z2Spec.
      reflexivity.
    + rewrite decide_False in Spec01; [|assumption].
      rewrite Spec01'.
      rewrite <- Spec01.
      rewrite Spec12.
      reflexivity.
Qed.

Lemma range_foreach_disjoint_commutes
  {X} {fn1 fn2 : option X -> option X} {range1 range2}
  (Disjoint : disjoint' range1 range2)
  : commutes
    (range'_foreach fn1 range1)
    (range'_foreach fn2 range2).
Proof.
  intros mem0 mem1 mem2 Success01 Success12.
  assert (forall z, range'_contains range2 z -> exists x1', fn2 (mem0 !! z) = Some x1') as fn2mem0. {
    intros z R2.
    pose proof (range'_foreach_spec _ _ z _ _ Success01) as Spec01.
    pose proof (range'_foreach_spec _ _ z _ _ Success12) as Spec12.
    destruct (decide (range'_contains range1 z)).
    - exfalso; apply Disjoint; eexists; eauto.
    - rewrite decide_True in Spec12; [|assumption].
      destruct Spec12 as [x2 [x2Spec fn2x1Spec]].
      exists x2; rewrite <- Spec01; assumption.
  }
  destruct (range'_foreach_success_condition fn2mem0) as [mem1' Success01'].
  exists mem1'.
  split; [assumption|].
  apply range_foreach_success_specification.
  - intros z R1.
    pose proof (range'_foreach_spec _ _ z _ _ Success01) as Spec01.
    pose proof (range'_foreach_spec _ _ z _ _ Success12) as Spec12.
    pose proof (range'_foreach_spec _ _ z _ _ Success01') as Spec01'.
    destruct (decide (range'_contains range2 z)).
    + exfalso; apply Disjoint; eexists; eauto.
    + rewrite decide_True in Spec01; [|assumption].
      destruct Spec01 as [fn1z0 [z1Spec fn1z0Spec]].
      rewrite Spec01'.
      rewrite Spec12.
      exists fn1z0; split; assumption.
  - intros z nR1.
    pose proof (range'_foreach_spec _ _ z _ _ Success01) as Spec01.
    pose proof (range'_foreach_spec _ _ z _ _ Success01') as Spec01'.
    pose proof (range'_foreach_spec _ _ z _ _ Success12) as Spec12.
    destruct (decide (range'_contains range2 z)).
    + rewrite decide_False in Spec01; [|assumption].
      destruct Spec01' as [fn2z0 [z1'Spec fn2z0Spec]].
      destruct Spec12 as [fn2z1 [z2Spec fn2z1Spec]].
      rewrite z1'Spec.
      rewrite <- fn2z0Spec.
      rewrite <- Spec01.
      rewrite fn2z1Spec.
      rewrite z2Spec.
      reflexivity.
    + rewrite decide_False in Spec01; [|assumption].
      rewrite Spec01'.
      rewrite <- Spec01.
      rewrite Spec12.
      reflexivity.
Qed.

Lemma commutes_option_build
  {X} {default : X} {fn1 fn2}
  (Commutes : commutes fn1 fn2)
  : commutes_option
    (fun ox => fn1 (unwrap default ox))
    (fun ox => fn2 (unwrap default ox)).
Proof.
  intros x0 x1 x2 Step01 Step12.
  destruct (Commutes (unwrap default x0) _ _ Step01 Step12) as [?[??]].
  eexists; eauto.
Qed.

Lemma permissions_foreach_commutes
  range1 range2
  (fn1 fn2 : lazy_permission -> option lazy_permission)
  default
  (FnCommutes : commutes fn1 fn2)
  : commutes
    (permissions_foreach default range1 fn1)
    (permissions_foreach default range2 fn2).
Proof.
  apply range_foreach_commutes.
  apply commutes_option_build.
  assumption.
Qed.

Lemma permissions_foreach_disjoint_commutes
  range1 range2
  (fn1 fn2 : lazy_permission -> option lazy_permission)
  default
  (Disjoint : disjoint' range1 range2)
  : commutes
    (permissions_foreach default range1 fn1)
    (permissions_foreach default range2 fn2).
Proof.
  apply range_foreach_disjoint_commutes.
  assumption.
Qed.

Lemma item_apply_access_read_commutes
  {cids rel1 rel2 range1 range2}
  : commutes
    (item_apply_access AccessRead ProtStrong cids rel1 range1)
    (item_apply_access AccessRead ProtStrong cids rel2 range2).
Proof.
  intros it0 it1 it2 Step01 Step12.
  option step in Step01 as ?:S1.
  option step in Step12 as ?:S2.
  injection Step01; destruct it1; intro H; injection H; intros; subst; simpl in *; clear Step01; clear H.
  injection Step12; destruct it2; intro H; injection H; intros; subst; simpl in *; clear Step12; clear H.
  destruct (permissions_foreach_commutes
    range1 range2
    _ _
    {| initialized:=PermLazy; perm:=initp it0 |}
    (apply_access_perm_read_commutes (rel1:=rel1) (rel2:=rel2) (prot:=bool_decide (protector_is_active (iprot it0) cids)))
    (lang_base.iperm it0) iperm iperm0) as [perms' [Pre Post]]; [exact S1|exact S2|].
  unfold item_apply_access.
  rewrite Pre; simpl.
  eexists; split; [reflexivity|].
  simpl. rewrite Post; simpl.
  reflexivity.
Qed.

Lemma item_apply_access_disjoint_commutes
  {cids rel1 rel2 kind1 kind2 range1 range2}
  (Disjoint : disjoint' range1 range2)
  : commutes
    (item_apply_access kind1 ProtStrong cids rel1 range1)
    (item_apply_access kind2 ProtStrong cids rel2 range2).
Proof.
  intros it0 it1 it2 Step01 Step12.
  option step in Step01 as ?:S1.
  option step in Step12 as ?:S2.
  injection Step01; destruct it1; intro H; injection H; intros; subst; simpl in *; clear Step01; clear H.
  injection Step12; destruct it2; intro H; injection H; intros; subst; simpl in *; clear Step12; clear H.
  edestruct (permissions_foreach_disjoint_commutes
    range1 range2
    (apply_access_perm kind1 rel1 (bool_decide (protector_is_active (iprot it0) cids)) true)
    (apply_access_perm kind2 rel2 (bool_decide (protector_is_active (iprot it0) cids)) true)
    {| initialized:=PermLazy; perm:=initp it0 |}
  ) as [?[Pre Post]]; eauto.
  unfold item_apply_access.
  rewrite Pre; simpl.
  eexists; split; [reflexivity|].
  simpl. rewrite Post; simpl.
  reflexivity.
Qed.

Lemma apply_access_success_condition
  {fn cids access_tag range tr} {dyn_rel : rel_dec tr}
  (ALL_SOME : every_node
    (fun it => is_Some (fn cids (if dyn_rel (itag it) access_tag then AccessChild else AccessForeign) range it)) tr)
  : exists tr', tree_apply_access fn cids access_tag range tr dyn_rel = Some tr'.
Proof.
  assert (every_node is_Some (map_nodes (fun it => fn cids (if dyn_rel (itag it) access_tag then AccessChild else AccessForeign) range it) tr)) as AllSomeMap by (rewrite every_node_map; assumption).
  destruct (proj2 (join_success_condition _) AllSomeMap).
  eexists; eassumption.
Qed.

Lemma join_map_commutes
  {fn1 fn2 : call_id_set -> access_rel -> Z * nat -> tree.app item} {cids access_tag1 access_tag2 range1 range2}
  (Fn1PreservesTag : forall it it' cids rel range, fn1 cids rel range it = Some it' -> itag it = itag it')
  (Fn2PreservesTag : forall it it' cids rel range, fn2 cids rel range it = Some it' -> itag it = itag it')
  (Commutes : forall rel1 rel2, commutes
    (fn1 cids rel1 range1)
    (fn2 cids rel2 range2))
  : forall tr (dyn_rel : rel_dec tr),
    commutes
      (fun tr => join_nodes (map_nodes (fun it => fn1 cids (if dyn_rel (itag it) access_tag1 then AccessChild else AccessForeign) range1 it) tr))
      (fun tr => join_nodes (map_nodes (fun it => fn2 cids (if dyn_rel (itag it) access_tag2 then AccessChild else AccessForeign) range2 it) tr)).
Proof.
  intros tr dyn_rel tr0.
  induction tr0 as [|data0 left0 IHleft right0 IHright]; intros tr1 tr2 Step01 Step12.
  - simpl in Step01; injection Step01; intros; subst.
    simpl in Step12; injection Step12; intros; subst.
    exists tree.empty; simpl; tauto.
  - option step in Step01 as data1:Data01.
    option step in Step01 as left1:Left01.
    option step in Step01 as right1:Right01.
    injection Step01; intros; subst.
    option step in Step12 as data2:Data12.
    option step in Step12 as left2:Left12.
    option step in Step12 as right2:Right12.
    injection Step12; intros; subst.
    destruct (Commutes _ _ data0 data1 data2 Data01 Data12) as [data1' [Data01' Data1'2]].
    destruct (IHleft left1 left2 Left01 Left12) as [left1' [Left01' Left1'2]].
    destruct (IHright right1 right2 Right01 Right12) as [right1' [Right01' Right1'2]].
    exists (branch data1' left1' right1').
    simpl in *.
    assert (itag data0 = itag data1) as Tg01 by (eapply Fn1PreservesTag; eassumption).
    assert (itag data0 = itag data1') as Tg01' by (eapply Fn2PreservesTag; eassumption).
    rewrite Tg01; rewrite Data01'; simpl.
    rewrite Left01'; simpl.
    rewrite Right01'; simpl.
    rewrite <- Tg01'; rewrite Data1'2; simpl.
    rewrite Left1'2; simpl.
    rewrite Right1'2; simpl.
    tauto.
Qed.

Lemma tree_apply_access_only_cares_about_rel_on_support
  {tr} {fn : call_id_set -> access_rel -> Z * nat -> tree.app item} {cids access_tag range}
  {tr1 tr2} (dyn_rel1 : rel_dec tr1) (dyn_rel2 : rel_dec tr2)
  (Agree : forall tg tg', tree_contains tg tr -> ParentChildIn tg tg' tr1 <-> ParentChildIn tg tg' tr2)
  : join_nodes (map_nodes (fun it => fn cids (if dyn_rel1 (itag it) access_tag then AccessChild else AccessForeign) range it) tr)
  = join_nodes (map_nodes (fun it => fn cids (if dyn_rel2 (itag it) access_tag then AccessChild else AccessForeign) range it) tr).
Proof.
  induction tr as [|data sibling IHsibling child IHchild]; [simpl; reflexivity|].
  simpl.
  rewrite IHsibling; [|intros; apply Agree; right; left; assumption].
  rewrite IHchild; [|intros; apply Agree; right; right; assumption].
  destruct (dyn_rel2 _ _) as [R|R]; destruct (dyn_rel1 _ _).
  all: rewrite <- Agree in R; [|left; simpl; done].
  all: try contradiction.
  all: reflexivity.
Qed.

Lemma tree_apply_access_commutes
  {fn1 fn2 cids access_tag1 access_tag2 range1 range2}
  (Fn1PreservesTag : forall it it' cids rel range, fn1 cids rel range it = Some it' -> itag it = itag it')
  (Fn2PreservesTag : forall it it' cids rel range, fn2 cids rel range it = Some it' -> itag it = itag it')
  (Commutes : forall rel1 rel2, commutes
    (fn1 cids rel1 range1)
    (fn2 cids rel2 range2))
  : commutes
    (fun tr => tree_apply_access fn1 cids access_tag1 range1 tr (naive_rel_dec tr))
    (fun tr => tree_apply_access fn2 cids access_tag2 range2 tr (naive_rel_dec tr)).
Proof.
  unfold tree_apply_access.
  intros tr0 tr1 tr2 Step01 Step12.
  erewrite (tree_apply_access_only_cares_about_rel_on_support _ (naive_rel_dec tr0)) in Step12.
  2: { intros. symmetry. exact (join_map_eqv_rel (fun it it' => Fn1PreservesTag it it' _ _ _) Step01). }
  destruct (join_map_commutes Fn1PreservesTag Fn2PreservesTag Commutes _ (naive_rel_dec tr0) tr0 tr1 tr2 Step01 Step12) as [tr1' [Step01' Step1'2]].
  exists tr1'.
  split; [assumption|].
  erewrite (tree_apply_access_only_cares_about_rel_on_support _ (naive_rel_dec tr0)).
  2: { intros. symmetry. exact (join_map_eqv_rel (fun it it' => Fn2PreservesTag it it' _ _ _) Step01'). }
  assumption.
Qed.

Lemma memory_access_read_commutes
  {cids access_tag1 access_tag2 range1 range2}
  : commutes
    (memory_access AccessRead ProtStrong cids access_tag1 range1)
    (memory_access AccessRead ProtStrong cids access_tag2 range2).
Proof.
  unfold memory_access.
  apply tree_apply_access_commutes.
  1,2: intros; eapply item_apply_access_preserves_tag; eassumption.
  intros.
  apply item_apply_access_read_commutes.
Qed.

Lemma memory_access_disjoint_commutes
  {cids kind1 kind2 access_tag1 access_tag2 range1 range2}
  (Disjoint : disjoint' range1 range2)
  : commutes
    (memory_access kind1 ProtStrong cids access_tag1 range1)
    (memory_access kind2 ProtStrong cids access_tag2 range2).
Proof.
  unfold memory_access.
  apply tree_apply_access_commutes.
  1,2: intros; eapply item_apply_access_preserves_tag; eassumption.
  intros.
  apply item_apply_access_disjoint_commutes; assumption.
Qed.

Lemma llvm_read_read_reorder
  {tr_initial cids_initial tr_final cids_final access_tag1 access_tag2 range1 range2}
  (Seq12 : bor_local_seq
    {|seq_inv:=fun _ _ => True|}
    tr_initial cids_initial
    (
         [AccessBLEvt AccessRead access_tag1 range1]
      ++ [AccessBLEvt AccessRead access_tag2 range2]
    )
    tr_final cids_final
  )
  : bor_local_seq
    {|seq_inv:=fun _ _ => True|}
    tr_initial cids_initial
    (
         [AccessBLEvt AccessRead access_tag2 range2]
      ++ [AccessBLEvt AccessRead access_tag1 range1]
    )
    tr_final cids_final.
Proof.
  rewrite bor_local_seq_split.
  rewrite bor_local_seq_split in Seq12.
  destruct Seq12 as [tr_interm [cids_interm [Pre Post]]].
  inversion Pre; subst.
  inversion Post; subst.
  inversion REST; subst.
  inversion REST0; subst.
  inversion HEAD; subst.
  inversion HEAD0; subst.
  destruct (memory_access_read_commutes tr_initial tr_interm tr_final ACC ACC0) as [tr_alt [PreAlt PostAlt]].

  exists tr_alt, cids_final.
  split.
  - econstructor; [done|constructor; [|exact PreAlt]|constructor; done].
    erewrite access_preserves_tags; eauto; apply item_apply_access_preserves_tag.
  - econstructor; [done|constructor; [|exact PostAlt]|constructor; done].
    erewrite <- access_preserves_tags; eauto; apply item_apply_access_preserves_tag.
Qed.

Lemma disjoint'_sym {range1 range2} : disjoint' range1 range2 <-> disjoint' range2 range1.
Proof. unfold disjoint'; split; intros P Q; apply P; destruct Q as [?[??]]; eexists; split; eauto. Qed.

Lemma llvm_disjoint_reorder
  {tr_initial cids_initial tr_final cids_final access_tag1 access_tag2 range1 range2 kind1 kind2}
  (Disjoint : disjoint' range1 range2)
  (Seq12 : bor_local_seq
    {|seq_inv:=fun _ _ => True|}
    tr_initial cids_initial
    (
         [AccessBLEvt kind1 access_tag1 range1]
      ++ [AccessBLEvt kind2 access_tag2 range2]
    )
    tr_final cids_final
  )
  : bor_local_seq
    {|seq_inv:=fun _ _ => True|}
    tr_initial cids_initial
    (
         [AccessBLEvt kind2 access_tag2 range2]
      ++ [AccessBLEvt kind1 access_tag1 range1]
    )
    tr_final cids_final.
Proof.
  rewrite bor_local_seq_split.
  rewrite bor_local_seq_split in Seq12.
  destruct Seq12 as [tr_interm [cids_interm [Pre Post]]].
  inversion Pre; subst.
  inversion Post; subst.
  inversion REST; subst.
  inversion REST0; subst.
  inversion HEAD; subst.
  inversion HEAD0; subst.
  destruct (memory_access_disjoint_commutes Disjoint tr_initial tr_interm tr_final ACC ACC0) as [tr_alt [PreAlt PostAlt]].

  exists tr_alt, cids_final.
  split.
  - econstructor; [done|constructor; [|exact PreAlt]|constructor; done].
    erewrite access_preserves_tags; eauto; apply item_apply_access_preserves_tag.
  - econstructor; [done|constructor; [|exact PostAlt]|constructor; done].
    erewrite <- access_preserves_tags; eauto; apply item_apply_access_preserves_tag.
Qed.

Lemma bor_local_seq_accesses_same_cids
  {tr cid cids evts tr' cids'}
  (StartsActive : call_is_active cid cids)
  (Seq : bor_local_seq {|seq_inv:=fun _ _ => True|} tr cids evts tr' cids')
  (NoEndCall : Forall (fun evt => evt ≠ EndCallBLEvt cid) evts)
  : bor_local_seq
    {|seq_inv:=fun _ cids => call_is_active cid cids|}
    tr cids evts tr' cids'.
Proof.
  generalize dependent tr.
  generalize dependent cids.
  induction evts; move=> ??? Seq; inversion Seq; subst.
  - constructor; assumption.
  - econstructor.
    + assumption.
    + eassumption.
    + eapply IHevts.
      * inversion NoEndCall; subst; assumption.
      * inversion HEAD; subst.
        -- eassumption.
        -- unfold call_is_active. rewrite elem_of_union. right.
           assumption.
        -- assert (cid ≠ cid0) as OtherCid by (intro; inversion NoEndCall; apply H2; subst; reflexivity).
           unfold call_is_active. rewrite elem_of_difference.
           split; [assumption|].
           rewrite not_elem_of_singleton; assumption.
        -- assumption.
      * assumption.
Qed.

Theorem llvm_noalias_reorder
  {tg_xparent new_permission cid}
  {tg_x kind_x range_x}
  {tg_y kind_y range_y}
  {tr_initial cids_initial opaque tr_final cids_final}
  (HasProtector_x : is_Some (new_protector new_permission))
  (AlreadyExists_y : tree_contains tg_y tr_initial) :
  let retag_x := RetagBLEvt tg_xparent tg_x new_permission cid in
  let access_y := AccessBLEvt kind_y tg_y range_y in
  let access_x := AccessBLEvt kind_x tg_x range_x in
  let invariant := {| seq_inv := fun _ cids => call_is_active cid cids |} in
  (bor_local_seq invariant tr_initial cids_initial ([retag_x] ++ opaque ++ [access_y] ++ [access_x]) tr_final cids_final)
  <->
  (bor_local_seq invariant tr_initial cids_initial ([retag_x] ++ opaque ++ [access_x] ++ [access_y]) tr_final cids_final).
Proof.
  split; intro Seq.
  - destruct kind_x, kind_y.
    2: assert (disjoint' range_y range_x) by (eapply llvm_retagx_opaque_writey_readx_disjoint; eassumption).
    3: assert (disjoint' range_y range_x) by (eapply llvm_retagx_opaque_ready_writex_disjoint; eassumption).
    4: assert (disjoint' range_y range_x) by (eapply llvm_retagx_opaque_writey_writex_disjoint; eassumption).
    all: rewrite bor_local_seq_split in Seq; destruct Seq as [?[? [Pre1 Seq]]].
    all: rewrite bor_local_seq_split in Seq; destruct Seq as [?[? [Pre2 Seq]]].
    all: rewrite bor_local_seq_split; eexists; eexists; split; [eassumption|].
    all: rewrite bor_local_seq_split; eexists; eexists; split; [eassumption|].
    all: eapply bor_local_seq_accesses_same_cids; [exact (seq_always_destruct_first Seq)| |simpl; auto].
    1: apply llvm_read_read_reorder; eapply bor_local_seq_forget; eassumption.
    all: apply llvm_disjoint_reorder; [assumption|].
    all: eapply bor_local_seq_forget; eassumption.
  - destruct kind_x, kind_y.
    2: assert (disjoint' range_x range_y) by (eapply llvm_retagx_opaque_readx_writey_disjoint; eassumption).
    3: assert (disjoint' range_x range_y) by (eapply llvm_retagx_opaque_writex_ready_disjoint; eassumption).
    4: assert (disjoint' range_x range_y) by (eapply llvm_retagx_opaque_writex_writey_disjoint; eassumption).
    all: rewrite bor_local_seq_split in Seq; destruct Seq as [?[? [Pre1 Seq]]].
    all: rewrite bor_local_seq_split in Seq; destruct Seq as [?[? [Pre2 Seq]]].
    all: rewrite bor_local_seq_split; eexists; eexists; split; [eassumption|].
    all: rewrite bor_local_seq_split; eexists; eexists; split; [eassumption|].
    all: eapply bor_local_seq_accesses_same_cids; [exact (seq_always_destruct_first Seq)| |simpl; auto].
    1: apply llvm_read_read_reorder; eapply bor_local_seq_forget; eassumption.
    all: apply llvm_disjoint_reorder; [assumption|].
    all: eapply bor_local_seq_forget; eassumption.
Qed.



