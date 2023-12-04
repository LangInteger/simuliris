(** This file has been adapted from the Stacked Borrows development, available at 
https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From Equations Require Import Equations.
From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Export lang_base notation tree tree_lemmas.
From iris.prelude Require Import options.

Lemma decision_equiv (P Q:Prop) :
  (P <-> Q) ->
  Decision P ->
  Decision Q.
Proof.
  unfold Decision. tauto.
Qed.

(*** TREE BORROWS SEMANTICS ---------------------------------------------***)

Implicit Type (c:call_id) (cids:call_id_set).
Implicit Type (blk:block) (n sz:nat) (z:Z) (range:Z * nat).
Implicit Type (trs:trees) (t:tag).

Definition range'_contains (r:range') (l:loc') : Prop :=
  (r.1 ≤ l)%Z /\ (l < r.1 + r.2)%Z.
Global Instance decision_range'_contains (r:range') (l:loc') : Decision (range'_contains r l).
Proof. solve_decision. Qed.

Definition range_contains (r:range) (l:loc) : Prop :=
  r.1 = l.1 /\ range'_contains r.2 l.2.
Global Instance decision_range_contains (r:range) (l:loc) : Decision (range_contains r l).
Proof. solve_decision. Qed.

Lemma range'_contains_excludes_equal range z' :
  let '(z, sz) := range in
  range'_contains (z, S sz) z' -> ~(range'_contains ((z + 1)%Z, sz) z') -> z = z'.
Proof.
  destruct range.
  intros Contains Excludes.
  unfold range'_contains in *; simpl in *.
  lia.
Qed.

Definition mem_apply_loc {X} (fn : option X -> option X) z
  : app (gmap loc' X) := fun map =>
    new ← fn (map !! z);
    Some (<[z := new]> map).

Fixpoint mem_apply_locs {X} (fn:option X -> option X) z sz
  {struct sz} : app (gmap loc' X) := fun map =>
  match sz with
  | O => Some map
  | S sz' =>
      newmap ← mem_apply_loc fn z map;
      mem_apply_locs fn (z + 1)%Z sz' newmap
  end.

Definition mem_enumerate_sat {X} (fn : X -> bool)
  : gmap loc' X -> list Z :=
  gmap_fold _ (fun k v acc =>
    if fn v then k :: acc else acc
  ) [] .

Fixpoint mem_fold_apply {X} (fn : option X -> option X) locs
  : app (gmap loc' X) := fun map =>
  match locs with
  | [] => Some map
  | z::locs' =>
      newmap ← mem_apply_loc fn z map;
      mem_fold_apply fn locs' newmap
  end.

Definition mem_apply_range' {X} (fn:option X -> option X) (r:range')
  : app (gmap loc' X) := mem_apply_locs fn r.1 r.2.

Lemma mem_apply_range'_spec {X} fn r z' :
  forall (map newmap: gmap loc' X),
  (mem_apply_range' fn r map = Some newmap) ->
  if (decide (range'_contains r z'))
    then exists val, newmap !! z' = Some val /\ fn (map !! z') = Some val
    else newmap !! z' = map !! z'.
Proof.
  unfold mem_apply_range'.
  destruct r as [z sz].
  generalize dependent z'.
  generalize dependent z.
  induction sz as [|sz IHsz]; intros z z' map newmap MemForeach.
  - unfold mem_apply_locs in MemForeach. injection MemForeach; intro; subst.
    destruct (decide (range'_contains (z, 0) z')) as [Contains | NotContains]; auto.
    unfold range'_contains in Contains; simpl in Contains. lia.
  (* Case 1: the item is at the beginning of the range.
     -> it will be unchanged by the aux function and written by the current one *)
  - destruct (decide (z = z')) as [Eql | Neq].
    + subst. assert (range'_contains (z', S sz) z') as ContainsS by (unfold range'_contains; simpl; lia).
      decide (decide (range'_contains (z', S sz) z')) with ContainsS.
      simpl in MemForeach.
      unfold mem_apply_loc in MemForeach.
      destruct (fn (map !! z')) as [x|]; simpl in *; [|inversion MemForeach].
      destruct (mem_apply_locs fn (z' + 1) sz _) eqn:Rec; [|inversion MemForeach]; simpl in *.
      injection MemForeach; intro; subst.
      exists x; split; auto.
      pose proof (IHsz _ z' _ _ Rec) as Unchanged.
      assert (~range'_contains ((z' + 1)%Z, sz) z') by (unfold range'_contains; simpl; lia).
      destruct (decide (range'_contains ((z'+1)%Z, sz) z')); [contradiction|].
      rewrite Unchanged.
      apply lookup_insert.
  (* Case 2: the item is in the middle of the range or completely outside.
     -> the map we get from the aux call is not altered on the location that matters *)
    + simpl in MemForeach.
      unfold mem_apply_loc in MemForeach.
      destruct (fn (map !! z)) eqn:Fn; simpl in *; [|inversion MemForeach].
      destruct (mem_apply_locs fn (z + 1) sz _) eqn:Rec; simpl in *; [|inversion MemForeach].
      specialize (IHsz _ z' _ _ Rec).
      * destruct (decide (range'_contains ((z + 1)%Z, sz) z')) as [Contains' | NotContains'].
        all: destruct (decide (range'_contains (z, S sz) z')) as [ContainsS' | NotContainsS'].
        (* bad range *)
        all: try (exfalso; unfold range'_contains in *; simpl in *; lia).
        (* good case *)
        -- destruct IHsz as [x0 [z'val fnval]].
           injection MemForeach; intros; subst.
           exists x0; split; auto.
           rewrite lookup_insert_ne in fnval; auto.
        -- injection MemForeach; intros; subst.
           rewrite lookup_insert_ne in IHsz; auto.
Qed.

Definition permissions_apply_range' (pdefault:lazy_permission) (range:range') (f:app lazy_permission)
  : app permissions := fun ps =>
  mem_apply_range'
    (fun oldp => f (unwrap pdefault oldp))
    range ps.

Lemma mem_apply_range'_defined_isSome {X} (map:gmap Z X) (fn:option X -> X) :
  forall range, is_Some (mem_apply_range' (fun x => Some (fn x)) range map).
Proof.
  intros range; destruct range as [z sz].
  generalize dependent z.
  generalize dependent map.
  unfold mem_apply_range'; simpl.
  induction sz as [|sz IHsz]; intros map z; simpl in *.
  - exists map; auto.
  - destruct (IHsz (<[z := fn (map !! z)]> map) (z+1)%Z) as [res H].
    rewrite H; simpl.
    exists res.
    reflexivity.
Qed.

Definition mem_apply_range'_defined {X} (fn:option X -> X) range
  : gmap Z X -> gmap Z X := fun map =>
  is_Some_proj (mem_apply_range'_defined_isSome map fn range).

Lemma is_Some_proj_extract {X} (ox:option X) (sx:is_Some ox) y :
  is_Some_proj sx = y -> ox = Some y.
Proof.
  destruct ox; simpl in *.
  - intro; subst; reflexivity.
  - inversion sx as [? H]; inversion H.
Qed.

Lemma mem_apply_range'_defined_spec {X} fn r z :
  forall (map newmap: gmap Z X),
  (mem_apply_range'_defined fn r map = newmap) ->
  if (decide (range'_contains r z))
    then exists val, newmap !! z = Some val /\ fn (map !! z) = val
    else newmap !! z = map !! z.
Proof.
  intros map newmap MemForeach.
  unfold mem_apply_range'_defined in MemForeach.
  pose proof (is_Some_proj_extract _ _ _ MemForeach) as Foreach.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec.
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [x [Mapz Appfn]].
    exists x; split; auto. injection Appfn; tauto.
  - assumption.
Qed.

(** CORE SEMANTICS *)

Definition IsTag t : Tprop (item) := fun it => it.(itag) = t.
Global Instance IsTag_dec t it : Decision (IsTag t it).
Proof. rewrite /IsTag. solve_decision. Qed.

Definition HasRootTag t : Tprop (tbranch item) := fun br => IsTag t (root br).
Global Instance HasRootTag_dec t it : Decision (HasRootTag t it).
Proof. rewrite /HasRootTag. solve_decision. Qed.

Definition HasStrictChildTag t' : Tprop (tbranch item) := exists_strict_child (IsTag t').
Global Instance HasChildTag_dec t' tr : Decision (HasStrictChildTag t' tr).
Proof. rewrite /HasStrictChildTag. solve_decision. Qed.

Definition StrictParentChildIn t t' : Tprop (tree item)
  := every_subtree (fun br => (IsTag t (root br)) -> (HasStrictChildTag t' br)).
Global Instance StrictParentChildIn_dec t t' tr : Decision (StrictParentChildIn t t' tr).
Proof. rewrite /StrictParentChildIn. solve_decision. Qed.

Definition ParentChildIn t t' : Tprop (tree item)
  := fun tr => t = t' \/ StrictParentChildIn t t' tr.
Global Instance ParentChildIn_dec t t' tr : Decision (ParentChildIn t t' tr).
Proof. rewrite /ParentChildIn. solve_decision. Qed.

Definition rel_dec (tr:tree item) := fun t t' =>
  match decide (ParentChildIn t t' tr), decide (ParentChildIn t' t tr) with
  | left _, left _ => This
  | left _, right _ => Parent
  | right _, left _ => Child
  | right _, right _ => Uncle
  end.

Implicit Type (kind:access_kind) (rel:rel_pos).
Implicit Type (it:item).
Implicit Type (prot:option protector).

(* Tells if an access requires you to initialize the permission afterwards (child accesses) *)
Definition requires_init (rel:rel_pos)
  : perm_init :=
  match rel with
  | This | Child => PermInit
  | Parent | Uncle => PermLazy
  end.

(* State machine without protector UB *)
Definition apply_access_perm_inner (kind:access_kind) (rel:rel_pos) (isprot:bool)
  : app permission := fun perm =>
  match kind, rel with
  | AccessRead, (Parent | Uncle) =>
      match perm with
      | Reserved TyFrz ResActivable => if isprot then Some $ Reserved TyFrz ResConflicted else Some $ Reserved TyFrz ResActivable
      | Reserved InteriorMut ResActivable => if isprot then Some $ Reserved InteriorMut ResConflicted else Some $ Reserved InteriorMut ResActivable
      | Reserved TyFrz ResConflicted | Reserved InteriorMut ResConflicted => Some perm
      | Active => if isprot then
        (* This is just a trick for commutativity of read operations.
           Protector should get triggered anyway *)
        Some Disabled else Some Frozen
      | Frozen | Disabled  => Some perm
      end
  | AccessWrite, (Parent | Uncle) =>
      match perm with
      | Reserved InteriorMut ResActivable => if isprot then Some Disabled else Some $ Reserved InteriorMut ResActivable
      | Reserved InteriorMut ResConflicted => if isprot then Some Disabled else Some $ Reserved InteriorMut ResConflicted
      | Disabled => Some Disabled
      | _ => Some Disabled
      end
  | AccessRead, (This | Child) =>
      match perm with
      | Disabled => None
      | _ => Some perm
      end
  | AccessWrite, (This | Child) =>
      match perm with
      | Reserved TyFrz ResConflicted => if isprot then None else Some Active
      | Reserved InteriorMut ResConflicted => if isprot then None else Some Active
      | Reserved TyFrz ResActivable | Reserved InteriorMut ResActivable | Active => Some Active
      | _ => None
      end
  end.

Definition call_is_active c cids := (c ∈ cids).
Global Instance call_is_active_dec c cids : Decision (call_is_active c cids).
Proof. rewrite /call_is_active. solve_decision. Qed.

Definition call_of_protector (prot:option protector) :=
  match prot with
  | Some (mkProtector _ c) => Some c
  | _ => None
  end.

Definition protector_is_for_call c prot := call_of_protector prot = Some c.
Global Instance protector_is_for_call_dec c prot : Decision (protector_is_for_call c prot).
Proof. rewrite /protector_is_for_call /call_of_protector. case_match; [case_match|]; solve_decision. Qed.

Definition protector_compatible_call c prot := is_Some prot -> protector_is_for_call c prot.

Definition protector_is_active prot cids :=
  exists c, protector_is_for_call c prot /\ call_is_active c cids.

Definition witness_protector_is_active prot cids :=
  match prot with
  | Some (mkProtector _ c) => call_is_active c cids
  | _ => False
  end.

Global Instance witness_protector_is_active_dec prot cids :
  Decision (witness_protector_is_active prot cids).
Proof.
  rewrite /witness_protector_is_active.
  case_match; [case_match|]; solve_decision.
Qed.

Lemma protector_is_active_matches_witness prot cids :
  witness_protector_is_active prot cids <-> protector_is_active prot cids.
Proof.
  rewrite /protector_is_active /witness_protector_is_active /protector_is_for_call /call_of_protector.
  split; intro Hyp.
  - destruct prot as [p|]; [destruct p as [prot call]|].
    * exists call; auto.
    * inversion Hyp.
  - destruct Hyp as [c [IsProt IsActive]].
    destruct prot as [p|]; [destruct p as [prot call]|].
    * injection IsProt; intros; subst; assumption.
    * inversion IsProt.
Qed.

Global Instance protector_is_active_dec prot cids :
  Decision (protector_is_active prot cids).
Proof.
  eapply decision_equiv; [eapply protector_is_active_matches_witness|].
  solve_decision.
Qed.

Definition protector_is_strong prot :=
  match prot with
  | Some (mkProtector weak _) => weak = ProtStrong
  | _ => False
  end.
Global Instance protector_is_strong_dec prot : Decision (protector_is_strong prot).
Proof. rewrite /protector_is_strong. try repeat case_match; solve_decision. Qed.

(* State machine including protector UB *)
Definition apply_access_perm kind rel (isprot:bool) (protector_relevant:bool)
  : app lazy_permission := fun operm =>
  let old := operm.(perm) in
  new ← apply_access_perm_inner kind rel isprot old;
  validated ← if operm.(initialized) then (
    (* only if the permission is initialized do we possibly trigger protector UB *)
    if isprot && protector_relevant && bool_decide (new = Disabled) then (
        None
    ) else Some new
  ) else Some new;
  Some $ mkPerm
    (most_init operm.(initialized) (requires_init rel)) (* can only become more initialized *)
    validated.

Definition item_apply_access kind strong cids rel range
  : app item := fun it =>
  let oldps := it.(iperm) in
  let protected := bool_decide (protector_is_active it.(iprot) cids) in
  let protector_relevant := bool_decide (strong = ProtStrong \/ protector_is_strong it.(iprot)) in
  newps ← permissions_apply_range' (mkPerm PermLazy it.(initp)) range
    (apply_access_perm kind rel protected protector_relevant) oldps;
  Some $ mkItem it.(itag) it.(iprot) it.(initp) newps.

(* FIXME: share code *)
Definition tree_apply_access
  (fn:call_id_set -> rel_pos -> (Z * nat) -> app item)
  cids (access_tag:tag) range (tr:tree item)
  : option (tree item) :=
  let app : item -> option item := fun it => (
    fn cids (rel_dec tr access_tag it.(itag)) range it
  ) in
  join_nodes (map_nodes app tr).

Definition tree_apply_access_nonchildren_only
  (fn:call_id_set -> rel_pos -> (Z * nat) -> app item)
  cids (access_tag:tag) range (tr:tree item)
  : option (tree item) :=
  let app : item -> option item := fun it => (
    (* FIXME This does not skip children *)
    fn cids (rel_dec tr access_tag it.(itag)) range it
  ) in
  join_nodes (map_nodes app tr).

Definition init_perms perm
  : permissions := mem_apply_range'_defined (fun _ => mkPerm PermLazy perm) (0%Z, O) ∅.

Definition init_tree t
  : tree item := branch (mkItem t None Active (init_perms Active)) empty empty.

Definition extend_trees t blk
  : trees -> trees := fun ts =>
  <[blk := init_tree t]>ts.

(* Perform the access check on a block of continuous memory.
 * This implements Tree::before_memory_{read,write,deallocation}. *)
Definition memory_access kind strong cids tg range
  : app (tree item) := fun tr =>
  tree_apply_access (item_apply_access kind strong) cids tg range tr.
Definition memory_access_nonchildren_only kind strong cids tg range
  : app (tree item) := fun tr =>
  tree_apply_access_nonchildren_only (item_apply_access kind strong) cids tg range tr.

Definition memory_deallocate cids t range
  : app (tree item) := fun tr =>
  tree_apply_access (item_apply_access AccessWrite ProtWeak) cids t range tr.

(* Normal reachability definition is not easily destructable, so we're defining it
   manually and proving it's equivalent to the reflexive transitive closuse of one step.
   The witness step needs to be strict otherwise the proof of equivalence will be stuck.
*)

Definition witness_transition p p' : Prop :=
  match p, p' with
  | Reserved m ResActivable, Reserved m' ResConflicted
  => m = m'
  | Reserved _ _, Active
  | Active, Frozen
  | Frozen, Disabled
  => True
  | _, _ => False
  end.

(* FIXME: use builtin rtc *)
Inductive witness_reach p p' : Prop :=
  | witness_reach_refl : p = p' -> witness_reach p p'
  | witness_reach_step p'' : witness_transition p p'' ->  witness_reach p'' p' -> witness_reach p p'
  .

Definition reach p p' : Prop :=
  match p, p' with
  | Reserved InteriorMut ResActivable, (Reserved InteriorMut ResActivable | Reserved InteriorMut ResConflicted | Active | Frozen | Disabled)
  | Reserved TyFrz ResActivable, (Reserved TyFrz ResActivable | Reserved TyFrz ResConflicted | Active | Frozen | Disabled)
  | Reserved InteriorMut ResConflicted, (Reserved InteriorMut ResConflicted | Active | Frozen | Disabled)
  | Reserved TyFrz ResConflicted, (Reserved TyFrz ResConflicted | Active | Frozen | Disabled)
  | Active, (Active | Frozen | Disabled)
  | Frozen, (Frozen | Disabled)
  | Disabled, (Disabled)
  => True
  | _, _ => False
  end.

Definition freeze_like p : Prop :=
  reach Frozen p \/ p = Reserved TyFrz ResConflicted \/ p = Reserved InteriorMut ResConflicted.

(* Now we check that the two definitions are equivalent, so that the clean definition
   acts as a witness for the easy-to-do-case-analysis definition *)

Ltac destruct_permission :=
  match goal with
  | p : permission |- _ => destruct p as [[][]| | |]
  end.

Ltac invert_reach :=
  match goal with
  | H : witness_reach _ _ |- _ =>
    let eql := fresh "Eql" in
    inversion H as [eql|]; clear H;
    try (inversion eql; clear eql)
  end.

Ltac invert_transition :=
  match goal with
  | H : witness_transition _ _ |- _ =>
    let eql := fresh "Eql" in
    inversion H; clear H
  end.

Ltac reach_inversion_strategy :=
  multimatch goal with
  | _ => destruct_permission
  | _ => invert_transition
  | _ => invert_reach
  end.

Lemma reach_complete p p' :
  witness_reach p p' -> reach p p'.
Proof.
  repeat destruct_permission; simpl; intro WReach; try tauto.
  all: do 15 reach_inversion_strategy.
Qed.

Ltac witness_reach_solve :=
  let p := fresh "p" in
  let p' := fresh "p'" in
  let p'' := fresh "p''" in
  match goal with
  | |- witness_reach ?p ?p => apply witness_reach_refl; reflexivity
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ (Reserved TyFrz ResConflicted)); simpl; [tauto|]
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ (Reserved InteriorMut ResConflicted)); simpl; [tauto|]
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ Active); simpl; [tauto|]
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ Frozen); simpl; [tauto|]
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ Disabled); simpl; [tauto|]
  end.

Lemma reach_sound p p' :
  reach p p' -> witness_reach p p'.
Proof.
  destruct p as [[][]| | |], p' as [[][]| | |]; simpl; intro; try tauto.
  all: do 10 witness_reach_solve.
Qed.

Lemma reach_correct p p' :
  reach p p' <-> witness_reach p p'.
Proof.
  split; [apply reach_sound|apply reach_complete].
Qed.

Lemma reach_reflexive p q : p = q -> reach p q.
Proof. rewrite reach_correct. apply witness_reach_refl. Qed.

Lemma reach_transitive p p' p'' : reach p p' -> reach p' p'' -> reach p p''.
Proof.
  repeat rewrite reach_correct.
  intros Reachpp' Reachp'p''.
  induction Reachpp'.
  - subst; tauto.
  - eapply witness_reach_step; [eassumption|auto].
Qed.

(** CONSISTENCY *)

(* General *)

Lemma not_is_negb (b:bool) :
  b = false <-> ~b = true.
Proof. split; intro. 1: subst; auto. apply not_true_is_false; auto. Qed.

Lemma IsTag_reverse it it' :
  IsTag it.(itag) it' -> IsTag it'.(itag) it.
Proof. unfold IsTag. auto. Qed.

Lemma apply_access_idempotent
  {kind rel} (isprot isstrong isprot' isstrong':bool) {perm perm'}
  (ProtIncr : if isprot then True else isprot' = false)
  (StongIncr : if isstrong then True else isstrong' = false)
  (Acc1 : apply_access_perm kind rel isprot isstrong perm = Some perm')
  (Witness : exists x, x = (kind, rel, perm, perm', isprot, isstrong, isprot', isstrong'))
  : apply_access_perm kind rel isprot' isstrong' perm' = Some perm'.
Proof.
  destruct perm as [init perm]; destruct perm' as [init' perm'].
  unfold apply_access_perm in *.
  (* This is going to be a big case analysis, we essentially have to destruct
     everything. Still, let's try to do it in a smart order otherwise it'll generate
     upwards of 2000 cases *)
  destruct kind, rel.
  all: destruct isprot, isstrong.
  all: destruct init, perm as [[][]| | |]; simpl in *; inversion Acc1; subst.
  all: simpl; try auto.
  all: destruct isprot'; simpl; try auto.
  all: destruct isstrong'; simpl; try auto.
Qed.

Definition tree_contains tg tr
  : Prop :=
  exists_node (IsTag tg) tr.

Definition tree_unique tg it tr
  : Prop :=
  every_node (fun it' => IsTag tg it' -> it' = it) tr.

Definition trees_at_block prop trs blk
  : Prop :=
  match trs !! blk with
  | None => False
  | Some tr => prop tr
  end.

Definition trees_contain tg trs blk :=
  trees_at_block (tree_contains tg) trs blk.

Definition trees_unique tg trs blk it :=
  trees_at_block (tree_unique tg it) trs blk.

Definition ParentChildInBlk tg tg' trs blk :=
  trees_at_block (ParentChildIn tg tg') trs blk.

Definition app_preserves_metadata app : Prop :=
  (forall it cids rel range it', app cids rel range it = Some it' ->
    itag it = itag it' /\ iprot it = iprot it' /\ initp it = initp it').

(* FIXME: order of args *)

(** Reborrow *)

Definition create_new_item tg perm :=
  {| itag:=tg; iprot:=perm.(new_protector); initp:=perm.(initial_state); iperm:=∅ |}.

Definition create_child cids (oldt:tag) (newt:tag) (newp:newperm)
  : app (tree item) := fun tr =>
  let it := create_new_item newt newp in
  Some $ insert_child_at tr it (IsTag oldt).

Definition item_lazy_perm_at_loc it (l:loc')
  : lazy_permission :=
  let op := iperm it !! l in
  unwrap {| initialized := PermLazy; perm := initp it |} op.

Definition item_perm_at_loc it z
  : permission :=
  perm (item_lazy_perm_at_loc it z).

Definition every_tagged t (P:Tprop item) tr
  : Prop :=
  every_node (fun it => IsTag t it -> P it) tr.

(* FIXME: gmap::partial_alter ? *)
Definition apply_within_trees (fn:app (tree item)) blk
  : app trees := fun trs =>
  oldtr ← trs !! blk;
  newtr ← fn oldtr;
  Some $ <[blk := newtr]> trs.

Definition item_fresh_call cid it :=
  ~protector_is_for_call cid (iprot it).

Definition tree_fresh_call cid tr :=
  every_node (item_fresh_call cid) tr.

Definition trees_fresh_call cid trs blk :=
  forall tr,
  trs !! blk = Some tr ->
  tree_fresh_call cid tr.

(* FIXME: this can only do strong accesses *)
Inductive bor_local_step tr cids
  : bor_local_event -> tree item -> call_id_set -> Prop :=
  | AccessLIS kind tr' range tg
    (EXISTS_TAG: tree_contains tg tr)
    (ACC: memory_access kind ProtStrong cids tg range tr = Some tr') :
    bor_local_step
      tr cids
      (AccessBLEvt kind tg range)
      tr' cids
  | InitCallLIS cid
    (INACTIVE_CID : ~cid ∈ cids)
    (FRESH_CID : tree_fresh_call cid tr) :
    bor_local_step
      tr cids
      (InitCallBLEvt cid)
      tr ({[cid]} ∪ cids)
  | EndCallLIS cid
    (EL: cid ∈ cids) :
    bor_local_step
      tr cids
      (EndCallBLEvt cid)
      tr (cids ∖ {[cid]})
  | RetagLIS tr' tgp tg newp (cid : call_id)
    (EL: cid ∈ cids)
    (EXISTS_PARENT: tree_contains tgp tr)
    (FRESH_CHILD: ~tree_contains tg tr)
    (COMPAT_CID: protector_compatible_call cid (new_protector newp))
    (RETAG_EFFECT: create_child cids tgp tg newp tr = Some tr') :
    bor_local_step
      tr cids
      (RetagBLEvt tgp tg newp cid)
      tr' cids
  .

Record seq_invariant := MkRecord {
  seq_inv : tree item -> call_id_set -> Prop;
}.
Inductive bor_local_seq (invariant : seq_invariant) tr cids
  : list bor_local_event -> tree item -> call_id_set -> Prop :=
  | bor_nil
    (INV : invariant.(seq_inv) tr cids) :
    bor_local_seq invariant
      tr cids
      []
      tr cids
  | bor_cons evt tr' cids' evts tr'' cids''
    (INV : invariant.(seq_inv) tr cids)
    (HEAD : bor_local_step tr cids evt tr' cids')
    (REST : bor_local_seq invariant tr' cids' evts tr'' cids'') :
    bor_local_seq invariant
      tr cids
      (evt :: evts)
      tr'' cids''.

(* Traverse the entire tree and get for each tag protected by cid its currently initialized locations.
   Those are all the locations that we'll do a read access through *)
Definition tree_get_all_protected_tags_initialized_locs (cid : nat) (tr : tree item)
  : list (tag * list Z) :=
  fold_nodes [] (fun it lacc racc =>
    (it.(itag), mem_enumerate_sat (fun (p:lazy_permission) =>
      (* filter out the unprotected and protected by another call.
         We could also do this outside of the function, which might in fact be
         easier to reason about eventually *)
      if decide (Some cid = option_map call it.(iprot)) then
        (* filter out the uninitialized *)
        if initialized p then true
        else false
      else false) it.(iperm))
    :: lacc
    ++ racc
  ) tr.

Definition tree_read_all_protected_initialized (cids : call_id_set) (cid : nat)
    : app (tree item) := fun tr =>
    (* read one loc by doing a memory_access *)
    let reader_loc (tg : tag) (loc : Z) : app (tree item) := fun tr =>
      memory_access_nonchildren_only AccessRead ProtStrong cids tg (loc, 1) tr in
    (* read several locs of the same tag, propagate failures *)
    let reader_locs (tg : tag) (locs : list Z) : app (tree item) := fun tr =>
      fold_left (fun (tr:option (tree item)) loc => tr ← tr; reader_loc tg loc tr) locs (Some tr) in
    (* get all initialized locs as defined above, these are what we need to read *)
    let init_locs := tree_get_all_protected_tags_initialized_locs cid tr in
    (* finally we can combine this all *)
    fold_left (fun (tr:option (tree item)) '(tg, init_locs) => tr ← tr; reader_locs tg init_locs tr) init_locs (Some tr).

(* FIXME: IMPORTANT: don't make the access visible to children ! *)
(* Finally we read all protected initialized locations on the entire trees by folding it
   for each tree separately.
   NOTE: be careful about how other properties assume the uniqueness of tags intra- and inter- trees,
   because this may have a weird behavior if you have the same tag across two trees and e.g. only one
   of them is protected, which shouldn't happen but isn't impossible by construction. *)
Definition trees_read_all_protected_initialized (cids : call_id_set) (cid : nat) (trs : trees) : option trees :=
  gmap_fold (option trees) (fun k (tr : tree item) (trs : option trees) =>
    trs ← trs;
    apply_within_trees (tree_read_all_protected_initialized cids cid) k trs
  ) (Some trs) gmap_empty.


Inductive bor_step (trs : trees) (cids : call_id_set) (nxtp : nat) (nxtc : call_id)
  : event -> trees -> call_id_set -> nat -> call_id -> Prop :=
  | AllocIS (x : loc) (sz : nat)
    (FRESH : trs !! x.1 = None) :
    bor_step
      trs cids nxtp nxtc
      (AllocEvt x.1 (Tag nxtp) (x.2, sz))
      (extend_trees (Tag nxtp) x.1 trs) cids (S nxtp) nxtc
  | CopyIS trs' (alloc : block) range tg val
    (* Successful read access *)
    (EXISTS_TAG: trees_contain tg trs alloc)
    (ACC: apply_within_trees (memory_access AccessRead ProtStrong cids tg range) alloc trs = Some trs') :
    bor_step
      trs cids nxtp nxtc
      (CopyEvt alloc tg range val)
      trs' cids nxtp nxtc
  | FailedCopyIS (alloc : block) range tg
    (* Unsuccessful read access just returns poison instead of causing UB *)
    (EXISTS_TAG : trees_contain tg trs alloc)
    (ACC : apply_within_trees (memory_access AccessRead ProtStrong cids tg range) alloc trs = None) :
    bor_step
      trs cids nxtp nxtc
      (FailedCopyEvt alloc tg range)
      trs cids nxtp nxtc
  | WriteIS trs' (alloc : block) range tg val
    (* Successful write access *)
    (EXISTS_TAG: trees_contain tg trs alloc)
    (ACC: apply_within_trees (memory_access AccessWrite ProtStrong cids tg range) alloc trs = Some trs') :
    bor_step
      trs cids nxtp nxtc
      (WriteEvt alloc tg range val)
      trs' cids nxtp nxtc
  | RetagIS trs' trs'' parentt (alloc : block) range (newp : newperm) cid
      (* For a retag we require that the parent exists and the introduced tag is fresh, then we do a read access.
         NOTE: create_child does not read, it only inserts, so the read needs to be explicitly added.
               We want to do the read *after* the insertion so that it properly initializes the locations of the range *)
    (EL: cid ∈ cids)
    (EXISTS_TAG: trees_contain parentt trs alloc)
    (SAME_CID : is_Some newp.(new_protector) -> protector_is_for_call cid newp.(new_protector))
    (FRESH_CHILD: ~trees_contain (Tag nxtp) trs alloc)
    (RETAG_EFFECT: apply_within_trees (create_child cids parentt (Tag nxtp) newp) alloc trs = Some trs')
    (READ_ON_REBOR: apply_within_trees (memory_access AccessRead ProtStrong cids (Tag nxtp) range) alloc trs' = Some trs'') :
    bor_step
      trs cids nxtp nxtc
      (RetagEvt alloc parentt (Tag nxtp) newp cid)
      trs'' cids (S nxtp) nxtc
  | DeallocIS trs' (alloc : block) (tg : tag) range
    (EXISTS_TAG: trees_contain tg trs alloc)
    (ACC: apply_within_trees (memory_deallocate cids tg range) alloc trs = Some trs') :
    (* FIXME: should we actually remove the tree ? *)
    bor_step
      trs cids nxtp nxtc
      (DeallocEvt alloc tg range)
      trs' cids nxtp nxtc
  | InitCallIS :
    bor_step
      trs cids nxtp nxtc
      (InitCallEvt nxtc)
      trs ({[nxtc]} ∪ cids) nxtp (S nxtc)
  | EndCallIS c trs'
      (* Don't forget the implicit read on function exit through all initialized locations *)
    (EL: c ∈ cids)
    (READ_ON_UNPROT : trees_read_all_protected_initialized cids c trs = Some trs') :
    bor_step
      trs cids nxtp nxtc
      (EndCallEvt c)
      trs (cids ∖ {[c]}) nxtp nxtc
  .



