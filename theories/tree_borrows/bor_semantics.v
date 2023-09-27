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

Fixpoint mem_foreach {X} (fn:option X -> option X) z sz
  {struct sz} : app (gmap loc' X) := fun map =>
  match sz with
  | O => Some map
  | S sz' =>
      new ← fn (map !! z);
      newmap ← mem_foreach fn (z + 1)%Z sz' map;
      Some (<[z := new]>newmap)
  end.

Definition range'_foreach {X} (fn:option X -> option X) (r:range') : app (gmap loc' X) := mem_foreach fn r.1 r.2.

Lemma range'_foreach_spec {X} fn r z' :
  forall (map newmap: gmap loc' X),
  (range'_foreach fn r map = Some newmap) ->
  if (decide (range'_contains r z'))
    then exists val, newmap !! z' = Some val /\ fn (map !! z') = Some val
    else newmap !! z' = map !! z'.
Proof.
  unfold range'_foreach.
  destruct r as [z sz].
  generalize dependent z'.
  generalize dependent z.
  induction sz; intros z z' map newmap MemForeach.
  - unfold mem_foreach in MemForeach. injection MemForeach; intro; subst.
    destruct (decide (range'_contains (z, 0) z')) as [Contains | NotContains]; auto.
    unfold range'_contains in Contains; simpl in Contains. lia.
  (* Case 1: the item is at the beginning of the range.
     -> it will be unchanged by the aux function and written by the current one *)
  - destruct (decide (z = z')) as [Eql | Neq].
    + subst. assert (range'_contains (z', S sz) z') as ContainsS by (unfold range'_contains; simpl; lia).
      decide (decide (range'_contains (z', S sz) z')) with ContainsS.
      simpl in MemForeach.
      destruct (fn (map !! z')); simpl in *; [|inversion MemForeach].
      destruct (mem_foreach fn (z' + 1) sz map) eqn:Rec; [|inversion MemForeach]; simpl in *.
      injection MemForeach; intro; subst.
      exists x; split; auto; apply lookup_insert.
  (* Case 2: the item is in the middle of the range or completely outside.
     -> the map we get from the aux call is not altered on the location that matters *)
    + simpl in MemForeach.
      destruct (fn (map !! z)) eqn:Fn; simpl in *; [|inversion MemForeach].
      destruct (mem_foreach fn (z + 1) sz map) eqn:Rec; simpl in *; [|inversion MemForeach].
      specialize IHsz with (z + 1)%Z z' map g.
      * destruct (decide (range'_contains ((z + 1)%Z, sz) z')) as [Contains' | NotContains'].
        all: destruct (decide (range'_contains (z, S sz) z')) as [ContainsS' | NotContainsS'].
        (* good case *)
        1,4: injection MemForeach; intro; subst; rewrite lookup_insert_ne; auto.
        (* bad range *)
        1: exfalso; unfold range'_contains in *; simpl in *; lia.
        (* bad range, this time it suggests z = z' *)
        1: exfalso; apply Neq. apply (range'_contains_excludes_equal (z, sz) z' ContainsS' NotContains').
Qed.

Definition permissions_foreach (pdefault:lazy_permission) range (f:app lazy_permission)
  : app permissions := fun ps =>
  range'_foreach
    (fun oldp => f (unwrap pdefault oldp))
    range ps.

Lemma mem_foreach_defined_isSome {X} (map:gmap Z X) (fn:option X -> X) :
  forall range, is_Some (range'_foreach (fun x => Some (fn x)) range map).
Proof.
  intros range; destruct range as [z sz].
  generalize dependent z.
  unfold range'_foreach; simpl.
  induction sz; intro z; simpl in *.
  - exists map; auto.
  - destruct (IHsz (z+1)%Z) as [res].
    rewrite H; simpl.
    exists (<[z:=fn (map !! z)]> res).
    reflexivity.
Qed.

Definition mem_foreach_defined {X} (fn:option X -> X) range
  : gmap Z X -> gmap Z X := fun map =>
  is_Some_proj (mem_foreach_defined_isSome map fn range).

Lemma is_Some_proj_extract {X} (ox:option X) (sx:is_Some ox) y :
  is_Some_proj sx = y -> ox = Some y.
Proof.
  destruct ox; simpl in *.
  - intro; subst; reflexivity.
  - inversion sx; inversion H.
Qed.

Lemma mem_foreach_defined_spec {X} fn r z :
  forall (map newmap: gmap Z X),
  (mem_foreach_defined fn r map = newmap) ->
  if (decide (range'_contains r z))
    then exists val, newmap !! z = Some val /\ fn (map !! z) = val
    else newmap !! z = map !! z.
Proof.
  intros map newmap MemForeach.
  unfold mem_foreach_defined in MemForeach.
  pose proof (is_Some_proj_extract _ _ _ MemForeach) as Foreach.
  pose proof (range'_foreach_spec _ _ z _ _ Foreach) as Spec.
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [x [Mapz Appfn]].
    exists x; split; auto. injection Appfn; tauto.
  - assumption.
Qed.

(** CORE SEMANTICS *)

Inductive access_rel := AccessForeign | AccessChild.
Global Instance access_rel_eq_dec : EqDecision access_rel.
Proof. solve_decision. Qed.

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

Definition RelPosIn t t' (tr:tree item) : access_rel :=
  if decide (ParentChildIn t t' tr) then AccessChild else AccessForeign.

Definition rel_dec (tr:tree item) : Type := forall t t', {ParentChildIn t t' tr} + {~ParentChildIn t t' tr}.
Definition naive_rel_dec (tr:tree item) : rel_dec tr := fun t t' => decide (ParentChildIn t t' tr).

Implicit Type (kind:access_kind) (rel:access_rel).
Implicit Type (it:item).
Implicit Type (prot:option protector).

Definition requires_init (rel:access_rel)
  : perm_init :=
  match rel with
  | AccessChild => PermInit
  | AccessForeign => PermLazy
  end.

Definition apply_access_perm_inner (kind:access_kind) (rel:access_rel) (isprot:bool)
  : app permission := fun perm =>
  match kind, rel with
  | AccessRead, AccessForeign =>
      match perm with
      | Reserved => if isprot then Some ReservedConfl else Some Reserved
      | ReservedMut => if isprot then Some ReservedConflMut else Some ReservedMut
      | ReservedConfl | ReservedConflMut => Some perm
      | Active => if isprot then
        (* This is just a trick for commutativity of read operations.
           Protector should get triggered anyway *)
        Some Disabled else Some Frozen
      | Frozen | Disabled  => Some perm
      end
  | AccessWrite, AccessForeign =>
      match perm with
      | ReservedMut => if isprot then Some Disabled else Some ReservedMut
      | ReservedConflMut => if isprot then Some Disabled else Some ReservedConflMut
      | Disabled => Some Disabled
      | _ => Some Disabled
      end
  | AccessRead, AccessChild =>
      match perm with
      | Disabled => None
      | _ => Some perm
      end
  | AccessWrite, AccessChild =>
      match perm with
      | ReservedConfl => if isprot then None else Some Active
      | ReservedConflMut => if isprot then None else Some Active
      | Reserved | ReservedMut | Active => Some Active
      | _ => None
      end
  end.

Definition call_is_active c cids := (c ∈ cids).
Global Instance call_is_active_dec c cids : Decision (call_is_active c cids).
Proof. rewrite /call_is_active. solve_decision. Qed.

Definition call_of_protector prot :=
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
  - destruct prot; [destruct p|].
    * exists call; auto.
    * inversion Hyp.
  - destruct Hyp as [c [IsProt IsActive]].
    destruct prot; [destruct p|].
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

Definition apply_access_perm kind rel (isprot:bool) (protector_relevant:bool)
  : app lazy_permission := fun operm =>
  let old := operm.(perm) in
  new ← apply_access_perm_inner kind rel isprot old;
  validated ← if operm.(initialized) then (
    if isprot && protector_relevant && bool_decide (new = Disabled) then (
        None
    ) else Some new
  ) else Some new;
  Some $ mkPerm (most_init operm.(initialized) (requires_init rel)) validated.

Definition item_apply_access kind strong cids rel range
  : app item := fun it =>
  let oldps := it.(iperm) in
  let protected := bool_decide (protector_is_active it.(iprot) cids) in
  let protector_relevant := bool_decide (strong = ProtStrong \/ protector_is_strong it.(iprot)) in
  newps ← permissions_foreach (mkPerm PermLazy it.(initp)) range (apply_access_perm kind rel protected protector_relevant) oldps;
  Some $ mkItem it.(itag) it.(iprot) it.(initp) newps.

(* FIXME: share code *)
Definition tree_apply_access
  (fn:call_id_set -> access_rel -> (Z * nat) -> app item)
  cids (access_tag:tag) range (tr:tree item) (dyn_rel:rel_dec tr)
  : option (tree item) :=
  let app : item -> option item := fun it => (
    fn cids (if dyn_rel it.(itag) access_tag then AccessChild else AccessForeign) range it
  ) in
  join_nodes (map_nodes app tr).

Definition init_perms perm
  : permissions := mem_foreach_defined (fun _ => mkPerm PermLazy perm) (0%Z, O) ∅.

Definition init_tree t
  : tree item := branch (mkItem t None Active (init_perms Active)) empty empty.

Definition extend_trees t blk
  : trees -> trees := fun ts =>
  <[blk := init_tree t]>ts.

(* Perform the access check on a block of continuous memory.
 * This implements Tree::before_memory_{read,write,deallocation}. *)
Definition memory_access kind strong cids tg range
  : app (tree item) := fun tr =>
  tree_apply_access (item_apply_access kind strong) cids tg range tr (naive_rel_dec tr).

Definition memory_deallocate cids t range
  : app (tree item) := fun tr =>
  Some tr.

Definition witness_transition p p' : Prop :=
  match p, p' with
  | Reserved, ReservedConfl
  | ReservedMut, ReservedConflMut
  | ReservedConfl, Active
  | ReservedConflMut, Active
  | Active, Frozen
  | Frozen, Disabled
  => True
  | _, _ => False
  end.

Inductive witness_reach p p' : Prop :=
  | witness_reach_refl : p = p' -> witness_reach p p'
  | witness_reach_step p'' : witness_transition p p'' ->  witness_reach p'' p' -> witness_reach p p'
  .

Definition reach p p' : Prop :=
  match p, p' with
  | ReservedMut, (ReservedMut | ReservedConflMut | Active | Frozen | Disabled)
  | Reserved, (Reserved | ReservedConfl | Active | Frozen | Disabled)
  | ReservedConflMut, (ReservedConflMut | Active | Frozen | Disabled)
  | ReservedConfl, (ReservedConfl | Active | Frozen | Disabled)
  | Active, (Active | Frozen | Disabled)
  | Frozen, (Frozen | Disabled)
  | Disabled, (Disabled)
  => True
  | _, _ => False
  end.

Ltac witness_reach_invert :=
  match goal with
  | H : witness_reach _ _ |- False =>
    let perm := fresh "perm" in
    let eql := fresh "Eql" in
    let trans := fresh "Trans" in
    let reach := fresh "Reach" in
    inversion H as [eql|perm trans reach]; [inversion eql|destruct perm; try inversion trans]
  end.

Lemma reach_complete p p' :
  witness_reach p p' -> reach p p'.
Proof.
  destruct p, p'; simpl; intro; try tauto.
  all: do 10 witness_reach_invert.
Qed.

Ltac witness_reach_solve :=
  let p := fresh "p" in
  let p' := fresh "p'" in
  let p'' := fresh "p''" in
  match goal with
  | |- witness_reach ?p ?p => apply witness_reach_refl; reflexivity
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ ReservedConfl); simpl; [tauto|]
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ ReservedConflMut); simpl; [tauto|]
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ Active); simpl; [tauto|]
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ Frozen); simpl; [tauto|]
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ Disabled); simpl; [tauto|]
  end.

Lemma reach_sound p p' :
  reach p p' -> witness_reach p p'.
Proof.
  destruct p, p'; simpl; intro; try tauto.
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
  destruct init; destruct init'; destruct perm; destruct perm'.
  all: destruct kind; destruct rel.
  all: try (inversion FirstPass; done).
  all: destruct isprot; [|subst]; try destruct isprot'.
  all: try (inversion FirstPass; done).
  all: destruct isstrong; [|subst]; try destruct isstrong'.
  all: inversion Acc1.
  all: unfold apply_access_perm; simpl; done.
Qed.

Definition tree_contains tg tr
  : Prop :=
  exists_node (IsTag tg) tr.

Definition tree_unique tg it tr
  : Prop :=
  every_node (fun it' => IsTag tg it' -> it' = it) tr.

(*
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
*)

Definition app_preserves_tag app : Prop :=
  (forall it cids rel range it', app cids rel range it = Some it' -> itag it = itag it').

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

(* FIXME: Check this much more thoroughly *)
(*
Inductive bor_step trs cids (nxtp:nat) (nxtc:call_id)
  : event -> trees -> call_id_set -> nat -> call_id -> Prop :=
  | AllocIS (x:loc) ptr
    (FRESH : trs !! x.1 = None) :
    (* Tagged nxtp is the first borrow of the variable x,
       used when accessing x directly (not through another pointer) *)
    (* FIXME: should we check that the block is absent from the trees ? *)
    bor_step
      trs cids nxtp nxtc
      (AllocEvt x (Tag nxtp) ptr)
      (extend_trees (Tag nxtp) x.1 (x.2, sizeof ptr) trs) cids (S nxtp) nxtc
  | ReadIS trs' (x:loc) tg ptr val
    (EXISTS_TAG: trees_contain tg trs x.1)
    (ACC: apply_within_trees (memory_read cids tg (x.2, sizeof ptr)) x.1 trs = Some trs') :
    bor_step
      trs cids nxtp nxtc
      (ReadEvt x tg ptr val)
      trs' cids nxtp nxtc
  | WriteIS trs' (x:loc) tg ptr val
    (EXISTS_TAG: trees_contain tg trs x.1)
    (ACC: apply_within_trees (memory_write cids tg (x.2, sizeof ptr)) x.1 trs = Some trs') :
    bor_step
      trs cids nxtp nxtc
      (WriteEvt x tg ptr val)
      trs' cids nxtp nxtc
  | DeallocIS trs' (x:loc) tg ptr
    (EXISTS_TAG: trees_contain tg trs x.1)
    (ACC: apply_within_trees (memory_deallocate cids tg (x.2, sizeof ptr)) x.1 trs = Some trs') :
    (* FIXME: remove the tree ? *)
    bor_step
      trs cids nxtp nxtc
      (DeallocEvt x tg ptr)
      trs' cids nxtp nxtc
  | InitCallIS :
    bor_step
      trs cids nxtp nxtc
      (InitCallEvt nxtc)
      trs ({[nxtc]} ∪ cids) nxtp (S nxtc)
  | EndCallIS c
    (EL: c ∈ cids) :
    bor_step
      trs cids nxtp nxtc
      (EndCallEvt c)
      trs (cids ∖ {[c]}) nxtp nxtc
  | RetagIS trs' parentt (x:loc) (ptr:pointer) (rtk:retag_kind) newp c
    (EL: c ∈ cids)
    (EXISTS_TAG: trees_contain parentt trs x.1)
    (FRESH_CHILD: ~trees_contain (Tag nxtp) trs x.1)
    (NEW_PERM: reborrow_perm (kindof ptr) rtk c = Some newp)
    (RETAG_EFFECT: apply_within_trees (create_child cids parentt (Tag nxtp) newp) x.1 trs = Some trs') :
    bor_step
      trs cids nxtp nxtc
      (RetagEvt x parentt (Tag nxtp) ptr rtk c)
      trs' cids (S nxtp) nxtc
  .
*)
