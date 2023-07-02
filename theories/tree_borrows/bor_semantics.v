(** This file has been adapted from the Stacked Borrows development, available at 
https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From Equations Require Import Equations.
From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Export lang_base notation.
From iris.prelude Require Import options.

(*** TREE BORROWS SEMANTICS ---------------------------------------------***)

Implicit Type (V W X Y:Type).
Implicit Type (c:call_id) (cids:call_id_set).
Implicit Type (blk:block) (n sz:nat) (z:Z) (range:Z * nat).
Implicit Type (trs:trees) (t:tag).

Definition app X : Type := X -> option X.
Definition Tprop X : Type := X -> Prop.

(** General Preliminaries *)

Definition unwrap {X} (default:X)
  : option X -> X :=
  fun o => match o with
  | Some t => t
  | None => default
  end.

Definition option_bind {X Y} (fn:X -> option Y)
  : option X -> option Y :=
  fun ox => x ← ox; fn x.

Definition option_join {X}
  : option (option X) -> option X :=
  fun oox => ox ← oox; ox.

Lemma option_map_compose {X Y Z} (fn:X -> Y) (fn':Y -> Z) :
  forall ox, option_map fn' (option_map fn ox) = option_map (compose fn' fn) ox.
Proof. intro ox. destruct ox; simpl; auto. Qed.

Lemma option_bind_map_join {X Y} (fn:X -> option Y) :
  option_bind fn = compose option_join (option_map fn).
Proof. apply functional_extensionality. intro ox. destruct ox; simpl; auto. Qed.

Definition range_contains range z : Prop :=
  (range.1 ≤ z)%Z /\ (z < range.1 + range.2)%Z.
Global Instance decision_range_contains range z : Decision (range_contains range z).
Proof. solve_decision. Qed.

Lemma range_contains_excludes_equal range z' :
  let '(z, sz) := range in
  range_contains (z, S sz) z' -> ~(range_contains ((z + 1)%Z, sz) z') -> z = z'.
Proof.
  destruct range.
  intros Contains Excludes.
  unfold range_contains in *; simpl in *.
  lia.
Qed.

Fixpoint mem_foreach {X} (fn:option X -> option X) z sz
  {struct sz} : app (gmap Z X) := fun map =>
  match sz with
  | O => Some map
  | S sz' =>
      new ← fn (map !! z);
      newmap ← mem_foreach fn (z + 1)%Z sz' map;
      Some (<[z := new]>newmap)
  end.

Definition range_foreach {X} (fn:option X -> option X) range := mem_foreach fn range.1 range.2.

Lemma range_foreach_spec {X} fn range z' :
  forall (map newmap: gmap Z X),
  (range_foreach fn range map = Some newmap) ->
  if (decide (range_contains range z'))
    then exists val, newmap !! z' = Some val /\ fn (map !! z') = Some val
    else newmap !! z' = map !! z'.
Proof.
  unfold range_foreach.
  destruct range as [z sz].
  generalize dependent z'.
  generalize dependent z.
  induction sz; intros z z' map newmap MemForeach.
  - unfold mem_foreach in MemForeach. injection MemForeach; intro; subst.
    destruct (decide (range_contains (z, 0) z')) as [Contains | NotContains]; auto.
    unfold range_contains in Contains; simpl in Contains. lia.
  (* Case 1: the item is at the beginning of the range.
     -> it will be unchanged by the aux function and written by the current one *)
  - destruct (decide (z = z')) as [Eql | Neq].
    + subst. assert (range_contains (z', S sz) z') as ContainsS by (unfold range_contains; simpl; lia).
      decide (decide (range_contains (z', S sz) z')) with ContainsS.
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
      * destruct (decide (range_contains ((z + 1)%Z, sz) z')) as [Contains' | NotContains'].
        all: destruct (decide (range_contains (z, S sz) z')) as [ContainsS' | NotContainsS'].
        (* good case *)
        1,4: injection MemForeach; intro; subst; rewrite lookup_insert_ne; auto.
        (* bad range *)
        1: exfalso; unfold range_contains in *; simpl in *; lia.
        (* bad range, this time it suggests z = z' *)
        1: exfalso; apply Neq. apply (range_contains_excludes_equal (z, sz) z' ContainsS' NotContains').
Qed.

Definition permissions_foreach (pdefault:lazy_permission) range (f:app lazy_permission)
  : app permissions := fun ps =>
  range_foreach
    (fun oldp => f (unwrap pdefault oldp))
    range ps.

Lemma mem_foreach_defined_isSome {X} (map:gmap Z X) (fn:option X -> X) :
  forall range, is_Some (range_foreach (fun x => Some (fn x)) range map).
Proof.
  intros range; destruct range as [z sz].
  generalize dependent z.
  unfold range_foreach; simpl.
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

(** Tree-specific preliminaries *)

Definition tree_fold {X Y} (unit:Y) (combine:X -> Y -> Y -> Y)
  : tree X -> Y := fix aux tr : Y :=
  match tr with
  | empty => unit
  | branch data sibling child => combine data (aux sibling) (aux child)
  end.

(* FIXME: do things flow better if this is a Fixpoint ? *)
Definition tree_map {X Y} (fn:X -> Y) : tree X -> tree Y := tree_fold empty (compose branch fn).

(* FIXME: Standard name for this ? *)
Definition tree_join {X}
  : tree (option X) -> option (tree X) := fix aux tr {struct tr} : option (tree X) :=
  match tr with
  | empty => Some empty
  | branch data sibling child =>
    data ← data;
    sibling ← aux sibling;
    child ← aux child;
    Some $ branch data sibling child
  end.

Lemma tree_join_join {X} :
  forall (tr:tree (option (option X))),
  option_bind tree_join (tree_join tr) = tree_join (tree_map option_join tr).
Proof.
  induction tr; simpl; auto.
  rewrite <- IHtr1; rewrite <- IHtr2.
  destruct data; simpl; auto.
  destruct o; simpl; auto.
  all: destruct (tree_join tr1); simpl; auto.
  all: destruct (tree_join tr2); simpl; auto.
  destruct (tree_join t); simpl; auto.
Qed.

Lemma tree_join_omap_comm {X Y} (fn:X -> Y) :
  forall (tr:tree (option X)),
  tree_join (tree_map (option_map fn) tr) = option_map (tree_map fn) (tree_join tr).
Proof.
  induction tr; simpl; auto.
  rewrite IHtr1; rewrite IHtr2; simpl.
  destruct data; simpl; auto.
  destruct (tree_join tr1); simpl; auto.
  destruct (tree_join tr2); simpl; auto.
Qed.

Lemma tree_map_compose {W X Y} (fn:W -> X) (fn':X -> Y) :
  forall (tr:tree W),
  tree_map fn' (tree_map fn tr) = tree_map (compose fn' fn) tr.
Proof.
  induction tr; simpl; auto.
  rewrite IHtr1. rewrite IHtr2; reflexivity.
Qed.


Lemma tree_join_delay {X Y} (fn:X -> option Y) :
  forall (tr:tree (option X)),
  tree_join (tree_map (option_bind fn) tr) = option_bind (compose tree_join (tree_map fn)) (tree_join tr).
Proof.
  intro tr.
  rewrite option_bind_map_join.
  rewrite option_bind_map_join.
  rewrite <- tree_map_compose.
  rewrite <- tree_join_join.
  rewrite tree_join_omap_comm.
  rewrite option_bind_map_join.
  unfold compose.
  rewrite option_map_compose.
  f_equal.
Qed.


Definition tree_Forall {X} (prop:Tprop X) (tr:tree X) := tree_fold True (fun data lt rt => prop data /\ lt /\ rt) tr.
Global Instance tree_Forall_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (tree_Forall prop tr).
Proof. intro. induction tr; solve_decision. Qed.

Definition tree_Exists {X} (prop:Tprop X) (tr:tree X) := tree_fold False (fun data lt rt => prop data \/ lt \/ rt) tr.
Global Instance tree_Exists_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (tree_Exists prop tr).
Proof. intro. induction tr; solve_decision. Qed.

(*
Definition tree_Once {X} (prop:Tprop X)
  : Tprop (tree X) := fix aux tr : Prop :=
  match tr with
  | empty => False
  | branch data sibling child =>
    (prop data /\ tree_Forall (compose not prop) sibling /\ tree_Forall (compose not prop) child)
    \/ (not $ prop data /\ aux sibling /\ tree_Forall (compose not prop) child)
    \/ (not $ prop data /\ tree_Forall (compose not prop) sibling /\ aux child)
  end.
Global Instance tree_Once_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (tree_Once prop tr).
Proof. intro. induction tr; solve_decision. Qed.
*)

Definition tree_StrictChildExists {X} (prop:Tprop X)
  : Tprop (tree X) := fun tr =>
  match tr with
  | empty => False
  | branch _ _ child => tree_Exists prop child
  end.
Global Instance tree_StrictChildExists_dec {X} prop (tr:tree X) :
  (forall u, Decision (prop u)) -> Decision (tree_StrictChildExists prop tr).
Proof. intro. induction tr; solve_decision. Qed.

Definition tree_ChildExists {X} (prop:Tprop X)
  : Tprop (tree X) := fun tr =>
  match tr with
  | empty => False
  | branch self _ child => prop self \/ tree_Exists prop child
  end.
Global Instance tree_ChildExists_dec {X} prop (tr:tree X) :
  (forall u, Decision (prop u)) -> Decision (tree_ChildExists prop tr).
Proof. intro. rewrite /tree_ChildExists. case_match; solve_decision. Qed.

Definition tree_AtNode {X} (search:Tprop X) (prop:Tprop (tree X))
  : Tprop (tree X) := fix aux tr : Prop :=
  match tr with
  | empty => True
  | branch data sibling child => (search data -> prop tr) /\ aux sibling /\ aux child
  end.
Global Instance tree_AtNode_dec {X} search prop (tr:tree X) :
  (forall u, Decision (search u)) -> (forall tr', Decision (prop tr')) -> Decision (tree_AtNode search prop tr).
Proof. intros. induction tr; rewrite /tree_AtNode; solve_decision. Qed.


Definition insert_child_at {X} (tr:tree X) (ins:X) (search:Tprop X) {search_dec:forall x, Decision (search x)} : tree X :=
  (fix aux tr : tree X :=
    match tr with
    | empty => empty
    | branch data sibling child =>
      let sibling := aux sibling in
      let child := aux child in
      if decide (search data)
      then branch data sibling (branch ins child empty)
      else branch data sibling child
    end
  ) tr.

(** CORE SEMANTICS *)



Inductive access_rel := AccessForeign | AccessChild.
Global Instance access_rel_eq_dec : EqDecision access_rel.
Proof. solve_decision. Qed.

Definition IsTag t : Tprop (item) := fun it => it.(itag) = t.
Global Instance IsTag_dec t it : Decision (IsTag t it).
Proof. rewrite /IsTag. solve_decision. Qed.

Definition HasChildTag t' : Tprop (tree item) := tree_ChildExists (IsTag t').
Global Instance HasChildTag_dec t' tr : Decision (HasChildTag t' tr).
Proof. rewrite /HasChildTag. solve_decision. Qed.

Definition ParentChildIn t t' : Tprop (tree item) := tree_AtNode (IsTag t) (HasChildTag t').
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
  : bool :=
  match rel with
  | AccessChild => true
  | AccessForeign => false
  end.

Definition apply_access_perm_inner (kind:access_kind) (rel:access_rel) (isprot:bool)
  : app permission := fun perm =>
  match kind, rel with
  | AccessRead, AccessForeign =>
      match perm with
      | Reserved | ReservedMut => if isprot then Some Frozen else Some perm
      | Active => Some Frozen
      | Frozen | Disabled  => Some perm
      end
  | AccessWrite, AccessForeign =>
      match perm with
      | ReservedMut => if isprot then Some Disabled else Some ReservedMut
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
      | Reserved | ReservedMut | Active => Some Active
      | _ => None
      end
  end.

Definition is_active_call cids c := (c ∈ cids).
Definition is_active_protector cids prot :=
  match prot with
  | Some (mkProtector _ c) => is_active_call cids c
  | _ => False
  end.
Global Instance is_active_protector_dec cids prot : Decision (is_active_protector cids prot).
Proof. rewrite /is_active_protector. rewrite /is_active_call. destruct prot as [[]|]; solve_decision. Qed.

Definition is_strong_protector prot :=
  match prot with
  | Some (mkProtector weak _) => ~Is_true weak
  | _ => False
  end.
Global Instance is_strong_protector_dec prot : Decision (is_strong_protector prot).
Proof. rewrite /is_strong_protector. try repeat case_match; solve_decision. Qed.

Definition validate_access_perm_inner
  : permission -> permission -> bool := fun old new =>
  if decide (old = new) then true
  else match old, new with
  | _, Disabled => false
  | Active, Frozen => false
  | _, _ => true
  end.

Definition apply_access_perm kind rel (isprot:bool)
  : app lazy_permission := fun operm =>
  let old := operm.(perm) in
  new ← apply_access_perm_inner kind rel isprot old;
  validated ← if operm.(initialized) && validate_access_perm_inner old new then Some new else None;
  Some $ mkPerm (operm.(initialized) || requires_init rel) validated.

Definition item_apply_access kind cids rel range
  : app item := fun it =>
  let oldps := it.(iperm) in
  let isprot := bool_decide (is_active_protector cids it.(iprot)) in
  newps ← permissions_foreach (mkPerm false it.(initp)) range (apply_access_perm kind rel isprot) oldps;
  Some $ mkItem it.(itag) it.(iprot) it.(initp) newps.

(* FIXME: is this correct wrt strong protectors ? *)
Definition item_dealloc cids rel range
  : app item := fun it =>
  let oldps := it.(iperm) in
  let isprot := bool_decide (is_active_protector cids it.(iprot)) in
  let isprot_strong := bool_decide (is_active_protector cids it.(iprot) /\ is_strong_protector it.(iprot)) in
  newps ← permissions_foreach (mkPerm false it.(initp)) range (apply_access_perm AccessWrite rel isprot) oldps;
  if isprot_strong then None else Some $ mkItem it.(itag) it.(iprot) it.(initp) newps.

(* FIXME: share code *)
Definition tree_apply_access
  (fn:call_id_set -> access_rel -> (Z * nat) -> app item)
  cids (access_tag:tag) range (tr:tree item) (dyn_rel:rel_dec tr)
  : option (tree item) :=
  let app : item -> option item := fun it => (
    fn cids (if dyn_rel access_tag it.(itag) then AccessChild else AccessForeign) range it
  ) in
  tree_join (tree_map app tr).

Definition init_perms perm range
  : permissions := mem_foreach_defined (fun _ => mkPerm true perm) range gmap_empty.

Definition init_tree t range
  : tree item := branch (mkItem t None Active (init_perms Active range)) empty empty.

Definition extend_trees t blk range
  : trees -> trees := fun ts =>
  <[blk := init_tree t range]>ts.

(* Perform the access check on a block of continuous memory.
 * This implements Tree::before_memory_{read,write,deallocation}. *)
Definition memory_read cids t range
  : app (tree item) := fun tr =>
  tree_apply_access (item_apply_access AccessRead) cids t range tr (naive_rel_dec tr).

Definition memory_write cids t range
  : app (tree item) := fun tr =>
  tree_apply_access (item_apply_access AccessWrite) cids t range tr (naive_rel_dec tr).

Definition memory_deallocate cids t range
  : app (tree item) := fun tr =>
  tree_apply_access item_dealloc cids t range tr (naive_rel_dec tr).


(** CONSISTENCY *)

(* General *)

Lemma not_is_negb (b:bool) :
  b = false <-> ~b = true.
Proof. split; intro. 1: subst; auto. apply not_true_is_false; auto. Qed.

Lemma IsTag_reverse it it' :
  IsTag it.(itag) it' -> IsTag it'.(itag) it.
Proof. unfold IsTag. auto. Qed.

Lemma apply_access_idempotent :
  forall kind rel (isprot isprot':bool) perm perm',
  (apply_access_perm kind rel isprot perm = Some perm') ->
  (apply_access_perm kind rel (if isprot then isprot' else false) perm' = Some perm').
Proof.
  intros kind rel isprot isprot' perm perm' FirstPass.
  destruct perm as [init perm]; destruct perm' as [init' perm'].
  destruct init; destruct init'; destruct perm; destruct perm'.
  all: destruct kind; destruct rel; auto.
  all: destruct isprot; auto.
  all: inversion FirstPass; auto.
Qed.

Lemma join_success_condition {X} (tr:tree (option X)) :
  is_Some (tree_join tr) <-> tree_Forall is_Some tr.
Proof.
  induction tr; simpl; split; auto.
  - intro Computation.
    destruct data; destruct (tree_join tr1); destruct (tree_join tr2).
    all: simpl in Computation; inversion Computation; inversion H.
    rewrite <- IHtr1.
    rewrite <- IHtr2.
    split; [|split]. all: auto.
  - intro AllSuccess.
    destruct AllSuccess as [DataSome [Success1 Success2]].
    destruct DataSome; rewrite H; clear H; simpl.
    destruct (proj2 IHtr1 Success1); rewrite H; clear H; simpl.
    destruct (proj2 IHtr2 Success2); rewrite H; clear H; simpl.
    auto.
Qed.

Lemma tree_Forall_forall {X} P tr :
  tree_Forall P tr <-> (forall (x:X), tree_Exists (fun x' => x = x') tr -> P x).
Proof.
  unfold tree_Forall.
  induction tr; simpl; [split; [intros; contradiction|tauto]|].
  rewrite IHtr1. rewrite IHtr2.
  split; intro; try repeat split.
  - destruct H as [H0 [H1 H2]]. intros it Hyp.
    destruct Hyp as [H'0 | [H'1 | H'2]]; subst; auto.
  - apply H; left; reflexivity.
  - intros it Hyp; apply H; right; left; assumption.
  - intros it Hyp; apply H; right; right; assumption.
Qed.

Lemma tree_Exists_exists {X} P tr :
  tree_Exists P tr <-> (exists (x:X), tree_Exists (fun x' => x = x') tr /\ P x).
Proof.
  unfold tree_Exists.
  induction tr; simpl; [split; [tauto|intro H; destruct H as [_ [Contra _]]; tauto]|].
  rewrite IHtr1. rewrite IHtr2.
  split; intro.
  - destruct H as [H0 | [H1 | H2]].
    * exists data; auto.
    * destruct H1 as [x [Ex Px]].
      exists x; auto.
    * destruct H2 as [x [Ex Px]].
      exists x; auto.
  - destruct H as [x [[H0 | [H1 | H2]] Px]].
    * left; subst; auto.
    * right; left; exists x; auto.
    * right; right; exists x; auto.
Qed.

(* Weakenings, compositions, transitivity *)

Lemma StrictChild_impl_Child {X} (prop:Tprop X) (tr:tree X) :
  tree_StrictChildExists prop tr -> tree_ChildExists prop tr.
Proof. intro. destruct tr; simpl; auto. Qed.

(*
Lemma Once_impl_Exists {X} (tr:tree X) (prop:Tprop X) :
  tree_Once prop tr -> tree_Exists prop tr.
Proof.
  intro Once. induction tr; simpl; auto.
  inversion Once as [
    [H0 [_ _]] | [
    [_ [H1 _]] |
    [_ [_ H2]]
  ]]; auto.
Qed.
*)

Lemma tree_permute_fold_map {X Y Z} (tr:tree X) (unit:Z) (combine:Y -> Z -> Z -> Z) (fn:X -> Y) :
  tree_fold unit combine (tree_map fn tr) = tree_fold unit (fun data lt rt => combine (fn data) lt rt) tr.
Proof.
  induction tr; simpl; auto.
  rewrite IHtr1. rewrite IHtr2.
  reflexivity.
Qed.

Lemma tree_Forall_map {X Y} (tr:tree X) (fn:X -> Y) (prop:Y -> Prop) :
  tree_Forall prop (tree_map fn tr) <-> tree_Forall (compose prop fn) tr.
Proof.
  unfold tree_Forall.
  rewrite tree_permute_fold_map.
  tauto.
Qed.

Lemma tree_Exists_map {X Y} (tr:tree X) (fn:X -> Y) (prop:Y -> Prop) :
  tree_Exists prop (tree_map fn tr) <-> tree_Exists (compose prop fn) tr.
Proof.
  unfold tree_Exists.
  rewrite tree_permute_fold_map.
  tauto.
Qed.

Lemma Forall_not_is_not_Exists {X} (prop:Tprop X) (tr:tree X) :
  tree_Forall (compose not prop) tr
  <-> ~tree_Exists prop tr.
Proof.
  unfold tree_Forall.
  split.
  - intros All Exists.
    induction tr; simpl; auto.
    inversion Exists as [Ex0 | [Ex1 | Ex2]]; simpl.
    all: inversion All as [All0 [All1 All2]]; auto.
  - intros nExists.
    induction tr; simpl; auto.
    try repeat split.
    (* Now swap the goal and the hypothesis that are all negated *)
    all: try apply IHtr1.
    all: try apply IHtr2.
    all: intro; apply nExists.
    all: simpl; auto.
Qed.

Lemma ChildExists_Exists {X} (prop:Tprop X) :
  forall tr,
  tree_ChildExists prop tr -> tree_Exists prop tr.
Proof. induction tr; simpl; auto; tauto. Qed.

Lemma ExistsAtNode_transitive {X} (search search':Tprop X) :
  forall tr,
  tree_Exists search tr ->
  tree_AtNode search (tree_ChildExists search') tr ->
  tree_Exists search' tr.
Proof.
  intros tr Exists Search.
  induction tr; simpl; auto.
  destruct Search as [Search0 [Search1 Search2]].
  destruct Exists as [Exists0 | [Exists1 | Exists2]]; auto.
  destruct (Search0 Exists0); auto.
Qed.

Lemma AtNodeExists_transitive {X} (search search' search'':Tprop X) :
  forall tr,
  tree_AtNode search (tree_ChildExists search') tr ->
  tree_AtNode search' (tree_ChildExists search'') tr ->
  tree_AtNode search (tree_ChildExists search'') tr.
Proof.
  intros tr Search Search'.
  induction tr; auto.
  destruct Search' as [Search' [Search'1 Search'2]].
  destruct Search as [Search [Search1 Search2]].
  pose Found1 := (IHtr1 Search1 Search'1).
  pose Found2 := (IHtr2 Search2 Search'2).
  simpl; try repeat split; auto.
  clear Found1; clear Found2; clear IHtr1; clear IHtr2.
  intro Found; destruct (Search Found) as [Found' | FoundSub].
  - destruct (Search' Found') as [Found'' | Found'Sub]; auto.
  - right; clear Found; clear Search; clear Search1; clear Search2.
    clear Search'.
    apply (ExistsAtNode_transitive search'); auto.
Qed.

Lemma ParentChild_transitive (t t' t'':tag) (tr:tree item) :
  ParentChildIn t t' tr -> ParentChildIn t' t'' tr -> ParentChildIn t t'' tr.
Proof.
  unfold ParentChildIn; unfold HasChildTag.
  apply AtNodeExists_transitive.
Qed.

(* Insertion lemmas *)

Lemma insert_True_preserves_Forall {X} (tr:tree X) (ins:X) (search prop:Tprop X)
  {search_dec:forall x, Decision (search x)} :
  prop ins ->
  tree_Forall prop tr <-> tree_Forall prop (insert_child_at tr ins search).
Proof.
  intro PropIns.
  induction tr; simpl; auto.
  destruct (decide (search data)) eqn:Found.
  (* For most cases, this is straightforward: destruct all and apply inductive hypotheses *)
  all: split; intro H.
  all: destruct H as [HData [H1 H2]].
  all: repeat try split; auto.
  all: try apply IHtr1; auto.
  all: try apply IHtr2; auto.
  (* The one case where this is nontrivial is the case where we did find the object,
     because IH handles (branch data sibling child) and we need (branch data (insert sibling) child) *)
  inversion H2 as [HIns [H2' HE]]; auto.
Qed.

(*
Lemma insert_False_preserves_Once {X} (tr:tree X) (ins:X) (search prop:Tprop X)
  {search_dec:forall x, Decision (search x)} :
  ~prop ins ->
  tree_Once prop tr <-> tree_Once prop (insert_child_at tr ins search).
Proof.
  intro NotIns.
  induction tr; simpl; auto.
  destruct (bool_decide (search data)) eqn:Found.
  all: split; intro H.
  (* Similarly to the Forall version, do a case analysis and try greedily applying inductive hypotheses
     This one is less straightforward because we can't split too agressively, we have to select the left/right path first *)
  all: destruct H as [
    [H0 [nH1 nH2]] | [
    [nH0 [H1 nH2]] |
    [nH0 [nH1 H2]]
  ]]; simpl; auto.
  all: try inversion H2 as [
    [HIns [nHSub nHEmpty]] | [
    [nHIns [HSub nHEmpty]] |
    [nHIns [nHSub HEmpty]]
  ]].
  all: try inversion nH2 as [HIns [HSub HEmpty]].
  (* Rewrite everything imaginable *)
  all: try rewrite <- insert_True_preserves_Forall in *; auto.
  all: try rewrite <- insert_True_preserves_Forall in *; auto.
  all: try rewrite <- insert_True_preserves_Forall in *; auto.
  all: try rewrite <- IHtr1 in *; auto.
  all: try rewrite <- IHtr2 in *; auto.
  (* Finally it's just disjunctions *)
  all: try (left; try repeat split; auto; easy).
  all: try (right; left; try repeat split; auto; easy).
  all: try (right; right; try repeat split; auto; easy).
Qed.
*)

Lemma insert_never_unchanged {X} (tr:tree X) (ins:X) (search prop:Tprop X)
  {search_dec:forall x, Decision (search x)} :
  tree_Forall (compose not search) tr ->
  insert_child_at tr ins search = tr.
Proof.
  induction tr; simpl; auto; intro H.
  destruct H as [H0 [H1 H2]].
  destruct (decide (search data)); [contradiction|].
  rewrite (IHtr1 H1).
  rewrite (IHtr2 H2).
  reflexivity.
Qed.

(*
Lemma insert_True_produces_Once {X} (tr:tree X) (ins:X) (search prop:Tprop X)
  {search_dec:forall x, Decision (search x)}:
  prop ins -> tree_Once search tr ->
  tree_Forall (compose not prop) tr ->
  tree_Once prop (insert_child_at tr ins search).
Proof.
  intros Ins OnceFind Absent.
  induction tr; simpl; auto.
  inversion OnceFind as [
    [Find0 [nFind1 nFind2]] | [
    [nFind0 [Find1 nFind2]] |
    [nFind0 [nFind1 Find2]]
  ]]; simpl; try rewrite Find0; try rewrite nFind0.
  all: try unfold compose in nFind1.
  all: try unfold compose in nFind2.
  all: inversion Absent as [Absent0 [Absent1 Absent2]].
  + (* it's the one we just inserted *)
    unfold compose in Absent0; rewrite (bool_decide_eq_true_2 _ _); [|apply Find0].
    simpl; right; right; try repeat split; auto.
    - rewrite (insert_never_unchanged tr1 ins search (compose not prop) nFind1); exact Absent1.
    - left; try repeat split; auto; rewrite insert_never_unchanged; auto.
  + (* It's further down (1/2) *)
    rewrite (bool_decide_eq_false_2 _ _); [|apply nFind0].
    simpl; right; left; try repeat split; auto.
    rewrite (insert_never_unchanged tr2 _ _ (compose not prop)); auto.
  + (* It's further down (2/2) *)
    rewrite (bool_decide_eq_false_2 _ _); [|apply nFind0].
    simpl; right; right; try repeat split; auto.
    rewrite (insert_never_unchanged tr1 _ _ (compose not prop)); auto.
Qed.
*)

Lemma insert_preserves_Exists {X} (ins:X) (tr:tree X) (search prop:Tprop X)
  {search_dec:forall x, Decision (search x)} :
  tree_Exists prop tr -> tree_Exists prop (insert_child_at tr ins search).
Proof.
  intros Exists.
  induction tr; simpl; auto.
  destruct (decide (search data)).
  all: simpl.
  all: inversion Exists as [Ex0 | [Ex1 | Ex2]].
  all: auto.
  right; right; right; left; auto.
Qed.

Lemma insert_False_infer_Exists {X} (ins:X) (tr:tree X) (search prop:Tprop X)
  {search_dec:forall x, Decision (search x)} :
  ~prop ins ->
  tree_Exists prop (insert_child_at tr ins search) ->
  tree_Exists prop tr.
Proof.
  intros nIns Exists.
  induction tr; simpl; auto.
  simpl in Exists.
  destruct (decide (search data)).
  all: inversion Exists as [Ex0 | [Ex1 | Ex2]].
  all: auto.
  right; right; auto.
  inversion Ex2 as [Ex20 | [Ex21 | Ex22]]; auto.
  - contradiction Ex20.
  - contradiction Ex22.
Qed.

Lemma insert_True_produces_Exists {X} (ins:X) (tr:tree X) (search prop:Tprop X)
  {search_dec:forall x, Decision (search x)} :
  prop ins ->
  tree_Exists search tr ->
  tree_Exists prop (insert_child_at tr ins search).
Proof.
  intros Ins Exists.
  induction tr; simpl; auto.
  destruct (decide (search data)).
  - right; right; left; done.
  - destruct Exists as [Ex0 | [Ex1 | Ex2]].
    * contradiction.
    * right; left; auto.
    * right; right; auto.
Qed.

Lemma insert_preserves_ChildExists {X} (ins:X) (tr:tree X) (search prop:Tprop X)
  {search_dec:forall x, Decision (search x)} :
  tree_ChildExists prop tr -> tree_ChildExists prop (insert_child_at tr ins search).
Proof.
  intro Exists.
  destruct tr; simpl; auto.
  destruct (decide (search data)) eqn:Found; simpl; auto.
  all: simpl in Exists.
  all: inversion Exists as [Ex0 | Ex2]; auto.
  1: right; right; left; apply insert_preserves_Exists; auto.
  right; apply insert_preserves_Exists; auto.
Qed.

Lemma insert_eqv_rel t t' (ins:item) (tr:tree item) (search:Tprop item)
  {search_dec:forall it, Decision (search it)} :
  ~IsTag t ins -> ~IsTag t' ins ->
  ParentChildIn t t' tr <-> ParentChildIn t t' (insert_child_at tr ins search).
Proof.
  intros Nott Nott'; unfold ParentChildIn; induction tr; simpl; auto.
  all: split; intro Hyp.
  + destruct (decide (search data)).
    all: destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
    * simpl; try repeat split.
      - intro H; destruct (Hyp0 H); auto.
        right; right; left. apply insert_preserves_Exists; auto.
      - apply IHtr1; auto.
      - intro H; right; apply Nott; auto.
      - apply IHtr2; auto.
    * simpl; try repeat split.
      - intro H; destruct (Hyp0 H); auto.
        right. apply insert_preserves_Exists; auto.
      - apply IHtr1; auto.
      - apply IHtr2; auto.
  + destruct (decide (search data)).
    all: destruct Hyp as [Hyp0 [Hyp1 Hyp2]].
    * simpl; try repeat split.
      - intro H; destruct (Hyp0 H); auto.
        right. apply (insert_False_infer_Exists ins tr2 search _); auto.
        destruct H0 as [H0Data | [H0Sub | H0Empty]]; auto.
        ++ contradiction Nott'; auto.
        ++ contradiction H0Empty.
      - apply IHtr1; auto.
      - apply IHtr2; auto.
        destruct Hyp2 as [Hyp2Data [Hyp2Sub Hyp2Empty]].
        auto.
    * simpl; try repeat split.
      - intro H; destruct (Hyp0 H); auto.
        right. apply (insert_False_infer_Exists ins tr2 search _); auto.
      - apply IHtr1; auto.
      - apply IHtr2; auto.
Qed.

Lemma insert_produces_ParentChild t (ins:item) (tr:tree item) :
  ParentChildIn t ins.(itag) (insert_child_at tr ins (IsTag t)).
Proof.
  induction tr; simpl; auto.
  destruct (decide (IsTag t data)) eqn:Found.
  - simpl; try repeat split; auto.
    2: unfold IsTag; auto.
    intro; right; left; unfold IsTag; auto.
  - simpl; try repeat split; auto.
    intro Contra; contradiction.
Qed.

Lemma insert_produces_ParentChild_transitive t t' (ins:item) (tr:tree item) :
  ~IsTag t ins -> ~IsTag t' ins ->
  ParentChildIn t t' tr ->
  ParentChildIn t ins.(itag) (insert_child_at tr ins (IsTag t')).
Proof.
  intros Nott Nott' Ptt'.
  apply (ParentChild_transitive t t' ins.(itag)).
  - apply insert_eqv_rel; auto.
  - apply insert_produces_ParentChild.
Qed.

Lemma exists_insert_requires_parent {X} (ins:X) (search prop:Tprop X)
  {search_dec:forall x, Decision (search x)} :
  forall tr,
  tree_Forall (compose not prop) tr ->
  tree_Exists prop (insert_child_at tr ins search) ->
  tree_Exists search tr.
Proof.
  induction tr; simpl; auto.
  intros Hyp Ex.
  destruct Hyp as [Nprop [Absent1 Absent2]].
  destruct (decide (search data)) eqn:Found; auto.
  all: destruct Ex as [Here | [Ex1 | Ex2]]; auto.
  contradiction.
Qed.

Lemma remove_False_preserves_Exists {X} (ins:X) (search prop:Tprop X)
  {search_dec:forall x, Decision (search x)} :
  ~prop ins ->
  forall tr,
  tree_Exists prop (insert_child_at tr ins search) ->
  tree_Exists prop tr.
Proof.
  intros Nprop tr Hyp; induction tr; simpl in *; auto.
  destruct (decide (search data)) eqn:Found; auto.
  all: destruct Hyp as [Here | [Hyp1 | Hyp2]]; auto.
  right; right. destruct Hyp2 as [Contra | [Hyp2Sub | Hyp2Empty]]; auto; contradiction.
Qed.

Lemma insert_produces_minimal_ParentChild (t t':tag) (ins:item) (tr:tree item) :
  ~IsTag t ins ->
  ~IsTag t' ins ->
  tree_Forall (compose not (IsTag ins.(itag))) tr ->
  ParentChildIn t ins.(itag) (insert_child_at tr ins (IsTag t')) ->
  ParentChildIn t t' tr.
Proof.
  intros Nott Nott' Absent Pins.
  induction tr; simpl; auto.
  simpl in Pins; destruct (decide (IsTag t' data)).
  all: destruct Pins as [Pins0 [Pins1 Pins2]].
  all: destruct Absent as [NotHere [Absent1 Absent2]].
  + try repeat split.
    - intro Tg; left; done.
    - exact (IHtr1 Absent1 Pins1).
    - destruct Pins2 as [_ [Pins2Sub _]]. exact (IHtr2 Absent2 Pins2Sub).
  + try repeat split; auto.
    intro Tg. simpl in Pins0. destruct (Pins0 Tg) as [PinsFound | PinsEx].
    - unfold compose in NotHere. contradiction PinsFound.
    - right. eapply (exists_insert_requires_parent ins); [apply Absent2|apply PinsEx].
Qed.

(* FIXME: order of args *)

(** Reborrow *)

Record newperm := mkNewPerm {
  initial_state : permission;
  new_protector : option protector;
}.

Definition newperm_from_ref
  (mut:mutability)
  (frz:freeze)
  (pin:pinedness)
  (rtk:retag_kind)
  (cid:call_id)
  : option newperm :=
  initial ← match mut, pin, frz with
    | Mutable, Unpin, Freeze => Some ReservedMut
    | Mutable, Unpin, Interiormut => Some Reserved
    | Immutable, _, Freeze => Some Frozen
    | _, _, _ => None
    end;
  let newprot := match rtk with FnEntry => Some {| weak:=false; call:=cid |} | Default => None end in
  Some {| initial_state:=initial; new_protector:=newprot |}.

Definition newperm_from_box
  (* FIXME: mut ? *)
  (* FIXME: pin ? *)
  (* FIXME: frz ? *)
  (rtk:retag_kind)
  (cid:call_id)
  : option newperm :=
  let initial := Reserved (* FIXME: mut ? *) in
  let newprot := match rtk with FnEntry => Some {| weak:=true; call:=cid |} | Default => None end in
  Some {| initial_state:=initial; new_protector:=newprot |}.

Definition create_new_item tg perm range :=
  let perms := init_perms perm.(initial_state) range in
  let it := {| itag:=tg; iprot:=perm.(new_protector); initp:=perm.(initial_state); iperm:=perms |} in
  it.

Definition create_child cids (oldt:tag) range (newt:tag) (newp:newperm)
  : app (tree item) := fun tr =>
  tr' ← memory_read cids oldt range tr;
  let it := create_new_item newt newp range in
  Some $ insert_child_at tr' it (IsTag oldt).

(* FIXME: do we need the visitor ? *)
(* NOTE: returns None on noop reborrows do not confuse that with returning None on UB ! *)
Definition reborrow_perm (ptrk:pointer_kind) (rtk:retag_kind) (cid:call_id)
  : option newperm :=
  match ptrk with
  | RefPtr mut frz pin => newperm_from_ref mut frz pin rtk cid
  | RawPtr => None
  | BoxPtr => newperm_from_box rtk cid
  end.

(* FIXME: gmap::partial_alter ? *)
Definition apply_within_trees (fn:app (tree item)) blk
  : app trees := fun trs =>
  oldtr ← trs !! blk;
  newtr ← fn oldtr;
  Some $ <[blk := newtr]> trs.

Definition tree_contains t tr
  : Prop :=
  tree_Exists (IsTag t) tr.

Definition trees_contain t trs blk
  : Prop :=
  match trs !! blk with
  | None => False
  | Some tr => tree_contains t tr
  end.

Definition tag_included (tg: tag) (nxtp:tag) : Prop :=
  let 'Tag nxtp := nxtp in
  let 'Tag tg := tg in
  (tg < nxtp)%nat.

Infix "<t" := tag_included (at level 60, no associativity).
Definition tag_values_included (v: value) nxtp :=
  ∀ l tg, ScPtr l tg ∈ v → tg <t nxtp.
Infix "<<t" := tag_values_included (at level 60, no associativity).

Global Instance tag_included_dec tg nxtp : Decision (tag_included tg nxtp).
Proof. destruct tg; destruct nxtp; cbn; apply _. Qed.
Global Instance tag_values_included_dec v nxtp : Decision (tag_values_included v nxtp).
Proof.
  rewrite /tag_values_included. induction v as [ | sc v IH].
  - left; intros l tg Ha. exfalso. by eapply not_elem_of_nil.
  - destruct sc as [| |l tg| |].
    1,2,4,5: destruct IH as [IH | IH]; [left | right]; setoid_rewrite elem_of_cons; [intros ?? [ [=] | ]| contradict IH]; eauto.
    destruct (decide (tg <t nxtp)) as [Hd | Hd]; destruct IH as [IH | IH]; [left | right | right | right]; setoid_rewrite elem_of_cons; [ | by eauto..].
    intros ?? [[= -> ->] | He]; [done | by eapply IH].
Qed.


(* FIXME: Check this much more thoroughly *)
Inductive bor_step trs cids (nxtp:nat) (nxtc:call_id)
  : event -> trees -> call_id_set -> nat -> call_id -> Prop :=
  | AllocIS (x:loc) ptr :
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
    (RETAG_EFFECT: apply_within_trees (create_child cids parentt (x.2, sizeof ptr) (Tag nxtp) newp) x.1 trs = Some trs') :
    bor_step
      trs cids nxtp nxtc
      (RetagEvt x parentt (Tag nxtp) ptr rtk c)
      trs' cids (S nxtp) nxtc
  .

