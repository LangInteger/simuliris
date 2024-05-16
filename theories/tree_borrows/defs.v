(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From iris.prelude Require Export prelude.
From simuliris.tree_borrows Require Export tactics notation lang bor_semantics bor_lemmas.
From iris.prelude Require Import options.

(* Henceforth also in the files importing us we want to use Z_scope. *)
Global Open Scope Z_scope.

Definition wf_mem_tag (h: mem) (nxtp: tag) :=
  ∀ (l l':loc) pid, h !! l = Some (ScPtr l' pid) →
    (pid < nxtp)%nat.

Definition lazy_perm_wf (lp : lazy_permission) :=
  lp.(perm) = Active → lp.(initialized) = PermInit.

Record item_wf (it:item) (nxtp:tag) (nxtc:call_id) := {
  item_tag_valid : forall tg, IsTag tg it -> (tg < nxtp)%nat;
  item_cid_valid : forall cid, protector_is_for_call cid (iprot it) -> (cid < nxtc)%nat;
  item_default_perm_valid : it.(initp) ≠ Active;
  item_perms_valid : map_Forall (λ _, lazy_perm_wf) it.(iperm);
  item_perm_reachable : it.(initp) ≠ Disabled → map_Forall (λ k v, reach it.(initp) (perm v)) it.(iperm)
}.

Definition item_all_more_init itp itc := ∀ l, initialized (item_lookup itc l) = PermInit → initialized (item_lookup itp l) = PermInit.
Definition parents_more_init (tr : tree item) := ∀ tg, every_child tg item_all_more_init tr.
Definition item_all_more_active itp itc := ∀ l, perm (item_lookup itc l) = Active → perm (item_lookup itp l) = Active.
Definition parents_more_active (tr : tree item) := ∀ tg, every_child tg item_all_more_active tr.

Definition item_protected_all_parents_not_disabled C itp itc := ∀ l, initialized (item_lookup itc l) = PermInit → protector_is_active (iprot itc) C → perm (item_lookup itp l) ≠ Disabled.
Definition protected_parents_not_disabled C (tr : tree item) := ∀ tg, every_child tg (item_protected_all_parents_not_disabled C) tr.

Definition tree_items_unique (tr:tree item) :=
  forall tg,
  tree_contains tg tr -> tree_unique tg tr.

Definition tree_items_compat_nexts (tr:tree item) (nxtp:tag) (nxtc: call_id) :=
  every_node (λ it, item_wf it nxtp nxtc) tr.
  (* FIXME: rename above to just tree_items_wf *)

(* FIXME: consistent naming *)
Definition wf_tree (tr:tree item) :=
  tree_items_unique tr.
Definition each_tree_wf (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → wf_tree tr.
Definition each_tree_parents_more_init (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → parents_more_init tr.
Definition each_tree_parents_more_active (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → parents_more_active tr.
Definition each_tree_protected_parents_not_disabled C (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → protected_parents_not_disabled C tr.
Definition tags_unique_per_location (trs:trees) :=
  ∀ blk1 blk2 tr1 tr2 tg, trs !! blk1 = Some tr1 → trs !! blk2 = Some tr2 →
          tree_contains tg tr1 → tree_contains tg tr2 → blk1 = blk2.
Definition wf_trees (trs:trees) :=
  each_tree_wf trs ∧ tags_unique_per_location trs.
Definition trees_compat_nexts (trs:trees) (nxtp:tag) (nxtc: call_id) :=
  ∀ blk tr, trs !! blk = Some tr → tree_items_compat_nexts tr nxtp nxtc.
Definition wf_non_empty (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → tr ≠ empty.
(*
Definition wf_no_dup (α: stacks) :=
  ∀ l stk, α !! l = Some stk → NoDup stk.
*)
Definition wf_cid_incl (cids: call_id_set) (nxtc: call_id) :=
  ∀ c : call_id, c ∈ cids → (c < nxtc)%nat.
Definition wf_scalar t sc := ∀ t' l, sc = ScPtr l t' → t' < t.

(* mem ~ gmap loc scalar
*)

Definition same_blocks (hp:mem) (trs:trees) :=
  dom trs =@{gset _} set_map fst (dom hp).
Arguments same_blocks / _ _.
(* OLD: forall blk l, is_Some (hp !! (blk, l)) -> is_Some (trs !! blk). *)
(* FIXME: map fst (dom hp) === dom trs *)
(* FIXME: forall blk, (exists l, is_Some (hp !! (blk, l))) <-> is_Some (trs !! blk). *)

Definition root_invariant blk it (shp : mem) :=
  it.(iprot) = None ∧
  ∀ off, match item_lookup it off with
    mkPerm PermInit Active => is_Some (shp !! (blk, off))
  | mkPerm PermLazy Disabled => shp !! (blk, off) = None
  | _ => False end.


Definition tree_root_compatible (tr : tree item) blk shp := 
  match tr with empty => False | branch it sib _ => root_invariant blk it shp ∧ sib = empty end.

Definition tree_roots_compatible (trs : trees) shp := 
  ∀ blk tr, trs !! blk = Some tr → tree_root_compatible tr blk shp.


Record state_wf (s: state) := {
  (*state_wf_dom : dom s.(shp) ≡ dom s.(strs); Do we care ? After all TB is very permissive about the range, so out-of-bounds UB is *always* triggered at the level of the heap, not the trees *)
  state_wf_dom : same_blocks s.(shp) s.(strs);
  (*state_wf_mem_tag : wf_mem_tag s.(shp) s.(snp);*) (* FIXME: this seems to state that all pointers are wf, it should be included *)
  state_wf_tree_unq : wf_trees s.(strs);
  state_wf_tree_more_init : each_tree_parents_more_init s.(strs);
  state_wf_tree_more_active : each_tree_parents_more_active s.(strs);
  state_wf_tree_not_disabled :  each_tree_protected_parents_not_disabled s.(scs) s.(strs);
  state_wf_tree_compat : trees_compat_nexts s.(strs) s.(snp) s.(snc);
  (* state_wf_non_empty : wf_non_empty s.(strs); *)
  state_wf_roots_active : tree_roots_compatible s.(strs) s.(shp);
  (*state_wf_cid_no_dup : NoDup s.(scs) ;*) (* FIXME: call ids are unique, include this *)
  state_wf_cid_agree: wf_cid_incl s.(scs) s.(snc);
  (* state_wf_cid_non_empty : s.(scs) ≠ []; *)
  (* state_wf_no_dup : wf_no_dup σ.(cst).(sst); *)
}.

Definition init_state := (mkState ∅ ∅ {[O]} O 1).

(** Tag kinds:
    - `tk_pub`: this tag is public
    - `tk_unq tk_res` and `tk_unq tk_act`: split from the `tk_unq` in Stacked Borrows.
      We need two of them to support the two stages of 2-phase borrows.
      The intent is that whatever mutable reference is reborrowed gets a
      `tk_unq tk_res` initially and on the first child write we can change it to a
      `tk_unq tk_act`.
    - `tk_local`: locally owned tag without any references (not even local reborrows). *)
Inductive tk_activation_kind := tk_res | tk_act.
Inductive tag_kind := tk_pub | tk_unq (act : tk_activation_kind) | tk_local.

Definition state_upd_mem (f : mem → mem) σ :=
  mkState (f σ.(shp)) σ.(strs) σ.(scs) σ.(snp) σ.(snc).
Definition state_upd_trees (f : trees → trees) σ :=
  mkState σ.(shp) (f σ.(strs)) σ.(scs) σ.(snp) σ.(snc).
Definition state_upd_calls (f : call_id_set → call_id_set) σ :=
  mkState σ.(shp) σ.(strs) (f σ.(scs)) σ.(snp) σ.(snc).
