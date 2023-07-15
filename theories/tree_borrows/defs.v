(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From iris.prelude Require Export prelude.
From simuliris.tree_borrows Require Export tactics notation lang bor_semantics.
From iris.prelude Require Import options.

(* Henceforth also in the files importing us we want to use Z_scope. *)
Global Open Scope Z_scope.

Definition wf_mem_tag (h: mem) (nxtp: nat) :=
  ∀ (l l':loc) pid, h !! l = Some (ScPtr l' pid) →
    let '(Tag pid) := pid in
    (pid < nxtp)%nat.

Definition item_wf (it:item) (nxtp:nat) (nxtc:call_id) :=
  (forall tg, IsTag (Tag tg) it -> (tg < nxtp)%nat)
  /\ (forall cid, protector_is_for_call (iprot it) cid -> (cid < nxtc)%nat).

Definition tree_item_included (tr:tree item) (nxtp:nat) (nxtc: call_id) :=
  forall tg,
  tree_contains tg tr -> exists it,
  tree_unique tg tr it /\ item_wf it nxtp nxtc.

Definition wf_tree (tr:tree item) (nxtp:nat) (nxtc:call_id) :=
  tree_item_included tr nxtp nxtc.
Definition wf_trees (trs:trees) (nxtp:nat) (nxtc: call_id) :=
  ∀ blk tr, trs !! blk = Some tr → wf_tree tr nxtp nxtc.
Definition wf_non_empty (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → tr ≠ empty.
(*
Definition wf_no_dup (α: stacks) :=
  ∀ l stk, α !! l = Some stk → NoDup stk.
*)
Definition wf_cid_incl (cids: call_id_set) (nxtc: call_id) :=
  ∀ c : call_id, c ∈ cids → (c < nxtc)%nat.
Definition wf_scalar t sc := ∀ t' l, sc = ScPtr l t' → t' <t t.

Definition same_blocks (hp:mem) (trs:trees) :=
  forall blk l, is_Some (hp !! (blk, l)) -> is_Some (trs !! blk).

Record state_wf (s: state) := {
  (*state_wf_dom : dom s.(shp) ≡ dom s.(strs); Do we care ? After all TB is very permissive about the range, so out-of-bounds UB is *always* triggered at the level of the heap, not the trees *)
  state_wf_dom : same_blocks s.(shp) s.(strs);
  (*state_wf_mem_tag : wf_mem_tag s.(shp) s.(snp);*)
  state_wf_tree_item : wf_trees s.(strs) s.(snp) s.(snc);
  state_wf_non_empty : wf_non_empty s.(strs);
  (*state_wf_cid_no_dup : NoDup s.(scs) ;*)
  state_wf_cid_agree: wf_cid_incl s.(scs) s.(snc);
  (* state_wf_cid_non_empty : s.(scs) ≠ []; *)
  (* state_wf_no_dup : wf_no_dup σ.(cst).(sst); *)
}.

Definition init_state := (mkState ∅ ∅ {[O]} O 1).

Inductive tag_kind := tk_pub  | tk_unq | tk_local.

Definition state_upd_mem (f : mem → mem) σ :=
  mkState (f σ.(shp)) σ.(strs) σ.(scs) σ.(snp) σ.(snc).
Definition state_upd_trees (f : trees → trees) σ :=
  mkState σ.(shp) (f σ.(strs)) σ.(scs) σ.(snp) σ.(snc).
Definition state_upd_calls (f : call_id_set → call_id_set) σ :=
  mkState σ.(shp) σ.(strs) (f σ.(scs)) σ.(snp) σ.(snc).
