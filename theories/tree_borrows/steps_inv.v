From simuliris.tree_borrows Require Export notation defs.
From simuliris.tree_borrows Require Import steps_progress steps_retag.
From iris.prelude Require Import options.

Lemma head_free_inv (P : prog) l t sz σ σ' e' efs :
  base_step P (Free (PlaceR l t sz)) σ e' σ' efs →
  ∃ trs', 
    (∀ m, is_Some (σ.(shp) !! (l +ₗ m)) ↔ 0 ≤ m < sz) ∧
    (sz > 0)%nat ∧
    trees_contain t σ.(strs) l.1 ∧
    apply_within_trees (memory_deallocate σ.(scs) t (l.2, sz)) l.1 σ.(strs) = Some trs' ∧
    e' = #[☠]%E ∧
    σ' = mkState (free_mem l sz σ.(shp)) (delete l.1 trs') σ.(scs) σ.(snp) σ.(snc) ∧
    efs = [].
Proof. intros Hhead. inv_base_step. eauto 8. Qed.

Lemma head_copy_inv (P : prog) l bor sz σ σ' e' efs :
  base_step P (Copy (Place l bor sz)) σ e' σ' efs →
  trees_contain bor σ.(strs) l.1 ∧
  efs = [] ∧
((apply_within_trees (memory_access AccessRead (scs σ) bor (l.2, sz)) l.1 σ.(strs) = None ∧
  σ = σ' ∧
  e' = ValR (replicate sz ScPoison)%V) ∨
  ∃ trs' (v':value),
  e' = (v')%E ∧
  σ' = mkState σ.(shp) trs' σ.(scs) σ.(snp) σ.(snc) ∧
  read_mem l sz σ.(shp) = Some v' ∧
  apply_within_trees (memory_access AccessRead (scs σ) bor (l.2, sz)) l.1 σ.(strs) = Some trs').
Proof. intros Hhead. inv_base_step; destruct σ; eauto 9. Qed.

Lemma head_write_inv (P : prog) l bor sz v σ σ' e' efs :
  base_step P (Write (Place l bor sz) (Val v)) σ e' σ' efs →
  ∃ trs',
  efs = [] ∧
  e' = (#[ScPoison])%E ∧
  σ' = mkState (write_mem l v σ.(shp)) trs' σ.(scs) σ.(snp) σ.(snc) ∧
  length v = sz ∧
  (∀ i : nat, (i < length v)%nat → l +ₗ i ∈ dom σ.(shp)) ∧
  trees_contain bor σ.(strs) l.1 ∧
  apply_within_trees (memory_access AccessWrite (scs σ) bor (l.2, sz)) l.1 σ.(strs) = Some trs'.
Proof. intros Hhead. inv_base_step. eauto 9. Qed.

(*
Lemma head_retag_inv (P : prog) σ σ' e' efs l ot c pkind T rkind :
  base_step P (Retag #[ScPtr l ot] #[ScCallId c] pkind T rkind) σ e' σ' efs →
  ∃ nt α' nxtp',
  retag σ.(sst) σ.(snp) σ.(scs) c l ot rkind pkind T = Some (nt, α', nxtp') ∧
  e' = (#[ScPtr l nt])%E ∧
  efs = [] ∧
  σ' = mkState σ.(shp) α' σ.(scs) nxtp' σ.(snc) ∧
  c ∈ σ.(scs).
Proof. intros Hhead. inv_base_step. eauto 8. Qed.

Lemma head_init_call_inv (P : prog) e' σ σ' efs :
  base_step P InitCall σ e' σ' efs →
  ∃ c,
    c = σ.(snc) ∧
    efs = [] ∧
    e' = (#[ScCallId c])%E ∧
    σ' = (mkState σ.(shp) σ.(sst) ({[ σ.(snc) ]} ∪ σ.(scs)) σ.(snp) (S σ.(snc))).
Proof. intros Hhead. inv_base_step. eauto. Qed.

Lemma head_end_call_inv (P : prog) e' σ σ' efs c :
  base_step P (EndCall #[ScCallId c]) σ e' σ' efs →
  c ∈ σ.(scs) ∧
  efs = [] ∧
  e' = (#[☠])%E ∧
  σ' = state_upd_calls (.∖ {[ c ]}) σ.
Proof. intros Hhead. inv_base_step. eauto. Qed.
*)


Lemma head_alloc_inv (P : prog) sz σ σ' e' efs :
  base_step P (Alloc sz) σ e' σ' efs →
  let blk := fresh_block σ.(shp) in
  (sz > 0)%nat ∧
  efs = [] ∧
  e' = Place (blk, 0) σ.(snp) sz ∧
  σ' = mkState (init_mem (blk, 0) sz σ.(shp)) (extend_trees σ.(snp) blk 0 sz σ.(strs)) σ.(scs) (S σ.(snp)) σ.(snc).
Proof. intros Hhead. inv_base_step. eauto. Qed.
