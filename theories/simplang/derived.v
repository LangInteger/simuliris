(** This file extends the HeapLang program logic with some derived laws (not
using the lifting lemmas) about arrays and prophecies.

For utility functions on arrays (e.g., freeing/copying an array), see
[heap_lang.lib.array].  *)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From simuliris.simplang Require Export primitive_laws notation.
From iris.prelude Require Import options.



(** * Rules for allocation *)
Lemma mapsto_seq_array `{sheapG Σ} {γh γm} {hG : gen_heapPreNameG loc (option (lock_state * val)) Σ γh γm} l dq v n :
  ([∗ list] i ∈ seq 0 n, mapsto (hG:=hG) (l +ₗ (i : nat)) dq (Some (RSt 0, v))) -∗
  array (hG:=hG) l dq (replicate n v).
Proof.
  rewrite /array /array_st. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc. iApply "IH". done.
Qed.

Lemma target_red_allocN `{sheapG Σ} `{sheapInv Σ} v n Ψ :
  (0 < n)%Z →
  (∀ l, l ↦t∗ replicate (Z.to_nat n) v -∗ l ==>t (Z.to_nat n) -∗ target_red (of_val #l) Ψ) -∗
  target_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Ψ.
Proof.
  iIntros (Hzs) "Ht". iApply (target_red_allocN_seq); [done..|].
  iIntros (l) "Hlm". iApply "Ht". by iApply mapsto_seq_array.
Qed.

Lemma source_red_allocN `{sheapG Σ} `{sheapInv Σ} v n Ψ :
  (0 < n)%Z →
  (∀ l, l ↦s∗ replicate (Z.to_nat n) v -∗ l ==>s (Z.to_nat n) -∗ source_red (of_val #l) Ψ) -∗
  source_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Ψ.
Proof.
  iIntros (Hzs) "Ht". iApply (source_red_allocN_seq); [done..|].
  iIntros (l) "Hlm". iApply "Ht". by iApply mapsto_seq_array.
Qed.


(* TODO: more laws *)
