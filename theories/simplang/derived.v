(** This file extends the HeapLang program logic with some derived laws (not
using the lifting lemmas) about arrays and prophecies.

For utility functions on arrays (e.g., freeing/copying an array), see
[heap_lang.lib.array].  *)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Export slsls.
From simuliris.simplang Require Export primitive_laws.
From simuliris.simplang Require Import tactics notation.
From iris.prelude Require Import options.

(** The [array] connective is a version of [mapsto] that works
with lists of values. *)
(* again parameterized over the ghost names *)
Definition array `{!sheapG Σ} {γh γm} {hG : gen_heapPreNameG loc (option val) Σ γh γm} (l : loc) (dq : dfrac) (vs : list val) : iProp Σ :=
  ([∗ list] i ↦ v ∈ vs, mapsto (hG:=hG) (l +ₗ i)  dq (Some v%V))%I.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "l ↦t∗{ dq } vs" := (array (hG:=gen_heap_inG_target) l dq vs)
  (at level 20, format "l  ↦t∗{ dq }  vs") : bi_scope.
Notation "l ↦t∗□ vs" := (array (hG:=gen_heap_inG_target) l DfracDiscarded vs)
  (at level 20, format "l  ↦t∗□  vs") : bi_scope.
Notation "l ↦t∗{# q } vs" := (array (hG:=gen_heap_inG_target) l (DfracOwn q) vs)
  (at level 20, format "l  ↦t∗{# q }  vs") : bi_scope.
Notation "l ↦t∗ vs" := (array (hG:=gen_heap_inG_target) l (DfracOwn 1) vs)
  (at level 20, format "l  ↦t∗  vs") : bi_scope.

Notation "l ↦s∗{ dq } vs" := (array (hG:=gen_heap_inG_source) l dq vs)
  (at level 20, format "l  ↦s∗{ dq }  vs") : bi_scope.
Notation "l ↦s∗□ vs" := (array (hG:=gen_heap_inG_source) l DfracDiscarded vs)
  (at level 20, format "l  ↦s∗□  vs") : bi_scope.
Notation "l ↦s∗{# q } vs" := (array (hG:=gen_heap_inG_source) l (DfracOwn q) vs)
  (at level 20, format "l  ↦s∗{# q }  vs") : bi_scope.
Notation "l ↦s∗ vs" := (array (hG:=gen_heap_inG_source) l (DfracOwn 1) vs)
  (at level 20, format "l  ↦s∗  vs") : bi_scope.


(** * Rules for allocation *)
Lemma mapsto_seq_array `{sheapG Σ} {γh γm} {hG : gen_heapPreNameG loc (option val) Σ γh γm} l dq v n :
  ([∗ list] i ∈ seq 0 n, mapsto (hG:=hG) (l +ₗ (i : nat)) dq (Some v)) -∗
  array (hG:=hG) l dq (replicate n v).
Proof.
  rewrite /array. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc. iApply "IH". done.
Qed.

Lemma target_red_allocN `{sheapG Σ} `{sheapInv Σ} v n Ψ :
  (0 < n)%Z →
  (∀ l, l ↦t∗ replicate (Z.to_nat n) v -∗ target_red (of_val #l) Ψ) -∗
  target_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Ψ.
Proof.
  iIntros (Hzs) "Ht". iApply (target_red_allocN_seq); [done..|].
  iIntros (l) "Hlm". iApply "Ht". by iApply mapsto_seq_array.
Qed.

Lemma source_red_allocN `{sheapG Σ} `{sheapInv Σ} v n Ψ :
  (0 < n)%Z →
  (∀ l, l ↦s∗ replicate (Z.to_nat n) v -∗ source_red (of_val #l) Ψ) -∗
  source_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Ψ.
Proof.
  iIntros (Hzs) "Ht". iApply (source_red_allocN_seq); [done..|].
  iIntros (l) "Hlm". iApply "Ht". by iApply mapsto_seq_array.
Qed.


(* TODO: more laws *)
