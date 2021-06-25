From simuliris.simulation Require Import slsls lifting gen_log_rel.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import primitive_laws gen_val_rel.
From iris.prelude Require Import options.

(** * Bijection between global variables

This file defines [globalbij] that asserts that all global variables
are related via a [loc_rel] chosen by the user. It is used to prove
the reflexivity of [GlobalVar x]. *)

Section globalbij.
  Context `{!sheapGS Σ} `{!sheapInv Σ}.
  Context (loc_rel : loc → loc → iProp Σ) {Hpers : ∀ l_t l_s, Persistent (loc_rel l_t l_s)}.
  Context (thread_own : thread_id → iProp Σ).
  Local Notation val_rel := (gen_val_rel loc_rel).
  Local Notation log_rel := (gen_log_rel val_rel thread_own).

  Definition globalbij_interp : iProp Σ :=
     ∃ gs_t gs_s, ⌜gs_s ⊆ gs_t⌝ ∗ target_globals gs_t ∗ source_globals gs_s ∗
     [∗ set] g∈gs_s, loc_rel (global_loc g) (global_loc g).

  Global Instance globalbij_interp_persistent: Persistent globalbij_interp.
  Proof using Hpers. apply _. Qed.

  (** If one can extract [globalbij_interp] from [sheap_inv], one can
      prove [log_rel (GlobalVar x) (GlobalVar x)] and a stronger lemma
      for [source_red (GlobalVar n)] (see the lemmas below). *)
  Definition sheap_inv_contains_globalbij : Prop :=
    ∀ P_s σ_s T_s, sheap_inv P_s σ_s T_s -∗ globalbij_interp.

  Lemma source_red_global' n Ψ π :
    sheap_inv_contains_globalbij →
    (target_global n -∗ source_global n -∗ loc_rel (global_loc n) (global_loc n) -∗
       source_red #(global_loc n) π Ψ) -∗
    source_red (GlobalVar n) π Ψ.
  Proof using Hpers.
    iIntros (Hrel) "Hred".
    iApply source_red_update_si.
    iIntros (?????) "($&$&$&$&Hinv)". iDestruct (Hrel with "Hinv") as "#Hbij".
    iFrame. iModIntro.
    iDestruct "Hbij" as (gs_t gs_s) "(%Hsub&Hgs_t&Hgs_s&Hrel)".
    iApply source_red_global. iIntros "#Hg_s".
    iDestruct (heap_global_in with "Hgs_s Hg_s") as %Hin. move: (Hin) => /Hsub?.
    iDestruct (heap_global_intro with "Hgs_t") as "#Hg_t"; [done|].
    iApply "Hred"; [done..|].
    by iApply (big_sepS_elem_of with "Hrel").
  Qed.

  Lemma log_rel_global_var x :
    sheap_inv_contains_globalbij →
    ⊢ log_rel (GlobalVar x) (GlobalVar x).
  Proof using Hpers.
    rewrite /log_rel /gen_log_rel.
    iIntros (Hrel ? xs) "!# Hs Ht"; simpl.
    iApply source_red_sim_expr. iApply source_red_global'; [done|]. iIntros "#Hg_t #Hg_s Hv".
    iApply source_red_base. iModIntro.
    iApply target_red_sim_expr. iApply (target_red_global with "Hg_t"). iApply target_red_base. iModIntro.
    iApply sim_expr_base. iApply lift_post_val. iFrame.
  Qed.
End globalbij.

Typeclasses Opaque globalbij_interp.
