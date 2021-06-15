From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst primitive_laws gen_log_rel gen_val_rel.

(** * Generic relation for global variables

This file defines [gen_global_rel] that relates the global variables
of source and target. It is used to prove the reflexivity of
[GlobalVar x]. *)

Section gen_global_rel.
  Context `{!sheapGS Σ} `{!sheapInv Σ}.
  Context (loc_rel : loc → loc → iProp Σ).
  Context (thread_own : thread_id → iProp Σ).
  Let log_rel := (gen_log_rel loc_rel thread_own).

  Definition gen_global_rel (g_t g_s : gset string) : iProp Σ :=
    ⌜g_s ⊆ g_t⌝ ∗ target_globals g_t ∗ source_globals g_s ∗
     [∗ set] g∈g_s, loc_rel (global_loc g) (global_loc g).

  Global Instance gen_global_rel_persistent g_t g_s `{!∀ l_t l_s, Persistent (loc_rel l_t l_s)}:
    Persistent (gen_global_rel g_t g_s).
  Proof. apply _. Qed.

  Definition gen_global_rel_law : Prop :=
    (∀ Φ, (∀ g_t g_s, gen_global_rel g_t g_s -∗ Φ) -∗ update_si Φ).

  Lemma source_red_global' n Ψ π :
    gen_global_rel_law →
    (target_global n -∗ source_global n -∗ loc_rel (global_loc n) (global_loc n) -∗
                   source_red #(global_loc n) π Ψ) -∗
    source_red (GlobalVar n) π Ψ.
  Proof.
    iIntros (Hrel) "Hred".
    iApply source_red_update_si. iApply Hrel. iIntros (g_t g_s) "(%Hsub&Hgs_t&Hgs_s&Hrel)".
    iApply source_red_global. iIntros "#Hg_s".
    iDestruct (heap_global_in with "Hgs_s Hg_s") as %Hin. move: (Hin) => /Hsub?.
    iDestruct (heap_global_intro with "Hgs_t") as "#Hg_t"; [done|].
    iApply "Hred"; [done..|].
    by iApply (big_sepS_elem_of with "Hrel").
  Qed.

  Lemma log_rel_global_var x :
    gen_global_rel_law →
    ⊢ log_rel (GlobalVar x) (GlobalVar x).
  Proof.
    iIntros (Hrel ? xs) "!# Hs Ht"; simpl.
    iApply source_red_sim_expr. iApply source_red_global'; [done|]. iIntros "#Hg_t #Hg_s Hv".
    iApply source_red_base. iModIntro.
    iApply target_red_sim_expr. iApply (target_red_global with "Hg_t"). iApply target_red_base. iModIntro.
    iApply sim_expr_base. iApply lift_post_val. iFrame.
  Qed.
End gen_global_rel.
