From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls lifting adequacy.
From simuliris.stacked_borrows Require Import proofmode tactics.
From simuliris.stacked_borrows Require Import parallel_subst primitive_laws
  log_rel_structural wf behavior refl.
From iris.prelude Require Import options.

(** Instantiate our notion of contextual refinement. *)
Notation ctx_rel := (gen_ctx_rel expr_head_wf).

(** Whole-program adequacy. *)

Lemma prog_rel_adequacy Σ `{!sborGpreS Σ} (p_t p_s : prog):
  isat (∀ `(sborGS Σ),
    ([∗ map] f ↦ K ∈ p_t, f @t K) -∗
    ([∗ map] f ↦ K ∈ p_s, f @s K) ==∗
    prog_rel p_t p_s
  ) →
  beh_rel p_t p_s.
Proof.
  intros Hrel. eapply (slsls_adequacy (sat:=isat)).
  eapply sat_mono, Hrel. clear Hrel.
  iIntros "Hprog_rel %σ_t %σ_s (->&->)".
  iMod (sbor_init p_t p_s) as (HsborGS) "(Hstate & Hp_t & Hp_s & Hprogs)".
  iMod ("Hprog_rel" with "Hp_t Hp_s") as "Hprog_rel".
  iModIntro. iExists sborGS_simulirisGS. iFrame.
  iSplitL.
  - by iApply value_rel_poison.
  - iIntros (??) "Hext". iApply rrel_obs. done.
Qed.

(** Adequacy for open terms. *)
Theorem log_rel_adequacy Σ `{!sborGpreS Σ} e_t e_s :
  (∀ `(sborGS Σ), ⊢ log_rel e_t e_s) →
  ctx_rel e_t e_s.
Proof.
  intros Hrel C fname x p Hpwf HCwf Hvars.
  apply (prog_rel_adequacy Σ). eapply isat_intro.
  iIntros (?) "_ _ !>".
  rewrite /prog_rel.
  iIntros "!# %f %arg %body".
  iDestruct (Hrel _) as "Hrel". clear Hrel.
  destruct (decide (f = fname)) as [->|Hne].
  - rewrite !lookup_insert.
    iIntros ([= <- <-]). iExists _, _. iSplitR; first done.
    (* TODO Factor this into a general lemma? *)
    iIntros (v_t v_s π) "#Hval /=".
    iApply sim_wand.
    + iApply (gen_log_rel_singleton with "[Hrel] Hval []"); first done.
      * by iApply log_rel_ctx.
      * done.
    + simpl. iIntros (??). rewrite left_id. auto.
  - rewrite !lookup_insert_ne //.
    iIntros (Hf). iExists arg, body. iSplit; first done.
    specialize (Hpwf _ _ Hf). destruct Hpwf as [HKwf HKclosed].
    (* TODO Factor this into a lemma? *)
    iIntros (v_t v_s π) "#Hval /=".
    iApply sim_wand.
    + iApply (gen_log_rel_singleton with "[Hrel] Hval []"); first set_solver.
      * by iApply log_rel_refl.
      * done.
    + simpl. iIntros (??). rewrite left_id. auto.
Qed.
