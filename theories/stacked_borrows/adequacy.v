From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls lifting adequacy.
From simuliris.stacked_borrows Require Import proofmode tactics.
From simuliris.stacked_borrows Require Import parallel_subst primitive_laws
  log_rel_structural wf behavior refl.
From iris.prelude Require Import options.

(* TODO move to std++ *)
Lemma Forall2_cons_iff {A B} (P : A → B → Prop)
  (x : A) (l : list A) (y : B) (k : list B) :
  Forall2 P (x :: l) (y :: k) ↔ P x y ∧ Forall2 P l k.
Proof.
  split.
  - apply Forall2_cons_inv.
  - intros []. by apply Forall2_cons.
Qed.

Lemma sc_rel_obs `{!sborGS Σ} sc_t sc_s :
  sc_rel sc_t sc_s ⊢@{iPropI Σ} ⌜ obs_scalar sc_t sc_s ⌝.
Proof.
  destruct sc_t, sc_s; try by eauto.
  rewrite sc_rel_cid_source. iIntros "[<- _]". eauto.
Qed.

Lemma rrel_obs `{!sborGS Σ} r_t r_s :
  rrel r_t r_s ⊢@{iPropI Σ} ⌜ obs_result r_t r_s ⌝.
Proof.
  destruct r_t as [v_t|], r_s as [v_s|]; try by eauto.
  iInduction v_t as [|sc_t scs_t] "IH" forall (v_s);
    destruct v_s as [|sc_s scs_s]; simpl; try eauto.
  { iIntros "_ !%". constructor. }
  rewrite {2}/value_rel big_sepL2_cons.
  iIntros "[Hs Hss]". rewrite /obs_value Forall2_cons_iff. iSplit.
  - iApply (sc_rel_obs with "Hs").
  - iApply ("IH" with "Hss").
Qed.

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
