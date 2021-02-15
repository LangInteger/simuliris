From simuliris.simulation Require Import language slsls.
From iris Require Import bi.bi bi.lib.fixpoint.
Import bi.
From iris.proofmode Require Import tactics.



(* TODO move to language.v? *)
Section lang.
  Context {Λ : language}.
   Record pure_step (e1 e2 : expr Λ) := {
      pure_step_safe P σ1 : reducible P e1 σ1;
      pure_step_det P σ1 e2' σ2:
        prim_step P (e1, σ1) (e2', σ2) → σ2 = σ1 ∧ e2' = e2
    }.

  Notation pure_steps_tp := (Forall2 (rtc pure_step)).

  (* TODO: we probably don't need the n anymore, since we don't have laters. maybe remove *)
  (* TODO: Exclude the case of [n=0], either here, or in [wp_pure] to avoid it
  succeeding when it did not actually do anything. *)
  Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
    pure_exec : φ → nsteps pure_step n e1 e2.

  Coercion fill : ectx >-> Funclass.
  Lemma pure_step_ctx (K : ectx Λ) e1 e2 :
    pure_step e1 e2 →
    pure_step (K e1) (K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible in *. naive_solver eauto using fill_prim_step.
    - intros P σ1 e2' σ2 Hpstep.
      by destruct (fill_reducible_prim_step _ _ _ _ _ _ (Hred P σ1) Hpstep) as
        (e2'' & -> & [-> ->]%Hstep).
  Qed.

  Lemma pure_step_nsteps_ctx (K : ectx Λ) n e1 e2 :
    nsteps pure_step n e1 e2 →
    nsteps pure_step n (K e1) (K e2).
  Proof. eauto using pure_step_ctx, nsteps_congruence. Qed.

  Lemma rtc_pure_step_ctx (K : ectx Λ) e1 e2 :
    rtc pure_step e1 e2 → rtc pure_step (K e1) (K e2).
  Proof. eauto using rtc_congruence, pure_step_ctx. Qed.

  (* We do not make this an instance because it is awfully general. *)
  Lemma pure_exec_ctx (K : ectx Λ) φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (K e1) (K e2).
  Proof. rewrite /PureExec; eauto using pure_step_nsteps_ctx. Qed.

  Record pure_head_step (e1 e2 : expr Λ) := {
    pure_head_step_safe P σ1 : head_reducible P e1 σ1;
    pure_head_step_det P σ1 e2' σ2 :
      head_step P e1 σ1 e2' σ2 → σ2 = σ1 ∧ e2' = e2
  }.

  Lemma pure_head_step_pure_step e1 e2 : pure_head_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros P σ. destruct (Hp1 P σ) as (e2' & σ2 & ?).
      eexists e2', σ2. by apply head_prim_step.
    - intros P σ1 e2' σ2 ?%head_reducible_prim_step; eauto.
  Qed.
End lang.

Section fix_sim.
  Context {PROP : bi} {PROP_bupd : BiBUpd PROP} {PROP_affine : BiAffine PROP}.
  Context {Λ : language} {s : simul_lang PROP Λ}.
  Instance: Sim s := (sim_stutter (s := s)).

  Lemma sim_pure_step_source Φ m e1 e2 e_s1 e_s2 ϕ :
    pure_step e1 e2 → PureExec ϕ m e_s1 e_s2 →
    ϕ → e2 ⪯ e_s2 {{ Φ }} -∗ e1 ⪯ e_s1 {{ Φ }}.
  Proof.
    intros H1 H2 Hϕ. specialize (H2 Hϕ). destruct H1 as [Hred Hdet].
    iIntros "H". iApply sim_step_target.
    iIntros (????) "Hstate". iModIntro. iSplitL "".
    { iPureIntro. apply Hred. }
    iIntros (??) "%". iModIntro. apply Hdet in H as [-> ->].
    iExists e_s2, σ_s. iFrame. iPureIntro. clear Hred Hdet.
    induction H2 as [ e_s2 | n e_s1 e_s2 e_s3 Hstep _ IH].
    - constructor.
    - econstructor; last apply IH. destruct Hstep as [Hred Hdet].
      destruct (Hred P_s σ_s) as (e_s' & σ_s' & H).
      by specialize (Hdet _ _ _ _ H) as [-> ->].
  Qed.

  Lemma sim_pure_steps Φ n m e1 e2 e_s1 e_s2 ϕ' ϕ :
    PureExec ϕ n e1 e2 → PureExec ϕ' m e_s1 e_s2 → n > 0 →
    ϕ → ϕ' → e2 ⪯ e_s2 {{ Φ }} -∗ e1 ⪯ e_s1 {{ Φ }}.
  Proof.
    intros H1 H2 Hgt Hϕ Hϕ'. specialize (H1 Hϕ).
    iInduction H1 as [ | n e1 e2 e3 Hstep Hsteps] "IH". { lia. }
    destruct n as [ | n]. { inversion Hsteps; subst. iApply sim_pure_step_source; eauto. }
    iIntros "H". iApply sim_stutter_source. destruct Hstep as [Hred Hdet].
    iIntros (????) "Hstate". iModIntro. iSplitL "".
    { iPureIntro. apply Hred. }
    iIntros (??) "%". iModIntro. apply Hdet in H as [-> ->].
    iFrame. iApply "IH". { iPureIntro; lia. } iApply "H".
  Qed.

  Lemma sim_pure_step_target Φ n e1 e2 e_s ϕ :
    PureExec ϕ n e1 e2 →
    ϕ → e2 ⪯ e_s {{ Φ }} -∗ e1 ⪯ e_s {{ Φ }}.
  Proof.
    intros H1 H2. specialize (H1 H2). induction H1 as [ | n e1 e2 e3 Hstep _ IH].
    - eauto.
    - iIntros "H". iApply sim_stutter_source. destruct Hstep as [Hred Hdet].
      iIntros (????) "Hstate". iModIntro. iSplitL "".
      { iPureIntro. apply Hred. }
      iIntros (??) "%". iModIntro. apply Hdet in H as [-> ->].
      iFrame. iApply IH. iApply "H".
  Qed.

End fix_sim.
