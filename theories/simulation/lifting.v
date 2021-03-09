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

  Class PureIrreducible (Φ : Prop) e :=
    pure_irreducible (P : prog Λ) σ : Φ → ∀ e' σ', ¬ prim_step P (e, σ) (e', σ').

End lang.

Section fix_sim.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language} {s : SimulLang PROP Λ}.
  Context (Ω : val Λ → val Λ → PROP).
  Existing Instance sim_stutter.


  Implicit Types
    (e_s e_t e: expr Λ)
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ)
    (Φ Ψ : val Λ → val Λ → PROP).
  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{Ω} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

  (** Pure reduction *)
  Lemma sim_pure_step_source Φ m e_t e_s1 e_s2 ϕ :
    PureExec ϕ m e_s1 e_s2 →
    ϕ → e_t ⪯ e_s2 {{ Φ }} -∗ e_t ⪯ e_s1 {{ Φ }}.
  Proof.
    intros H1 Hϕ. specialize (H1 Hϕ).
    iIntros "H". iApply sim_step_source.
    iIntros (????) "Hstate". iModIntro. 
    iExists e_s2, σ_s. iFrame. iPureIntro.
    induction H1 as [ e_s2 | n e_s1 e_s2 e_s3 Hstep _ IH].
    - constructor.
    - econstructor; last apply IH. destruct Hstep as [Hred Hdet].
      destruct (Hred P_s σ_s) as (e_s' & σ_s' & H).
      by specialize (Hdet _ _ _ _ H) as [-> ->].
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

  (** Primitive reduction *)
  Lemma sim_prim_step_source_eval e_t e_s Φ:
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' σ_t',
        ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
          state_interp P_t σ_t' P_s σ_s ∗
          source_eval (λ _ e_s' _, e_t' ⪯{Ω} e_s' {{ Φ }}) e_s) -∗
    e_t ⪯{Ω} e_s {{ Φ }}.
  Proof.
    iIntros "Hev". iApply sim_step_target. iIntros (????) "Hstate".
    iMod ("Hev" with "Hstate") as "[Hred Hev]". iModIntro. iFrame.
    iIntros (e_t' σ_t') "Htarget". iMod ("Hev" with "Htarget") as "[Hstate Hev]".
    iMod (source_eval_elim with "Hev Hstate") as (e_s' σ_s') "(?&?&?)".
    iModIntro; iExists e_s', σ_s'. iFrame.
  Qed.

  Lemma sim_prim_step_target e_t e_s Φ : 
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' σ_t',
        ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
          state_interp P_t σ_t' P_s σ_s ∗
          e_t' ⪯{Ω} e_s {{ Φ }}) -∗
    e_t ⪯{Ω} e_s {{ Φ }}.
  Proof. 
    iIntros "Ha". iApply sim_prim_step_source_eval. iIntros (????) "Hstate". 
    iMod ("Ha" with "Hstate") as "[Hred Hs]". iModIntro. iFrame. 
    iIntros (e_t' σ_t') "Hprim". iMod ("Hs" with "Hprim") as "[Hstate Hs]". iModIntro. 
    iFrame. iApply source_eval_base; eauto.
  Qed.

  Lemma sim_prim_step_source e_t e_s Φ : 
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ==∗
      ∃ e_s' σ_s',
        ⌜prim_step P_s (e_s, σ_s) (e_s', σ_s')⌝ ∗
          state_interp P_t σ_t P_s σ_s' ∗
          e_t ⪯{Ω} e_s' {{ Φ }}) -∗
    e_t ⪯{Ω} e_s {{ Φ }}.
  Proof. 
    iIntros "Hsource". iApply sim_step_source. 
    iIntros (????) "Hstate". iMod ("Hsource" with "Hstate") as (e_s' σ_s') "[% Hstate]".
    iModIntro. iExists e_s', σ_s'. iFrame. iPureIntro. by econstructor.
  Qed.

  (** Head reduction *)
  Lemma sim_head_step_target e_t e_s Φ : 
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ==∗
      ⌜head_reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' σ_t',
        ⌜head_step P_t e_t σ_t e_t' σ_t'⌝ ==∗
          state_interp P_t σ_t' P_s σ_s ∗
          e_t' ⪯{Ω} e_s {{ Φ }}) -∗
    e_t ⪯{Ω} e_s {{ Φ }}.
  Proof. 
    iIntros "Htarget". iApply sim_prim_step_target. iIntros (????) "Hstate".
    iMod ("Htarget" with "Hstate") as "(% & Hstep)". rename H into Hred. iModIntro.
    iSplitR. { iPureIntro. by apply head_prim_reducible. }
    iIntros (e_t' σ_t') "%". rename H into Hprim. iApply "Hstep".
    iPureIntro. by apply head_reducible_prim_step.
  Qed.

  (** Stuckness *)
  Lemma source_stuck_prim ϕ e_s :
    PureIrreducible ϕ e_s →
    ϕ →
    to_val e_s = None →
    ⊢ source_stuck e_s.
  Proof.
    intros Hirred Hp Hval. iApply stuck_source_stuck.
    iIntros (??). iPureIntro. split; first done.
    by intros e' σ' Hprim%Hirred.
  Qed.

End fix_sim.
