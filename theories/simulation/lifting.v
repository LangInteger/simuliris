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

  Class SIrreducible (Φ : Prop) (P : prog Λ) e σ  :=
    sirreducible : Φ → irreducible P e σ.

  (* a more constructive formulation *)
  Class IrredUnless (ϕ : Prop) P (e : expr Λ) σ :=
    irred_unless : ¬ irreducible P e σ → ϕ.

  Global Instance irred_unless_sirreducible ϕ P e σ : IrredUnless ϕ P e σ → SIrreducible (¬ ϕ) P e σ.
  Proof.
    intros Hunless Hϕ e' σ' Hprim. apply Hϕ, Hunless. intros Hirred. by eapply Hirred.
  Qed.

  (** We can get the other direction if we can decide ϕ (or assume XM) *)
  Lemma irred_unless_irred_dec ϕ P e σ :
    Decision ϕ →
    SIrreducible (¬ ϕ) P e σ →
    IrredUnless ϕ P e σ.
  Proof.
    intros [Hphi | Hnphi] Hirred Hnirred; first done.
    contradict Hnirred. by apply Hirred.
  Qed.

  Lemma irred_unless_weaken P e σ (ϕ ψ : Prop)  :
    (ϕ → ψ) →
    IrredUnless ϕ P e σ → IrredUnless ψ P e σ.
  Proof. intros Hw Hnirred Hirred. by apply Hw, Hnirred. Qed.
End lang.

#[export]
Hint Mode SIrreducible - - - + - : core.
#[export]
Hint Mode IrredUnless - - - + - : core.
#[export]
Hint Mode PureExec - - - + - : core.

Section fix_sim.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language} {s : SimulLang PROP Λ}.
  Context (Ω : val Λ → val Λ → PROP).

  Implicit Types
    (e_s e_t e: expr Λ)
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ).
  Local Notation "et '⪯' es [{ Φ }]" := (et ⪯{Ω} es [{Φ}])%I (at level 40, Φ at level 200) : bi_scope.

  (** Pure reduction *)
  Lemma source_red_lift_pure Ψ m e_s1 e_s2 ϕ :
    PureExec ϕ m e_s1 e_s2 →
    ϕ → source_red e_s2 Ψ -∗ source_red e_s1 Ψ.
  Proof.
    intros Hp Hϕ. specialize (Hp Hϕ).
    induction Hp as [ e_s2 | n e_s1 e_s2 e_s3 Hstep _ IH]; first done.
    rewrite IH. iIntros "Hs". iApply source_red_step.
    iIntros (????) "[Hstate %Hnreach]". iModIntro. iExists e_s2, σ_s.
    iFrame.
    destruct Hstep as [Hred Hdet]. destruct (Hred P_s σ_s) as (e_s' & σ_s' & H).
    by specialize (Hdet _ _ _ _ H) as [-> ->].
  Qed.

  Lemma target_red_lift_pure Ψ n e1 e2 ϕ :
    PureExec ϕ n e1 e2 →
    ϕ → target_red e2 Ψ -∗ target_red e1 Ψ.
  Proof.
    intros Hp Hϕ. specialize (Hp Hϕ).
    induction Hp as [ e_t2 | n e_t1 e_t2 e_t3 Hstep _ IH]; first done.
    rewrite IH. iIntros "Ht". iApply target_red_step.
    iIntros (????) "Hstate". iModIntro. iSplitR. { iPureIntro. apply Hstep. }
    iIntros (??) "%". iModIntro. apply Hstep in H as [-> ->]. iFrame.
  Qed.

  (** Primitive reduction *)
  Lemma sim_lift_prim_step_target e_t e_s Φ :
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' σ_t',
        ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
          state_interp P_t σ_t' P_s σ_s ∗
          e_t' ⪯{Ω} e_s [{ Φ }]) -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "Ha".
    iApply sim_step_target. iIntros (????) "[Hstate %Hnreach]".
    iMod ("Ha" with "[$Hstate//]") as "[Hred Hev]". iModIntro. iFrame.
    iIntros (e_t' σ_t') "Htarget". iMod ("Hev" with "Htarget") as "[Hstate Hev]".
    iModIntro; iExists e_s, σ_s. iFrame. iPureIntro; constructor.
  Qed.

  Lemma sim_lift_prim_step_source e_t e_s Φ :
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ==∗
      ∃ e_s' σ_s',
        ⌜prim_step P_s (e_s, σ_s) (e_s', σ_s')⌝ ∗
          state_interp P_t σ_t P_s σ_s' ∗
          e_t ⪯{Ω} e_s' [{ Φ }]) -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "Hsource". iApply sim_step_source.
    iIntros (????) "[Hstate %Hnreach]".
    iMod ("Hsource" with "Hstate") as (e_s' σ_s') "[% Hstate]".
    iModIntro. iExists e_s', σ_s'. iFrame. iPureIntro. by econstructor.
  Qed.

  (** Head reduction *)
  Lemma sim_lift_head_step_target e_t e_s Φ :
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗
      ⌜head_reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' σ_t',
        ⌜head_step P_t e_t σ_t e_t' σ_t'⌝ ==∗
          state_interp P_t σ_t' P_s σ_s ∗
          e_t' ⪯{Ω} e_s [{ Φ }]) -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "Htarget". iApply sim_lift_prim_step_target. iIntros (????) "[Hstate %Hnreach]".
    iMod ("Htarget" with "[$Hstate//]") as "(% & Hstep)". rename H into Hred. iModIntro.
    iSplitR. { iPureIntro. by apply head_prim_reducible. }
    iIntros (e_t' σ_t') "%". rename H into Hprim. iApply "Hstep".
    iPureIntro. by apply head_reducible_prim_step.
  Qed.

  (* for symmetry, in this lemma nothing actually happens *)
  Lemma sim_lift_head_step_source e_t e_s Φ :
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ==∗
      ∃ e_s' σ_s',
        ⌜head_step P_s e_s σ_s e_s' σ_s'⌝ ∗ |==>
          (state_interp P_t σ_t P_s σ_s' ∗
          e_t ⪯{Ω} e_s' [{ Φ }])) -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "Hsource". iApply sim_lift_prim_step_source.
    iIntros (????) "Hstate". iMod ("Hsource" with "Hstate") as (e_s' σ_s') "[% >Hstate]".
    iModIntro. iExists e_s', σ_s'. iFrame. iPureIntro. by apply head_prim_step.
  Qed.

  (* this lemma is useful because it only requires to re-establish the SI after
    stepping both in the target and the source *)
  Lemma sim_lift_head_step_both e_t e_s Φ:
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗
      ⌜head_reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' σ_t',
        ⌜head_step P_t e_t σ_t e_t' σ_t'⌝ ==∗
          ∃ e_s' σ_s', ⌜head_step P_s e_s σ_s e_s' σ_s'⌝ ∗
            state_interp P_t σ_t' P_s σ_s' ∗ e_t' ⪯{Ω} e_s' [{ Φ }]) -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "Hsim". iApply sim_step_target.
    iIntros (????) "[Hstate %Hnreach]". iMod ("Hsim" with "[$Hstate//]") as "(% & Hstep)".
    iModIntro. iSplitR. { iPureIntro. by eapply head_prim_reducible. }
    iIntros (e_t' σ_t') "%". iMod ("Hstep" with "[]") as (e_s' σ_s') "(% & Hstate & Hsim)".
    { iPureIntro. by eapply head_reducible_prim_step. }
    iModIntro. iExists e_s', σ_s'. iFrame. iPureIntro.
    econstructor; first by eapply head_prim_step. constructor.
  Qed.

  (** Stuckness *)
  Lemma source_stuck_prim ϕ e_s Ψ :
    (∀ P_s σ_s, SIrreducible ϕ P_s e_s σ_s) →
    ϕ →
    to_val e_s = None →
    ⊢ source_red e_s Ψ.
  Proof.
    intros Hirred Hp Hval. iApply source_red_stuck.
    iIntros (????) "_ !>". iPureIntro. split; first done.
    by intros e' σ' Hprim%Hirred.
  Qed.

  Lemma source_red_irred_unless ϕ e_s Ψ :
    (∀ P_s σ_s, IrredUnless ϕ P_s e_s σ_s) →
    to_val e_s = None →
    (⌜ϕ⌝ -∗ source_red e_s Ψ) -∗
    source_red e_s Ψ.
  Proof.
    intros Hunless Hval. iIntros "Hs".
    rewrite source_red_eq /flip source_red_unfold /source_red_rec.
    iIntros (????) "[Hstate %Hnreach]".
    assert (¬ irreducible P_s e_s σ_s) as Hn.
    { contradict Hnreach. exists e_s, σ_s. split; first constructor. done. }
    apply Hunless in Hn. iMod ("Hs" with "[//] [$Hstate //]") as "Hs"; done.
  Qed.

  Lemma sim_irred_unless ϕ e_s e_t Φ :
    (∀ P_s σ_s, IrredUnless ϕ P_s e_s σ_s) →
    to_val e_s = None →
    (⌜ϕ⌝ -∗ e_t ⪯ e_s [{ Φ }]) -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    intros Hunless Hval. iIntros "Hs".
    rewrite sim_expr_unfold.
    iIntros (????) "[Hstate %Hnreach]".
    assert (¬ irreducible P_s e_s σ_s) as Hn.
    { contradict Hnreach. exists e_s, σ_s. split; first constructor. done. }
    apply Hunless in Hn. iMod ("Hs" with "[//] [$Hstate //]") as "Hs"; done.
  Qed.

  (** Target eval *)
  Lemma target_red_lift_head_step Ψ e_t :
    ⊢ (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗
        (⌜ head_reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜head_step P_t e_t σ_t e_t' σ_t'⌝ ==∗
          state_interp P_t σ_t' P_s σ_s ∗ target_red e_t' Ψ)) -∗
      target_red e_t Ψ.
  Proof.
    iIntros "Htarget". iApply target_red_step. iIntros (????) "Hstate".
    iMod ("Htarget" with "Hstate") as "(%Hred & Hstep)". iModIntro.
    iSplitR. { iPureIntro. by apply head_prim_reducible. }
    iIntros (e_t' σ_t') "%Hprim". iApply "Hstep".
    iPureIntro. by apply head_reducible_prim_step.
  Qed.

  (** source eval *)
  Lemma source_red_lift_head_step Ψ e_s :
   ⊢ (∀ P_s σ_s P_t σ_t,
       state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗ ∃ e_s' σ_s',
          ⌜head_step P_s e_s σ_s e_s' σ_s'⌝ ∗
          |==> state_interp P_t σ_t P_s σ_s' ∗ source_red e_s' Ψ) -∗
      source_red e_s Ψ.
  Proof.
    iIntros "Hsource". iApply source_red_step.
    iIntros (????) "[Hstate %Hnreach]".
    iMod ("Hsource" with "[$Hstate//]") as (e_s' σ_s') "[% >Hstate]".
    iModIntro. iExists e_s', σ_s'. iFrame. iPureIntro. by apply head_prim_step.
  Qed.

  (** Coinduction *)
  (** We have to give a "loop invariant" [inv] (that may assert ownership or say that e_t, e_s
      have a certain shape) that needs to be established initially and re-established each time
      we want to use the co-induction hypothesis.
   Alternatively, when we get to a point where [Φ] holds, we can break out of the co-induction.

   Thus, note that for this lemma it is crucial that we need not reduce to a value to get to the postcondition.

   In each step of the coinduction, we need to take a step in the source and target.
     Since we do not have any means to keep track of this in the simulation relation, this lemma
     requires to take steps in the beginning, before escaping to the simulation relation again.
  *)
  Lemma sim_lift_coind (inv : expr Λ → expr Λ → PROP) e_t e_s Φ :
    (□ ∀ e_t e_s P_t P_s σ_t σ_s,
      inv e_t e_s -∗ state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗
        ⌜reducible P_t e_t σ_t⌝ ∗
        ∀ e_t' σ_t',
          ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
          ∃ e_s' σ_s', ⌜prim_step P_s (e_s, σ_s) (e_s', σ_s')⌝ ∗
            state_interp P_t σ_t' P_s σ_s' ∗
            e_t' ⪯{Ω} e_s' [{ λ e_t'' e_s'', Φ e_t'' e_s'' ∨ inv e_t'' e_s'' }]) -∗
    inv e_t e_s -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
  (* FIXME: we have the same proof pattern here as for the bind lemma,
    where we need to repeat some parts of the proof for the nested leastfp induction.
    Surely there must be a way to capture this pattern and make the proofs more concise? *)
    iIntros "#Hstep Hinv".
    iApply (sim_expr_coind _ _ (λ e_t' e_s', inv e_t' e_s' ∨ e_t' ⪯{Ω} e_s' [{λ e_t'' e_s'', Φ e_t'' e_s'' ∨ inv e_t'' e_s'' }])%I); last by eauto.
    iModIntro. clear e_t e_s. iIntros (e_t e_s) "[Hinv | Hs]".
    - rewrite /greatest_step least_def_unfold /least_step. iIntros (????) "[Hstate Hnreach]".
      iMod ("Hstep" with "Hinv [$Hstate $Hnreach ]") as "[Hred Hs]".
      iModIntro. iRight; iLeft. iFrame. iIntros (e_t' σ_t') "Hprim".
      iMod ("Hs" with "Hprim") as (e_s' σ_s') "(%Hprim & Hstate & Hs)".
      iModIntro. iRight. iExists e_s', σ_s'. iFrame. iPureIntro; by constructor.
    - rewrite {2}sim_expr_eq sim_expr_def_unfold.
      rewrite /greatest_step !least_def_unfold /least_step.
      iIntros (????) "[Hstate %Hnreach]". iMod ("Hs" with "[$Hstate //]") as "[Hs | [Hs | Hs]]".
      + (* when we have a "Red" there, we are really in the same situation again, so we take
          a step again, instead of going into the base case *)
        iDestruct "Hs" as (e_s' σ_s') "(%Hs_prim & Hstate & [Hbase | Hinv])".
        { (* base case -- mirror that in the goal *)
          iModIntro. iLeft. iExists e_s', σ_s'. by iFrame.
        }
        (* take a step using the hypothesis *)
        iRight; iLeft.
        iMod ("Hstep" with "Hinv [$Hstate]") as "[Hred Hs]".
        { iPureIntro. by eapply not_reach_stuck_pres_rtc. }
        iModIntro. iFrame. iIntros (e_t' σ_t') "Hprim".
        iMod ("Hs" with "Hprim") as (e_s'' σ_s'') "(%Hs_prim' & Hstate & Hs)".
        iModIntro. iRight. iExists e_s'', σ_s''. iFrame. iPureIntro.
        eapply tc_rtc_l; first done. by constructor.
      + iModIntro. iRight; iLeft. iDestruct "Hs" as "[Hred Hs]". iFrame "Hred".
        iIntros (e_t' σ_t') "Hprim". iMod ("Hs" with "Hprim") as "[Hstutter | Htstep]"; first last.
        { iModIntro. iRight. cbn. iDestruct "Htstep" as (e_s' σ_s') "(? & ? &?)".
          iExists e_s', σ_s'. rewrite sim_expr_eq. iFrame.
        }
        iModIntro. iLeft. iDestruct "Hstutter" as "[Hstate Hsim]". iFrame.
        iApply (sim_ind with "[] Hsim"). iModIntro. iIntros (e_t'').
        iIntros "IH". rewrite least_def_unfold.
        clear P_t σ_t e_t' σ_t' e_t Hnreach.
        iIntros (????) "[Hstate %Hnreach]". iMod ("IH" with "[$Hstate //]") as "[IH | [IH | IH]]".
        * (* same as above *)
          iDestruct "IH" as (e_s' σ_s') "(%Hs_prim & Hstate & [Hbase | Hinv])".
          { (* base case -- mirror that in the goal *)
            iModIntro. iLeft. iExists e_s', σ_s'. by iFrame.
          }
          (* take a step using the hypothesis *)
          iRight; iLeft.
          iMod ("Hstep" with "Hinv [$Hstate]") as "[Hred Hs]".
          { iPureIntro. by eapply not_reach_stuck_pres_rtc. }
          iModIntro. iFrame. iIntros (e_t' σ_t') "Hprim".
          iMod ("Hs" with "Hprim") as (e_s'' σ_s'') "(%Hs_prim' & Hstate & Hs)".
          iModIntro. iRight. iExists e_s'', σ_s''. iFrame. iPureIntro.
          eapply tc_rtc_l; first done. by constructor.
        * iDestruct "IH" as "[Hred IH]". iModIntro; iRight; iLeft. iFrame.
          iIntros (??) "Hprim". iMod ("IH" with "Hprim") as "[Hstutter | Htstep]".
          { iModIntro; iLeft. iFrame. }
          iModIntro; iRight. cbn. iDestruct "Htstep" as (e_s' σ_s') "(? & ? &?)".
          iExists e_s', σ_s'. rewrite sim_expr_eq. iFrame.
        * iRight; iRight. iDestruct "IH" as (f K_t v_t K_s v_s σ_s') "(-> & ? & ? & ? & Hs)".
          iExists f, K_t, v_t, K_s, v_s, σ_s'. iFrame. iModIntro. iSplitR; first done.
          iIntros (??) "Ho"; cbn. iRight. rewrite sim_expr_eq. by iApply "Hs".
      + iRight; iRight. iDestruct "Hs" as (f K_t v_t K_s v_s σ_s') "(-> & ? & ? & ? & Hs)".
        iExists f, K_t, v_t, K_s, v_s, σ_s'. iFrame. iModIntro. iSplitR; first done.
        iIntros (??) "Ho"; cbn. iRight. rewrite sim_expr_eq. by iApply "Hs".
  Qed.

  Lemma sim_lift_head_coind (inv : expr Λ → expr Λ → PROP) e_t e_s Φ :
    (□ ∀ e_t e_s P_t P_s σ_t σ_s,
      inv e_t e_s -∗ state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗
        ⌜head_reducible P_t e_t σ_t⌝ ∗
        ∀ e_t' σ_t',
          ⌜head_step P_t e_t σ_t e_t' σ_t'⌝ ==∗
          ∃ e_s' σ_s', ⌜head_step P_s e_s σ_s e_s' σ_s'⌝ ∗
            state_interp P_t σ_t' P_s σ_s' ∗
            e_t' ⪯{Ω} e_s' [{ λ e_t'' e_s'', Φ e_t'' e_s'' ∨ inv e_t'' e_s'' }]) -∗
    inv e_t e_s -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "#Ha Hinv". iApply (sim_lift_coind with "[] Hinv").
    iModIntro. iIntros (??????) "Hinv [Hstate %Hnreach]".
    iMod ("Ha" with "Hinv [$Hstate//]") as "[%Hred Hs]". iModIntro.
    iSplitR. { iPureIntro. by apply head_prim_reducible. }
    iIntros (??) "%Hprim". iMod ("Hs" with "[]") as (e_s' σ_s') "(%Hhead & Hstate & Hs)".
    { iPureIntro. by apply head_reducible_prim_step. }
    iModIntro. iExists e_s', σ_s'. iFrame. iPureIntro. by apply head_prim_step.
  Qed.


  (** The following lemma (which one might expect, given how cofix in Coq
      and guarded recursion in Iris work) should not be provable:
      It requires us to conjure up a proof that that any acceptable expressions by inv
      are in the simulation relation.
      While we only get that after already having taken a step in source and target, thus justifying soundness, it still requires us to produce this proof without having seen the "full" co-inductive step, which should lead us to two expressions related by inv again.
      If we fix the statement such that we only get the full coinduction hypothesis after having shown the full step "to the next iteration", we exactly arrive at the above statement [sim_lift_coind].

      (but I still think this should be a sound co-induction principle: we'd just need a way "to look into the future" to justify it).
   *)
  Lemma sim_lift_coind' (inv : expr Λ → expr Λ → PROP) e_t e_s Φ :
    (□ ∀ e_t e_s P_t P_s σ_t σ_s,
      inv e_t e_s -∗ state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗
        ⌜reducible P_t e_t σ_t⌝ ∗
        ∀ e_t' σ_t',
          ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
          ∃ e_s' σ_s', ⌜prim_step P_s (e_s, σ_s) (e_s', σ_s')⌝ ∗
            state_interp P_t σ_t' P_s σ_s' ∗
            ((∀ e_t' e_s', inv e_t' e_s' -∗ e_t' ⪯{Ω} e_s' [{ Φ }]) -∗
            e_t' ⪯{Ω} e_s' [{ λ e_t'' e_s'', Φ e_t'' e_s'' }])) -∗
    inv e_t e_s -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
  Abort.
End fix_sim.
