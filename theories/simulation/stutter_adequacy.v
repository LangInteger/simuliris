From iris Require Import bi.bi bi.lib.fixpoint.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import relations language slsls.


(* The adequacy proof proceeds in three steps:
   1. We combine all local simulations to one global simulation in Iris
   2. We obtain a meta level simultation by using satisfiability
   3. We prove that the meta level simultation implies a behavioral refinement
*)

Section fix_lang.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.

  Context {Λ : language}.
  Context {s : SimulLang PROP Λ}.

  Implicit Types
    (e_s e_t e : expr Λ)
    (P_s P_t P : prog Λ)
    (σ_s σ_t σ : state Λ)
    (Φ Ψ : val Λ → val Λ → PROP).

  Local Existing Instance sim_stutter.

Section global.

  Definition least_step (Φ : val Λ → val Λ → PROP) (greatest_rec : exprO → exprO → PROP) (e_s : exprO) (least_rec : exprO → PROP) (e_t : exprO) :=
    (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ -∗ |==>
      (* value case *)
      (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')⌝ ∗
        state_interp P_t σ_t P_s σ_s' ∗ Φ v_t v_s)

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
        (* stuttering *)
        (state_interp P_t σ_t' P_s σ_s ∗ least_rec e_t') ∨
        (* take a step *)
        (∃ e_s' σ_s', ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗ greatest_rec e_s' e_t'))
    )%I.

  Lemma least_step_mon Φ l1 l2 g1 g2 e_s:
    ⊢ <pers> (∀ e, l1 e -∗ l2 e)
    → <pers> (∀ e_s e_t, g1 e_s e_t -∗ g2 e_s e_t)
    → ∀ e, least_step Φ g1 e_s l1 e -∗ least_step Φ g2 e_s l2 e.
  Proof.
    iIntros "#H #H0" (e) "Hl". rewrite /least_step. iIntros (P_t σ_t P_s σ_s) "Ha".
    iMod ("Hl" with "Ha") as "[Hval | Hstep]"; iModIntro.
    + iLeft. iApply "Hval".
    + iRight. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ H1]". by iApply "H". }
      iRight. iDestruct "Hstep" as (e_s' σ_s') "(H1& H2 &H3)".
      iExists (e_s'), (σ_s'). iFrame. by iApply "H0".
  Qed.

  Instance least_step_mono (Φ : val Λ → val Λ → PROP) (greatest_rec : exprO → exprO → PROP) (e_s : exprO) :
    BiMonoPred (least_step Φ greatest_rec e_s).
  Proof.
    constructor.
    - intros l1 l2. iIntros "H". iApply (least_step_mon Φ l1 l2 greatest_rec greatest_rec e_s with "H").
      eauto.
    - intros l Hne n e1 e2 Heq.
      apply discrete_iff in Heq as ->. reflexivity. apply _.
  Qed.

  Definition least_def (Φ : val Λ → val Λ → PROP) (greatest_rec : exprO → exprO → PROP) (e_s : exprO) :=
    bi_least_fixpoint (least_step Φ greatest_rec e_s).

  Lemma least_def_ind greatest_rec (e_s : exprO) Φ (Ψ : exprO → PROP):
    Proper ((≡) ==> (≡)) Ψ →
    ⊢ (□ ∀ e_t, least_step Φ greatest_rec e_s Ψ e_t -∗ Ψ e_t)
      -∗ ∀ e_t : exprO, least_def Φ greatest_rec e_s e_t -∗ Ψ e_t.
  Proof. iIntros (Hp) "#H". iApply least_fixpoint_ind. iModIntro. iIntros (e_t) "IH". by iApply "H". Qed.


  Lemma least_def_unfold (Φ : val Λ → val Λ → PROP) (greatest_rec : exprO → exprO → PROP) (e_s : exprO) e_t:
    least_def Φ greatest_rec e_s e_t ⊣⊢ least_step Φ greatest_rec e_s (least_def Φ greatest_rec e_s) e_t.
  Proof. by rewrite /least_def least_fixpoint_unfold. Qed.

  Definition greatest_step (Φ : val Λ → val Λ → PROP) (greatest_rec : exprO * exprO → PROP) '(e_s, e_t) :=
    least_def Φ (uncurry greatest_rec) e_s e_t.

  Instance greatest_step_proper Φ greatest_rec:
    Proper ((≡) ==> (≡)) (greatest_step Φ greatest_rec).
  Proof. solve_proper. Qed.

  Lemma least_def_mon Φ g1 g2 e_s:
    ⊢ <pers> (∀ p, g1 p -∗ g2 p) → ∀ e, least_def Φ (uncurry g1) e_s e -∗ least_def Φ (uncurry g2) e_s e.
  Proof.
    iIntros "#H".
    rewrite /least_def.
    iApply (least_fixpoint_ind (least_step Φ (uncurry g1) e_s) (bi_least_fixpoint (least_step Φ (uncurry g2) e_s))).
    iModIntro. iIntros (e).
    rewrite least_fixpoint_unfold. iIntros "H0". iApply (least_step_mon Φ _ _ (uncurry g1) (uncurry g2) e_s).
    - eauto.
    - iModIntro. iIntros (? ?). rewrite /uncurry. by iApply "H".
    - iApply "H0".
  Qed.

  Instance greatest_step_mono (Φ : val Λ → val Λ → PROP) :
    BiMonoPred (greatest_step Φ).
  Proof.
    constructor.
  - intros g1 g2.
    iIntros "#H" ([e_s e_t]) "Hg". rewrite /greatest_step. iApply least_def_mon; eauto.
  - intros g Hne n [e_s e_t] [e_s' e_t'] Heq. apply discrete_iff in Heq as [-> ->].
    reflexivity. apply _.
  Qed.

  Definition gsim_def (Φ : val Λ → val Λ → PROP) :=
    bi_greatest_fixpoint (greatest_step Φ).

  Lemma gsim_def_unfold Φ e_s e_t:
    gsim_def Φ (e_s, e_t) ⊣⊢ greatest_step Φ (gsim_def Φ) (e_s, e_t).
  Proof. by rewrite /gsim_def greatest_fixpoint_unfold. Qed.

  Lemma gsim_def_least_def_unfold Φ e_s e_t :
    gsim_def Φ (e_s, e_t) ⊣⊢ least_def Φ (uncurry (gsim_def Φ)) e_s e_t.
  Proof. by rewrite gsim_def_unfold. Qed.

  Definition gsim_aux : seal (λ e_t e_s Φ, @gsim_def Φ (e_s, e_t)). by eexists. Qed.
  Definition gsim := ((gsim_aux).(unseal)).
  Definition gsim_eq : gsim = λ e_t e_s Φ, @gsim_def Φ (e_s, e_t). by rewrite <- (gsim_aux).(seal_eq). Defined.

  Lemma gsim_unfold Φ e_t e_s:
    gsim e_t e_s Φ ⊣⊢
    (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ -∗ |==>
      (* value case *)
        (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')⌝ ∗
          state_interp P_t σ_t P_s σ_s' ∗ Φ v_t v_s)

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
        (state_interp P_t σ_t' P_s σ_s ∗ gsim e_t' e_s Φ) ∨
        (∃ e_s' σ_s', ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗
        gsim e_t' e_s' Φ))
    )%I.
  Proof.
    rewrite !gsim_eq /uncurry gsim_def_unfold /greatest_step.
    rewrite least_def_unfold /least_step.
    by setoid_rewrite <-gsim_def_least_def_unfold.
  Qed.
End global.

Section local_to_global.

  Definition local_rel P_t P_s : PROP :=
    (□ ∀ f K_s, ⌜P_s !! f = Some K_s⌝ → ∃ K_t, ⌜P_t !! f = Some K_t⌝ ∗ sim_ectx K_t K_s val_rel)%I.
  Typeclasses Opaque local_rel.

  Global Instance local_rel_persistent P_s P_t : Persistent (local_rel P_s P_t).
  Proof. rewrite /local_rel; apply _. Qed.

  Lemma gsim_coind Φ (Ψ : exprO → exprO → PROP):
    Proper ((≡) ==> (≡) ==> (≡)) Ψ →
    ⊢ (□ ∀ e_t e_s, Ψ e_t e_s -∗ greatest_step Φ (λ '(e_s, e_t), Ψ e_t e_s) (e_s, e_t))
      -∗ ∀ e_t e_s, Ψ e_t e_s -∗ gsim e_t e_s Φ.
  Proof.
    iIntros (Hp) "#H". iIntros (e_t e_s) "H0".
    rewrite gsim_eq /gsim_def.

    set (Ψ_curry := (λ '(e_t, e_s), Ψ e_s e_t)).
    assert (NonExpansive Ψ_curry) as Hne.
    { intros ? [e1 e2] [e1' e2'] [H1 H2]. rewrite /Ψ_curry. cbn in H1, H2.
      apply equiv_dist, Hp. now apply discrete_iff in H1. now apply discrete_iff in H2.
    }
    iApply (greatest_fixpoint_coind (greatest_step Φ) Ψ_curry).
    { iModIntro. iIntros ([e_s' e_t']). iApply "H". }
    iApply "H0".
  Qed.

  Lemma local_to_global P_t P_s e_t e_s:
    local_rel P_t P_s -∗
    progs_are P_t P_s  -∗
    sim (Sim:=sim_stutter) e_t e_s val_rel -∗
    gsim e_t e_s val_rel.
  Proof.
    iIntros "#Hloc #Hprog Hsim".
    iApply (gsim_coind val_rel (λ e_t e_s, sim (Sim:=sim_stutter) e_t e_s val_rel) with "[] Hsim"); clear e_t e_s.
    iModIntro. iIntros (e_t e_s).
    rewrite /greatest_step sim_eq sim_def_unfold /slsls.greatest_step.
    iRevert (e_t). iApply sim_ind. iModIntro. iIntros (e_t).
    rewrite /slsls.least_step least_def_unfold /least_step.
    iIntros "Hsim" (P_t' σ_t P_s' σ_s) "[Hstate %]".
    rewrite /progs_are; iDestruct ("Hprog" with "Hstate") as "[% %]"; subst P_t' P_s'.
    iMod ("Hsim" with "[$Hstate //]") as "[Hsim|[Hsim|Hsim]]"; iModIntro; [by eauto..|].
    iDestruct "Hsim" as (f K_t v_t K_s v_s σ_s') "(% & % & Hval & Hstate & Hcont)".
    subst e_t. iRight.

    (* the function is in the source table *)
    edestruct (@not_stuck_call_in_prg Λ) as [K_f_s Hdef_s]; [by eauto..|].

    (* we prove reducibility and the step relation *)
    iSplit.
    - iAssert (∃ K_f_t, ⌜P_t !! f = Some K_f_t⌝)%I as (K_f_t) "%".
      { rewrite /local_rel; iDestruct ("Hloc" $! _ _ Hdef_s) as (K_f_t) "[% _]"; by eauto. }
      iPureIntro. eexists _, _.
      by apply fill_prim_step, head_prim_step, call_head_step_intro.
    - iIntros (e_t' σ_t' Hstep).
      apply prim_step_call_inv in Hstep as (K_f_t & Hdef & -> & ->).
      iModIntro. iRight. iExists (fill K_s (fill K_f_s (of_val v_s))), σ_s'.
      iFrame. iSplit.
      + iPureIntro. eapply tc_rtc_l; first by eauto.
        constructor. by apply fill_prim_step, head_prim_step, call_head_step_intro.
      + rewrite /uncurry. iPoseProof (sim_bind _ _ K_t K_s val_rel with "[Hval Hcont]") as "HP"; last first.
        { rewrite sim_eq; iApply "HP". }
        iApply (sim_mono with "[Hcont] [Hval]").
        * rewrite sim_eq. iExact "Hcont".
        * rewrite /local_rel; iDestruct ("Hloc" $! _ _ Hdef_s) as (K_f_t') "[% Hcont]".
          assert (K_f_t' = K_f_t) as -> by naive_solver.
          iSpecialize ("Hcont" with "Hval").
          by iApply "Hcont".
  Qed.

End local_to_global.

End fix_lang.
Typeclasses Opaque local_rel.


Section meta_level_simulation.

  Context {PROP : bi}.
  Context {Λ : language}.
  Context {s : SimulLang PROP Λ}.
  Context {PROP_bupd : BiBUpd PROP}.
  Context {PROP_affine : BiAffine PROP}.
  Context {sat: PROP → Prop} {Sat: Satisfiable sat}.
  Arguments sat _%I.

  Variable (P_t P_s: prog Λ).

  (* we pull out the simulation to a meta-level simulation *)
  Definition Sim (e_t: expr Λ) (σ_t: state Λ) (e_s: expr Λ) (σ_s: state Λ) :=
    sat (state_interp P_t σ_t P_s σ_s ∗ gsim e_t e_s val_rel).

  (* unfolding of the first case *)
  Lemma Sim_val (v_t: val Λ) (e_s: expr Λ) (σ_t σ_s: state Λ):
    Sim (of_val v_t) σ_t e_s σ_s →
    ¬ reach_stuck P_s e_s σ_s →
    ∃ v_s σ_s', rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s') ∧ sat (state_interp P_t σ_t P_s σ_s' ∗ val_rel v_t v_s).
  Proof.
    rewrite /Sim gsim_unfold; intros Hsat Hreach.
    eapply sat_mono with (Q:= (|==> _)%I) in Hsat; last first.
    { iIntros "[Hσ Hsim]". iMod ("Hsim" with "[$Hσ //]") as "Hsim". iExact "Hsim". }
    eapply sat_bupd in Hsat.
    eapply sat_or in Hsat as [Hsat|Hsat]; last first.
    { eapply sat_sep in Hsat as [Hsat _].
      eapply sat_elim in Hsat as [e [σ [] % val_prim_step]]. }
    eapply sat_exists in Hsat as [v_t' Hsat].
    eapply sat_exists in Hsat as [v_s Hsat].
    eapply sat_exists in Hsat as [σ_s' Hsat].
    eapply sat_sep in Hsat as [Heq % sat_elim Hsat].
    eapply sat_sep in Hsat as [Hrtc % sat_elim Hsat].
    rewrite to_of_val in Heq; injection Heq as <-.
    exists v_s, σ_s'; split; auto.
  Qed.

  (* unfolding of the second case, ignoring lfp *)
  Lemma Sim_step (e_t e_t' e_s: expr Λ) (σ_t σ_t' σ_s: state Λ):
    Sim e_t σ_t e_s σ_s →
    ¬ reach_stuck P_s e_s σ_s →
    prim_step P_t (e_t, σ_t) (e_t', σ_t') →
    ∃ e_s' σ_s', rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s') ∧ Sim e_t' σ_t' e_s' σ_s'.
  Proof.
    rewrite /Sim gsim_unfold; intros Hsat Hreach Hstep.
    eapply sat_mono with (Q:= (|==> _)%I) in Hsat; last first.
    { iIntros "[Hσ Hsim]". iMod ("Hsim" with "[$Hσ //]") as "Hsim". iExact "Hsim". }
    eapply sat_bupd in Hsat.
    eapply sat_or in Hsat as [Hsat|Hsat].
    { eapply sat_exists in Hsat as [v_t' Hsat].
      eapply sat_exists in Hsat as [v_s Hsat].
      eapply sat_exists in Hsat as [σ_s' Hsat].
      eapply sat_sep in Hsat as [Heq % sat_elim _].
      exfalso; eapply val_prim_step.
      by rewrite -(of_to_val _ _ Heq) in Hstep. }
    eapply sat_sep in Hsat as [_ Hsat].
    do 2 eapply sat_forall in Hsat.
    eapply sat_wand in Hsat; last by iPureIntro.
    eapply sat_bupd in Hsat.
    eapply sat_or in Hsat as [Hsat|Hsat].
    - eauto using rtc_refl.
    - eapply sat_exists in Hsat as [e_s' Hsat].
      eapply sat_exists in Hsat as [σ_s' Hsat].
      eapply sat_sep in Hsat as [Htc % sat_elim Hsat].
      exists e_s', σ_s'; split; auto using tc_rtc.
  Qed.

  (* we don't have a proof for the extraction of the least fixpoint itself *)
  Lemma Sim_src_step (e_t e_s: expr Λ) (σ_t σ_s: state Λ):
    Sim e_t σ_t e_s σ_s →
    ¬ reach_stuck P_s e_s σ_s →
    ex_loop (prim_step P_t) (e_t, σ_t) →
    ∃ e_t' σ_t' e_s' σ_s', tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s') ∧
    ex_loop (prim_step P_t) (e_t', σ_t') ∧ Sim e_t' σ_t' e_s' σ_s'.
  Proof.
    rewrite /Sim; intros Hsat Hreach Hstep.
    enough (sat (∃ (e_t' : expr Λ) (σ_t' : state Λ) (e_s' : expr Λ) (σ_s' : state Λ),
      ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗
      ⌜ex_loop (prim_step P_t) (e_t', σ_t')⌝ ∗
      state_interp P_t σ_t' P_s σ_s' ∗ gsim e_t' e_s' val_rel
    )) as Hsat'.
    { do 4 eapply sat_exists in Hsat' as [? Hsat'].
      do 2 eapply sat_sep in Hsat' as [? % sat_elim Hsat'].
      eauto 10.
    }
    eapply sat_bupd, sat_mono, Hsat.
    iIntros "[Hσ Hsim]". rewrite {1}gsim_eq gsim_def_unfold /greatest_step.
    clear Hsat. iRevert (σ_t Hstep) "Hσ".
    (* the strengthened induction *)
    iApply (least_def_ind _ _ _ (λ e_t, ∀ a : state Λ,
          ⌜ex_loop (prim_step P_t) (e_t, a)⌝
          → state_interp P_t a P_s σ_s
          -∗ |==> ∃ (e_t' : expr Λ) (σ_t' : state Λ) (e_s' : expr Λ)  (σ_s' : state Λ),
              ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝
            ∗ ⌜ex_loop (prim_step P_t) (e_t', σ_t')⌝
            ∗ state_interp P_t σ_t' P_s σ_s' ∗ gsim e_t' e_s' val_rel)%I with "[] Hsim"); clear e_t.
    iModIntro. rewrite /least_step. iIntros (e_t) "Hsim". iIntros (σ_t Hdiv) "SI".
    iMod ("Hsim" with "[$SI //]") as "[Hsim|Hsim]".
    - iExFalso. iDestruct "Hsim" as (v_t v_s σ_s' Hval) "_".
      apply ex_loop_pair_inv in Hdiv as (e_t' & σ_t' & Hstep & _).
      exfalso; eapply val_prim_step.
      by rewrite -(of_to_val _ _ Hval) in Hstep.
    - iDestruct "Hsim" as "[_ Hsim]".
      apply ex_loop_pair_inv in Hdiv as (e_t' & σ_t' & Hstep & Hdiv).
      iMod ("Hsim" $! _ _ Hstep) as "[Hsim|Hsim]".
      + iDestruct "Hsim" as "[SI IH]".
        by iMod ("IH" with "[//] SI").
      + iDestruct "Hsim" as (e_s' σ_s' Htc) "[SI Hsim]".
        iModIntro; iExists _, _, _, _; iFrame; iSplit; first by eauto.
        iSplit; first by eauto. rewrite gsim_eq. iApply "Hsim".
  Qed.

  (* progress *)
  Lemma Sim_progress (e_t e_s: expr Λ) (σ_t σ_s: state Λ):
    Sim e_t σ_t e_s σ_s →
    ¬ reach_stuck P_s e_s σ_s →
    ¬ stuck P_t e_t σ_t.
  Proof.
    rewrite /Sim gsim_unfold; intros Hsat Hreach Hstuck.
    eapply sat_mono with (Q:= (|==> _)%I) in Hsat; last first.
    { iIntros "[Hσ Hsim]". iMod ("Hsim" with "[$Hσ //]") as "Hsim". iExact "Hsim". }
    eapply sat_bupd in Hsat.
    eapply sat_or in Hsat as [Hsat|Hsat].
    { eapply sat_exists in Hsat as [v_t' Hsat].
      eapply sat_exists in Hsat as [v_s Hsat].
      eapply sat_exists in Hsat as [σ_s' Hsat].
      eapply sat_sep in Hsat as [Heq % sat_elim _].
      unfold stuck in *; naive_solver. }
    eapply sat_sep in Hsat as [Hred % sat_elim _].
    by destruct Hstuck as [Hval Hirr % not_reducible].
  Qed.

End meta_level_simulation.


Section simulation_behaviorally_related.

  Context {PROP : bi}.
  Context {Λ : language}.
  Context {s : SimulLang PROP Λ}.
  Context {PROP_bupd : BiBUpd PROP}.
  Context {PROP_affine : BiAffine PROP}.
  Context {sat: PROP → Prop} {Sat: Satisfiable sat}.
  Arguments sat _%I.

  Variable (P_t P_s: prog Λ).

  (* divergent case *)
  Lemma Sim_diverge' e_t e_s σ_t σ_s:
    Sim (sat := sat) P_t P_s e_t σ_t e_s σ_s →
    ¬ reach_stuck P_s e_s σ_s →
    ex_loop (prim_step P_t) (e_t, σ_t) →
    ex_loop (tc (prim_step P_s)) (e_s, σ_s).
  Proof.
    revert e_t e_s σ_t σ_s; cofix IH.
    intros e_s σ_s e_t σ_t Hsim Hstuck Hdiv.
    eapply Sim_src_step in Hsim as (e_t' & σ_t' & e_s' & σ_s' & Hsteps & Hloop & Hsim'); [|by auto..].
    econstructor; first apply Hsteps.
    eapply IH; eauto.
    eapply not_reach_stuck_pres_tc; eauto.
  Qed.

  Lemma Sim_diverge e_t e_s σ_t σ_s:
    Sim (sat:=sat) P_t P_s e_t σ_t e_s σ_s →
    ¬ reach_stuck P_s e_s σ_s →
    ex_loop (prim_step P_t) (e_t, σ_t) →
    ex_loop (prim_step P_s) (e_s, σ_s).
  Proof.
    eauto using Sim_diverge', ex_loop_tc.
  Qed.


  (* return value case *)
  Lemma Sim_steps e_t e_s σ_t σ_s e_t' σ_t':
    Sim (sat:=sat) P_t P_s e_t σ_t e_s σ_s →
    ¬ reach_stuck P_s e_s σ_s →
    rtc (prim_step P_t) (e_t, σ_t) (e_t', σ_t') →
    ∃ e_s' σ_s', rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s') ∧ Sim (sat:=sat) P_t P_s e_t' σ_t' e_s' σ_s'.
  Proof.
    intros Hsim Hstuck Hrtc; remember (e_t, σ_t) as tgt; remember (e_t', σ_t') as src.
    revert e_t e_t' e_s σ_t σ_t' σ_s Heqtgt Heqsrc Hsim Hstuck; induction Hrtc as [|? [e_t_mid σ_t_mid] ? Hstep ? IH];
    intros e_t e_t' e_s σ_t σ_t' σ_s Heqtgt Heqsrc Hsim Hstuck; subst.
    - exists e_s, σ_s; split; first reflexivity.
      naive_solver.
    - eapply Sim_step in Hsim as (e_s_mid & σ_s_mid & Htc & Hsim); [|by eauto..].
      edestruct IH as (e_s' & σ_s' & Hrtc' & Hsim'); [by eauto using not_reach_stuck_pres_rtc..|].
      eexists _, _; split; last done. etrans; eauto.
  Qed.

  Lemma Sim_return e_t e_s σ_t σ_s v_t σ_t':
    Sim (sat:=sat) P_t P_s e_t σ_t e_s σ_s →
    ¬ reach_stuck P_s e_s σ_s →
    rtc (prim_step P_t) (e_t, σ_t) (of_val v_t, σ_t') →
    ∃ v_s σ_s', rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')
    ∧ sat (state_interp P_t σ_t' P_s σ_s' ∗ val_rel v_t v_s).
  Proof.
    (* first we exectute the simulation to v_t *)
    intros Hsim Hstuck Htgt; eapply Sim_steps in Htgt as (e_s' & σ_s' & Hsrc & Hsim'); [|eauto..].
    (* then we use the value case to extract the source value *)
    eapply Sim_val in Hsim' as (v_s & σ_s'' & Hsteps & Hsat); last by eauto using not_reach_stuck_pres_rtc.
    eexists _, _; split; eauto using rtc_transitive.
  Qed.

  (* undefined behavior *)
  Lemma Sim_safety e_t e_s σ_t σ_s:
    Sim (sat:=sat) P_t P_s e_t σ_t e_s σ_s →
    ¬ reach_stuck P_s e_s σ_s →
    ¬ reach_stuck P_t e_t σ_t.
  Proof.
    intros Hsim Hnstuck (e_t' & σ_t' & Hrtc & Hstuck).
    eapply Sim_steps in Hsim as (e_s' & σ_s' & Hsteps & Hsim); [|by eauto..].
    eapply Sim_progress; eauto using not_reach_stuck_pres_rtc.
  Qed.


End simulation_behaviorally_related.




Section adequacy_statement.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language}.
  Context {s : SimulLang PROP Λ}.
  Context {sat: PROP → Prop} {Sat: Satisfiable sat}.
  Arguments sat _%I.

  Variable (I: state Λ → state Λ → Prop).
  Variable (O: val Λ → val Λ → Prop).
  Variable (main: string) (u: val Λ).

  Definition B (P_t P_s: prog Λ) :=
    ∀ σ_t σ_s, I σ_t σ_s ∧ ¬ reach_stuck P_s (of_call main u) σ_s →
    (* divergent case *)
    (ex_loop (prim_step P_t) (of_call main u, σ_t) → ex_loop (prim_step P_s) (of_call main u, σ_s)) ∧
    (* convergent case *)
    (∀ v_t σ_t', rtc (prim_step P_t) (of_call main u, σ_t) (of_val v_t, σ_t') →
    ∃ v_s σ_s', rtc (prim_step P_s) (of_call main u, σ_s) (of_val v_s, σ_s') ∧ O v_t v_s) ∧
    (* safety *)
    (¬ reach_stuck P_t (of_call main u) σ_t).

  Lemma adequacy P_t P_s:
    (* pre *)
    sat (local_rel (s := s) P_t P_s ∗
      (∀ σ_t σ_s, ⌜I σ_t σ_s⌝ -∗ state_interp P_t σ_t P_s σ_s) ∗
      progs_are P_t P_s ∗
      val_rel u u) →
    (* post *)
    (∀ v_t v_s σ_t σ_s, sat (state_interp P_t σ_t P_s σ_s ∗ val_rel (SimulLang := s) v_t v_s) → O v_t v_s) →
    B P_t P_s.
  Proof.
    intros Hpre Hpost σ_t σ_s [HI Hstuck].
    edestruct (not_stuck_call_in_prg P_s main empty_ectx) as [K_s Hsrc]; first done.
    { by rewrite fill_empty. }
    eapply sat_mono with (Q := (state_interp P_t σ_t P_s σ_s ∗ gsim (of_call main u) (of_call main u) val_rel)%I) in Hpre;
      first fold (Sim (sat:=sat) P_t P_s (of_call main u) σ_t (of_call main u) σ_s) in Hpre; last first.
    - iIntros "(#HL & HI & #Hprogs & Hval)".
      iSplitL "HI"; first by iApply "HI".
      iApply (local_to_global with "HL Hprogs").
      unfold local_rel; iDestruct ("HL" $! _ _ Hsrc) as (K_tgt Htgt) "Hsim'".
      iPoseProof (intuitionistically_elim with "Hsim'") as "Hsim".
      iApply sim_call_inline; last iFrame "Hsim Hval Hprogs"; by auto.
    - split; [|split].
      + by eapply Sim_diverge.
      + intros v_t σ_t' Hsteps_tgt.
        edestruct Sim_return as (v_s & σ_s' & Hsteps_src & Hsat); by eauto.
      + by eapply Sim_safety.
  Qed.

End adequacy_statement.

Section adequacy_statement_alt.

  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language}.
  Context {s : SimulLang PROP Λ}.
  Context {sat: PROP → Prop} {Sat: Satisfiable sat}.
  Arguments sat _%I.

  Variable (I: state Λ → state Λ → Prop).
  Variable (O: val Λ → val Λ → Prop).
  Variable (main: string) (u: val Λ).

  Lemma adequacy_alt P_t P_s:
    sat (local_rel (s := s) P_t P_s ∗
      (∀ σ_t σ_s, ⌜I σ_t σ_s⌝ -∗ state_interp P_t σ_t P_s σ_s) ∗
      progs_are P_t P_s ∗
      val_rel u u ∗
      ∀ v_s v_t, val_rel (SimulLang := s) v_t v_s -∗ ⌜O v_t v_s⌝) →
    B I O main u P_t P_s.
  Proof.
    intros Hsat. eapply sat_frame_intro in Hsat; last first.
    { iIntros "(H1 & H2 & H3 & H4 & F)". iSplitL "F"; first iExact "F".
      iCombine "H1 H2 H3 H4" as "H". iExact "H". }
    eapply (@adequacy PROP _ _ _ _ _ (sat_frame _) _); first apply Hsat.
    intros v_t v_s σ_t σ_s Hsat_post. eapply sat_elim, sat_mono, Hsat_post.
    iIntros "(H & _ & Hval)". by iApply "H".
  Qed.

End adequacy_statement_alt.

