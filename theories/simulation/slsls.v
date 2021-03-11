(** * SLSLS, Separation Logic Stuttering Local Simulation *)

From iris.bi Require Import bi lib.fixpoint.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import relations language.
From simuliris.simulation Require Export simulation.
From iris.prelude Require Import options.
Import bi.

(* TODO @LG: cleanup this file, check which lemmas belong here and which should be moved somewhere else.
  e.g. should the source_red + source_stutter judgments stay here (they could also be used with the nostutter relation)?
*)

Section fix_lang.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language}.
  Context {s : SimulLang PROP Λ}.

  Set Default Proof Using "Type*".

  Implicit Types
    (e_s e_t e: expr Λ)
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ).

  (** Simulation relation with stuttering *)

  Section sim_def.
  Context (val_rel : val Λ → val Λ → PROP).
  Definition least_step Φ (greatest_rec : exprO → exprO → PROP) e_s
      (least_rec : exprO → PROP) e_t :=
    (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ -∗ |==>
      (* value case *)
      (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗
        ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')⌝ ∗
        state_interp P_t σ_t P_s σ_s' ∗ Φ v_t v_s)

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
        (* stuttering *)
        (state_interp P_t σ_t' P_s σ_s ∗ least_rec e_t') ∨
        (* take a step *)
        (∃ e_s' σ_s', ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗
          state_interp P_t σ_t' P_s σ_s' ∗ greatest_rec e_s' e_t'))

      ∨ (* call case *)
      (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
        ⌜rtc (prim_step P_s) (e_s, σ_s) (fill K_s (of_call f v_s), σ_s')⌝ ∗
        val_rel v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
        (∀ v_t v_s, val_rel v_t v_s -∗ greatest_rec (fill K_s (of_val v_s)) (fill K_t (of_val v_t))))
    )%I.

  Lemma least_step_mon Φ l1 l2 g1 g2 e_s:
    ⊢ □ (∀ e, l1 e -∗ l2 e)
    → □ (∀ e_s e_t, g1 e_s e_t -∗ g2 e_s e_t)
    → ∀ e, least_step Φ g1 e_s l1 e -∗ least_step Φ g2 e_s l2 e.
  Proof.
    iIntros "#H #H0" (e) "Hl". rewrite /least_step. iIntros (P_t σ_t P_s σ_s) "Ha".
    iMod ("Hl" with "Ha") as "[Hval | [Hstep | Hcall]]"; iModIntro.
    + iLeft. iApply "Hval".
    + iRight; iLeft. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ H1]". by iApply "H". }
      iRight. iDestruct "Hstep" as (e_s' σ_s') "(H1& H2 &H3)".
      iExists (e_s'), (σ_s'). iFrame. by iApply "H0".
    + iRight; iRight. iDestruct "Hcall" as (f K_t v_t K_s v_s σ_s') "(H1& H2& H3& H4&H5)".
      iExists (f), (K_t), (v_t), (K_s), (v_s), (σ_s'). iFrame.
      iIntros (? ?) "H1". iApply "H0". by iApply "H5".
  Qed.

  Instance least_step_mono Φ greatest_rec e_s :
    BiMonoPred (least_step Φ greatest_rec e_s).
  Proof.
    constructor.
    - intros l1 l2. iIntros "H".
      iApply (least_step_mon Φ l1 l2 greatest_rec greatest_rec e_s with "H").
      eauto.
    - intros l Hne n e1 e2 Heq.
      apply (discrete_iff _ _) in Heq as ->. done.
  Qed.

  Definition least_def Φ (greatest_rec : exprO → exprO → PROP) e_s :=
    bi_least_fixpoint (least_step Φ greatest_rec e_s).

  Lemma least_def_unfold Φ greatest_rec e_s e_t :
    least_def Φ greatest_rec e_s e_t ⊣⊢
      least_step Φ greatest_rec e_s (least_def Φ greatest_rec e_s) e_t.
  Proof. by rewrite /least_def least_fixpoint_unfold. Qed.

  Definition greatest_step Φ greatest_rec '(e_s, e_t) :=
    least_def Φ (uncurry greatest_rec) e_s e_t.

  Instance greatest_step_proper Φ greatest_rec :
    Proper ((≡) ==> (≡)) (greatest_step Φ greatest_rec).
  Proof. solve_proper. Qed.

  Lemma least_def_mon Φ g1 g2 e_s:
    □ (∀ p, g1 p -∗ g2 p) -∗
    ∀ e, least_def Φ (uncurry g1) e_s e -∗ least_def Φ (uncurry g2) e_s e.
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

  Instance greatest_step_mono Φ :
    BiMonoPred (greatest_step Φ).
  Proof.
    constructor.
  - intros g1 g2.
    iIntros "#H" ([e_s e_t]) "Hg". rewrite /greatest_step. iApply least_def_mon; eauto.
  - intros g Hne n [e_s e_t] [e_s' e_t'] Heq.
    apply (discrete_iff _ _) in Heq as [-> ->]. done.
  Qed.

  Definition sim_def Φ :=
    bi_greatest_fixpoint (greatest_step Φ).

  Lemma sim_def_unfold Φ e_s e_t:
    sim_def Φ (e_s, e_t) ⊣⊢ greatest_step Φ (sim_def Φ) (e_s, e_t).
  Proof. by rewrite /sim_def greatest_fixpoint_unfold. Qed.

  Lemma sim_def_least_def_unfold Φ e_s e_t :
    sim_def Φ (e_s, e_t) ⊣⊢ least_def Φ (uncurry (sim_def Φ)) e_s e_t.
  Proof. by rewrite sim_def_unfold. Qed.
  End sim_def.
  Implicit Types (Ω : val Λ → val Λ → PROP).

  Definition sim_aux : seal (λ Ω e_t e_s Φ, @sim_def Ω Φ (e_s, e_t)).
  Proof. by eexists. Qed.
  Global Instance sim_stutter : Sim s := (sim_aux).(unseal).
  Lemma sim_eq : sim (Sim:=sim_stutter) = λ Ω e_t e_s Φ, @sim_def Ω Φ (e_s, e_t).
  Proof. rewrite -sim_aux.(seal_eq) //. Qed.

  Lemma sim_unfold Ω Φ e_t e_s:
    sim (Sim:=sim_stutter) Ω e_t e_s Φ ⊣⊢
    (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ -∗ |==>
      (* value case *)
        (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')⌝ ∗
          state_interp P_t σ_t P_s σ_s' ∗ Φ v_t v_s)

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
        (state_interp P_t σ_t' P_s σ_s ∗ sim Ω e_t' e_s Φ) ∨
        (∃ e_s' σ_s', ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗
        sim Ω e_t' e_s' Φ))

      ∨ (* call case *)
      (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
        ⌜rtc (prim_step P_s) (e_s, σ_s) (fill K_s (of_call f v_s), σ_s')⌝ ∗
        Ω v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
        sim_ectx Ω K_t K_s Φ)
    )%I.
  Proof.
    rewrite /sim_ectx !sim_eq /uncurry sim_def_unfold /greatest_step.
    rewrite least_def_unfold /least_step.
    setoid_rewrite <-sim_def_least_def_unfold. done.
  Qed.

  (* any post-fixed point is included in the gfp *)
  Lemma sim_coind Ω Φ (Ψ : exprO → exprO → PROP) :
    Proper ((≡) ==> (≡) ==> (≡)) Ψ →
    ⊢ (□ ∀ e_t e_s, Ψ e_t e_s -∗ greatest_step Ω Φ (λ '(e_s, e_t), Ψ e_t e_s) (e_s, e_t))
      -∗ ∀ e_t e_s, Ψ e_t e_s -∗ sim Ω e_t e_s Φ.
  Proof.
    iIntros (Hp) "#H". iIntros (e_t e_s) "H0".
    rewrite sim_eq /sim_def.

    set (Ψ_curry := (λ '(e_t, e_s), Ψ e_s e_t)).
    assert (NonExpansive Ψ_curry) as Hne.
    { intros ? [e1 e2] [e1' e2'] [H1 H2]. rewrite /Ψ_curry. cbn in H1, H2.
      apply equiv_dist, Hp.
      - by apply (discrete_iff _ _) in H1.
      - by apply (discrete_iff _ _) in H2.
    }
    iApply (greatest_fixpoint_coind (greatest_step Ω Φ) Ψ_curry).
    { iModIntro. iIntros ([e_s' e_t']). iApply "H". }
    iApply "H0".
  Qed.

  Local Existing Instance least_step_mono.
  Local Existing Instance greatest_step_mono.
  (* TODO: not sure yet if this lemma is useful. if not, remove *)
  Lemma sim_strong_ind' Ω e_s Φ (Ψ : exprO → exprO → (val Λ → val Λ → PROP) → PROP):
    Proper ((≡) ==> (≡) ==> (pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> (≡)) Ψ →
    ⊢ (□ ∀ e_t, least_step Ω Φ (uncurry (sim_def Ω Φ)) e_s
            (λ e_t', Ψ e_t' e_s Φ ∧ least_def Ω Φ (uncurry (sim_def Ω Φ)) e_s e_t')
          e_t -∗ Ψ e_t e_s Φ)
      -∗ ∀ e_t : exprO, (e_t ⪯{Ω} e_s {{ Φ }}) -∗ Ψ e_t e_s Φ.
  Proof.
    iIntros (Hp) "#IH". iIntros (e_t).
    rewrite sim_eq /sim_def.
    rewrite greatest_fixpoint_unfold {2}/greatest_step /least_def.

    change (bi_greatest_fixpoint (greatest_step Ω Φ)) with (sim_def Ω Φ).
    set (g_rec := least_step Ω Φ (uncurry (sim_def Ω Φ)) e_s).

    set (Ψ' := (λ e_t, Ψ e_t e_s Φ) : exprO → PROP).
    iAssert ((□ (∀ e_t : exprO, g_rec (λ e_t' : exprO, Ψ' e_t' ∧ bi_least_fixpoint g_rec e_t') e_t -∗ Ψ' e_t)))%I as "#H".
    { iModIntro. iApply "IH". }
    iPoseProof (least_fixpoint_strong_ind g_rec Ψ' with "H") as "Htemp".
    unfold Ψ'. iApply "Htemp".
  Qed.

  (* TODO: not sure yet if this lemma is useful. if not, remove *)
  Lemma sim_ind' e_s Ω Φ (Ψ : exprO → exprO → (val Λ → val Λ → PROP) → PROP):
    Proper ((≡) ==> (≡) ==> (pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> (≡)) Ψ →
    ⊢ (□ ∀ e_t, least_step Ω Φ (uncurry (sim_def Ω Φ)) e_s (λ e_t', Ψ e_t' e_s Φ) e_t -∗ Ψ e_t e_s Φ)
      -∗ ∀ e_t : exprO, e_t ⪯{Ω} e_s {{ Φ }} -∗ Ψ e_t e_s Φ.
  Proof.
    iIntros (Hp) "#IH". iApply sim_strong_ind'. iModIntro.
    iIntros (e_t) "H". iApply "IH".
    iApply least_step_mon. 3: iApply "H". 2: auto.
    iModIntro. by iIntros (e) "[H _]".
  Qed.

  Lemma sim_strong_ind greatest_rec e_s Ω Φ (Ψ : exprO → PROP):
    Proper ((≡) ==> (≡)) Ψ →
    (□ ∀ e_t, least_step Ω Φ greatest_rec e_s
          (λ e_t', Ψ e_t' ∧ least_def Ω Φ greatest_rec e_s e_t')
      e_t -∗ Ψ e_t) -∗
    ∀ e_t : exprO, least_def Ω Φ greatest_rec e_s e_t -∗ Ψ e_t.
  Proof.
    iIntros (Hp) "#H". iApply least_fixpoint_strong_ind.
    iModIntro. iIntros (e_t) "IH". by iApply "H".
  Qed.

  Lemma sim_ind greatest_rec e_s Ω Φ (Ψ : exprO → PROP):
    Proper ((≡) ==> (≡)) Ψ →
    (□ ∀ e_t, least_step Ω Φ greatest_rec e_s Ψ e_t -∗ Ψ e_t) -∗
    ∀ e_t : exprO, least_def Ω Φ greatest_rec e_s e_t -∗ Ψ e_t.
  Proof.
    iIntros (Hp) "#H". iApply least_fixpoint_ind.
    iIntros "!>" (e_t) "IH". by iApply "H".
  Qed.

  Global Instance sim_proper :
    Proper ((pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> eq ==> eq ==>
      (pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> (≡)) sim.
  Proof.
    intros o1 o2 H e e' -> e1 e1' -> p1 p2 Heq2.
    rewrite !sim_eq. apply greatest_fixpoint_proper; last done.
    intros p3 [e3 e3']. rewrite /greatest_step /least_def.
    apply least_fixpoint_proper; last done. solve_proper.
  Qed.

  Lemma sim_value_target Ω Φ v_t e_s v_s:
    Φ v_t v_s -∗
    (∀ P_s σ_s, ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s)⌝) -∗
    (of_val v_t) ⪯{Ω} e_s {{Φ}}.
  Proof.
    iIntros "Hv Hr". rewrite sim_unfold. iIntros (????) "[Hstate Hreach]".
    iModIntro. iLeft. iExists (v_t), (v_s), (σ_s). iFrame.
    iSplitR; first by rewrite to_of_val. eauto.
  Qed.

  Lemma sim_value Ω Φ v_t v_s:
    ⊢ (Φ v_t v_s) -∗ (of_val v_t) ⪯{Ω} (of_val v_s) {{ Φ }}.
  Proof.
    iIntros "Hv". rewrite sim_unfold. iIntros (????) "[Hstate Hreach]".
    iModIntro. iLeft. iExists (v_t), (v_s), (σ_s). iFrame.
    iSplitL; first by rewrite to_of_val. eauto.
  Qed.

  (* FIXME(RJ) this lemma leaks implementation details? *)
  Lemma sim_stutter_incl Ω Φ e_s e_t:
    least_def Ω Φ (uncurry (sim_def Ω Φ)) e_s e_t -∗ e_t ⪯{Ω} e_s {{ Φ }}.
  Proof. iIntros "H". by rewrite sim_eq sim_def_unfold /greatest_step. Qed.

  Lemma bupd_sim Ω Φ e_t e_s:
    ⊢ (|==> e_t ⪯{Ω} e_s {{ Φ }}) -∗ e_t ⪯{Ω} e_s {{ Φ }}.
  Proof.
    iIntros "Hv". rewrite sim_unfold. iIntros (????) "H". iMod "Hv". iApply ("Hv" with "H").
  Qed.

  Lemma sim_bupd Ω Φ e_t e_s:
    (e_t ⪯{Ω} e_s {{ λ v_t v_s, |==> Φ v_t v_s }}) -∗ e_t ⪯{Ω} e_s {{ Φ }}.
  Proof.
    iIntros "Hv".
    iApply (sim_coind Ω Φ (λ e_t e_s, e_t ⪯{Ω} e_s {{λ v_t v_s, |==> Φ v_t v_s}})%I); last by iFrame.
    iModIntro. clear e_t e_s. iIntros (e_t e_s) "Hv".
    rewrite sim_unfold /greatest_step least_def_unfold /least_step.
    iIntros (????) "H". iMod ("Hv" with "H") as "Hv".
    iDestruct "Hv" as "[Hv | [H | H]]".
    - iDestruct "Hv" as (v_t v_s σ_s') "(H1 & H2 & H3 & >H4)".
      iModIntro. iLeft. iExists v_t, v_s, σ_s'. iFrame.
    - iModIntro. iRight; iLeft. iDestruct "H" as "[Hred H]"; iFrame.
      iIntros (??) "Hs". iMod ("H" with "Hs") as "[[? Hs] | Hs]"; iModIntro.
      + iLeft. iFrame.
        iApply sim_ind. 2: { rewrite sim_eq sim_def_least_def_unfold. iFrame. }
        iModIntro. clear e_t' P_t P_s σ_t' σ_t σ_s. iIntros (e_t') "IH".
        rewrite least_def_unfold !/least_step.
        iIntros (????) "H". iMod ("IH" with "H") as "Hv".
        iDestruct "Hv" as "[Hv | [H | H]]".
        * iDestruct "Hv" as (v_t v_s σ_s') "(H1 & H2 & H3 & >H4)".
          iModIntro. iLeft. iExists v_t, v_s, σ_s'. iFrame.
        * iModIntro. iRight; iLeft. iDestruct "H" as "[Hred H]"; iFrame.
          iIntros (??) "Hs". iMod ("H" with "Hs") as "[[? Hs] | Hs]"; iModIntro.
          { iLeft. iFrame. }
          iRight. rewrite sim_eq. iFrame.
        * iModIntro. iRight; iRight. rewrite sim_eq. iFrame.
      + iRight. iFrame.
    - iModIntro. iRight; iRight. iFrame.
  Qed.

  (* we change the predicate beause at every recursive ocurrence,
     we give back ownership of the monotonicity assumption *)
  Lemma least_def_mono rec Ω Φ Φ' :
    (∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) -∗
    ∀ e_s e_t,
    least_def Ω Φ rec e_s e_t -∗
    least_def Ω Φ' (λ e_s e_t, rec e_s e_t ∗ ∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) e_s e_t.
  Proof.
    iIntros "Hmon" (e_s e_t). iIntros "Hleast". iRevert "Hmon".
    iApply (sim_ind _ _ _ _ (λ e_t, (∀ v_t v_s : val Λ, Φ v_t v_s -∗ Φ' v_t v_s) -∗ least_def Ω Φ' (λ e_s e_t, rec e_s e_t ∗ ∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) e_s e_t)%I with "[] Hleast"); clear e_t.
    iModIntro. iIntros (e_t) "IH Hmon". rewrite least_def_unfold /least_step.
    iIntros (P_t σ_t P_s σ_s) "H". iMod ("IH" with "H") as "IH". iModIntro.
    iDestruct "IH" as "[Hval | [Hstep | Hcall]]".
    - iLeft. iDestruct "Hval" as (v_t v_s σ_s') "(?&?&?&?)".
      iExists v_t, v_s, σ_s'. iFrame. by iApply "Hmon".
    - iRight; iLeft. iDestruct "Hstep" as "[$ Hstep]".
      iIntros (e_t' σ_t' Hstep).
      iMod ("Hstep" with "[//]") as "[Hstep|Hstep]".
      + iModIntro. iLeft. iDestruct "Hstep" as "[$ H]". by iApply "H".
      + iModIntro. iRight. iFrame "Hmon". eauto.
    - iRight; iRight. by iFrame "Hmon".
  Qed.

  Lemma sim_mono Ω Φ Φ' :
    (∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) -∗
    ∀ e_s e_t : exprO, e_t ⪯{Ω} e_s {{ Φ }} -∗ e_t ⪯{Ω} e_s {{ Φ' }}.
  Proof.
    iIntros "Hmon" (e_s e_t) "H".
    iApply (sim_coind Ω Φ' (λ e_t e_s, e_t ⪯{Ω} e_s {{ Φ }} ∗ (∀ v_t v_s : val Λ, Φ v_t v_s -∗ Φ' v_t v_s))%I); last by iFrame.
    iModIntro. clear e_t e_s. iIntros (e_t e_s) "[H Hmon]".
    rewrite sim_eq sim_def_unfold.
    rewrite /greatest_step !least_def_unfold /least_step.
    iIntros (????) "Hs". iSpecialize ("H" with "Hs"). iMod "H". iModIntro.
    iDestruct "H" as "[Hval | [Hred | Hcall]]".
    - iLeft. iDestruct "Hval" as (v_t v_s σ_s') "(?&?&?&?)".
      iExists v_t, v_s, σ_s'. iFrame. by iApply "Hmon".
    - iRight; iLeft. iDestruct "Hred" as "[Hred Hstep]". iFrame.
      iIntros (e_t' σ_t') "Hprim".
      iMod ("Hstep" with "Hprim") as "[Hstutter | Hstep]"; iModIntro.
      + iLeft. iDestruct "Hstutter" as "[Hstate Hleast]". iFrame.
        by iApply (least_def_mono with "Hmon").
      + iRight. by iFrame.
    - iRight; iRight. iFrame.
  Qed.

  (* TODO: clean up the bind lemma proof *)
  (* coinduction predicate used for the bind lemma *)
  Definition bind_pred Ω Φ := uncurry (λ '(e_s, e_t), ∃ e_t' e_s' (K_t K_s : ectx Λ),
    ⌜e_t = fill K_t e_t'⌝ ∧ ⌜e_s = fill K_s e_s'⌝ ∧
     e_t' ⪯{Ω} e_s' {{ λ v_t v_s : val Λ, fill K_t (of_val v_t) ⪯{Ω} fill K_s (of_val v_s) {{ Φ }} }})%I.

  (* Lemma used two times in the proof of the bind lemma (for the value cases of the inner and outer induction) *)
  Lemma sim_bind_val Ω P_s e_s σ_s v_s σ_s' e_t v_t K_t σ_t P_t K_s Φ :
      rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s') →
      to_val e_t = Some v_t →
      (¬ reach_stuck P_s (fill K_s e_s) σ_s) →
      ⊢ fill K_t (of_val v_t) ⪯{Ω} fill K_s (of_val v_s) {{Φ}} -∗
        state_interp P_t σ_t P_s σ_s' -∗ |==>

        (* val case *)
        (∃ (v_t' v_s' : val Λ) σ_s'', ⌜to_val (fill K_t e_t) = Some v_t'⌝ ∗
          ⌜rtc (prim_step P_s) (fill K_s e_s, σ_s) (of_val v_s', σ_s'')⌝ ∗
          state_interp P_t σ_t P_s σ_s'' ∗ Φ v_t' v_s')

        ∨ (* red case *)
         ⌜reducible P_t (fill K_t e_t) σ_t⌝ ∗
         (∀ e_t' σ_t',
            ⌜prim_step P_t (fill K_t e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
              (* stutter *)
              state_interp P_t σ_t' P_s σ_s ∗ least_def Ω Φ (bind_pred Ω Φ) (fill K_s e_s) e_t'
              ∨ (* step *)
              (∃ e_s' σ_s'',
               ⌜tc (prim_step P_s) (fill K_s e_s, σ_s) (e_s', σ_s'')⌝ ∗ state_interp P_t σ_t' P_s σ_s'' ∗
               bind_pred Ω Φ e_s' e_t'))
        ∨ (* call case *)
          (∃ (f : string) (K_t' : ectx Λ) (v_t' : val Λ) (K_s' : ectx Λ) (v_s' : val Λ) σ_s'',
            ⌜fill K_t e_t = fill K_t' (of_call f v_t')⌝ ∗
            ⌜rtc (prim_step P_s) (fill K_s e_s, σ_s) (fill K_s' (of_call f v_s'), σ_s'')⌝ ∗
            Ω v_t' v_s' ∗ state_interp P_t σ_t P_s σ_s'' ∗
            (∀ v_t'' v_s'' : val Λ, Ω v_t'' v_s'' -∗
              bind_pred Ω Φ (fill K_s' (of_val v_s'')) (fill K_t' (of_val v_t'')))).
  Proof.
    (* unfold Hpost to examine the result and combine the two simulation proofs *)
    iIntros (H0 H Hnreach) "Hpost Hstate".
    rewrite {1}sim_eq {1}sim_def_unfold.
    rewrite {1}/greatest_step !least_def_unfold /least_step.
    iMod ("Hpost" with "[Hstate]") as "Hpost".
    { iFrame. iPureIntro. intros Hstuck. eapply Hnreach, prim_step_rtc_reach_stuck.
      1:by apply fill_prim_step_rtc. assumption. }
    iModIntro.
    iDestruct "Hpost" as "[Hv | [Hstep | Hcall]]".
    + iLeft. iDestruct "Hv" as (v_t' v_s' σ_s'') "(% & % & Hstate & Hpost)".
      iExists v_t', v_s', σ_s''. iFrame.
      iSplitL. { iPureIntro. by rewrite -H1 (of_to_val _ _ H). }
      iPureIntro. etrans; eauto using fill_prim_step_rtc.
    + iRight; iLeft. iDestruct "Hstep" as "[% Hstep]". iSplitR "Hstep".
      { iPureIntro. by rewrite (of_to_val _ _ H) in H1. }
      iIntros (e_t' σ_t') "%". iMod ("Hstep" with "[]") as "Hstep".
      { iPureIntro. by rewrite (of_to_val _ _ H). }
      iModIntro. iDestruct "Hstep" as "[[Hstate Hstutter] | Hstep]".
      * (* CA on the reduction of e_s to v_s to check if we need to stutter or not *)
        apply (rtc_inv_tc) in H0 as [Heq | H3].
        { injection Heq as ??; subst. iLeft. iFrame. iApply least_def_mon. 2: iApply "Hstutter".
          iModIntro. iIntros ([e_s e_t'']) "H".
          iExists e_t'', e_s, empty_ectx, empty_ectx.
          rewrite !fill_empty. do 2 (iSplitR; first auto).
          iApply sim_mono. 2: { rewrite sim_eq. iApply "H". }
          iIntros (v_t' v_s') "Hv". rewrite !fill_empty. by iApply sim_value.
        }
        {
          iRight. iExists (fill K_s (of_val v_s)), σ_s'. iFrame.
          iSplitR "Hstutter".
          { iPureIntro. by apply fill_prim_step_tc. }
          cbn. iExists e_t', (fill K_s (of_val v_s)), empty_ectx, empty_ectx. rewrite !fill_empty.
          do 2 (iSplitR; first auto).
          iApply sim_mono. 2: { iApply sim_stutter_incl. iApply "Hstutter". }
          iIntros (v_t' v_s') "Hv". rewrite !fill_empty. by iApply sim_value.
        }
      * iDestruct "Hstep" as (e_s' σ_s'') "(%&Hstate& Hrec)". iRight.
        iExists e_s', σ_s''. iFrame. iSplitR.
        { iPureIntro. eapply tc_rtc_l; by eauto using fill_prim_step_rtc. }
        cbn. iExists e_t', e_s', empty_ectx, empty_ectx. rewrite !fill_empty.
        do 2 (iSplitR; first auto).
        iApply sim_mono. 2: { rewrite sim_eq. iApply "Hrec". }
        iIntros (??) "H". rewrite !fill_empty.
        by iApply sim_value.
    + iDestruct "Hcall" as (f K_t' v_t' K_s' v_s' σ_s'') "(%&%&Hvrel&Hstate&Hcall)".
      (* CA on the reduction of fill K_s v_s to fill K_s' (f v_s') to see if we need to take a step or do the call *)
      iRight; iRight.
      iExists f, K_t', v_t', K_s', v_s', σ_s''. iFrame.
      iSplitR. { iPureIntro. by rewrite -H1 (of_to_val _ _ H). }
      iSplitR. { iPureIntro. etrans; eauto using fill_prim_step_rtc. }
      iIntros (v_t'' v_s'') "Hvrel". cbn.
      iExists (fill K_t' (of_val v_t'')), (fill K_s' (of_val v_s'')), empty_ectx, empty_ectx.
      rewrite !fill_empty. do 2 (iSplitR; first auto).
      iApply sim_mono; first last.
      { rewrite sim_eq. by iApply "Hcall". }
      iIntros (??) "H". rewrite !fill_empty. by iApply sim_value.
  Qed.

  Lemma sim_bind Ω e_t e_s K_t K_s Φ :
    e_t ⪯{Ω} e_s {{λ v_t v_s : val Λ, fill K_t (of_val v_t) ⪯{Ω} fill K_s (of_val v_s) {{Φ}} }} -∗
    fill K_t e_t ⪯{Ω} fill K_s e_s {{Φ}}.
  Proof.
    iIntros "H".
    iApply (sim_coind Ω Φ (λ e_t' e_s', bind_pred Ω Φ e_s' e_t')%I).
    2: { iExists e_t, e_s, K_t, K_s. iFrame. eauto. }
    iModIntro. clear e_t e_s K_t K_s.
    iIntros (e_t' e_s') "IH".
    iDestruct "IH" as (e_t e_s K_t K_s) "[-> [-> H]]".
    rewrite {1}sim_eq {1}sim_def_unfold.
    rewrite /greatest_step !least_def_unfold /least_step.

    iIntros (????) "[Hs %]". rename H into Hnreach.
    iMod ("H" with "[Hs]") as "H".
    { iFrame. iPureIntro. contradict Hnreach. by apply fill_reach_stuck. }
    iDestruct "H" as "[Hval | [Hstep | Hcall]]".
    - iDestruct "Hval" as (v_t v_s σ_s') "(%& %&Hstate&Hpost)".
      by iApply (sim_bind_val with "[Hpost] [Hstate]").
    - (* simply thread through everything *)
      iModIntro. iRight; iLeft. iDestruct "Hstep" as "[% Hstep]".
      iSplitR. { iPureIntro. by apply fill_reducible. }
      iIntros (e_t' σ_t') "%".
      destruct (fill_reducible_prim_step _ _ _ _ _ _ H H0) as (e_t'' & -> & H1).
      iMod ("Hstep" with "[]") as "Hstep". { iPureIntro. apply H1. }
      iModIntro. iDestruct "Hstep" as "[[Hstate Hstutter] | Hstep]".
      + iLeft. iFrame.
        (* inner induction *)
        iApply (sim_ind _ _ _ _ (λ e_t'', least_def Ω Φ (bind_pred Ω Φ) (fill K_s e_s) (fill K_t e_t''))%I); last done.
        clear H0 H1 e_t'' H e_t σ_t P_t Hnreach P_s σ_s.
        iModIntro. iIntros (e_t'') "IH". rewrite least_def_unfold /least_step.
        iIntros (????) "[Hstate %]". iMod ("IH" with "[Hstate ]") as "IH".
        { iFrame. iPureIntro. contradict H. by apply fill_reach_stuck. }
        iDestruct "IH" as "[Hval | [Hred | Hcall]]".
        * iDestruct "Hval" as (v_t v_s σ_s') "(% & % & Hstate & Hrec)".
          by iApply (sim_bind_val with "[Hrec] [Hstate]").
        * iModIntro. iDestruct "Hred" as "[% Hred]". iRight; iLeft. iSplitR.
          { iPureIntro. by apply fill_reducible. }
          iIntros (e_t' σ_t'') "%".
          destruct (fill_reducible_prim_step _ _ _ _ _ _ H0 H1) as (e_t''' & -> & H2).
          iMod ("Hred" with "[ //]") as "[Hstutter | Hstep]"; iModIntro; first by iLeft.
          iRight. iDestruct "Hstep" as (e_s' σ_s') "(%&Hstate&Hrec)".
          iExists (fill K_s e_s'), σ_s'. iFrame. iSplitR.
          { iPureIntro. by apply fill_prim_step_tc. }
          cbn. iExists e_t''', e_s', K_t, K_s. do 2 (iSplitR; first auto).
          by rewrite sim_eq.
        * iModIntro. iDestruct "Hcall" as (f K_t' v_t K_s' v_s σ_s') "(-> & % & Hv & Hstate & Hcall)".
          iRight; iRight. iExists f, (comp_ectx K_t K_t'), v_t, (comp_ectx K_s K_s'), v_s, σ_s'.
          iSplitR. { by rewrite fill_comp. }
          iSplitR. { iPureIntro. rewrite -fill_comp. by apply fill_prim_step_rtc. }
          iFrame. iIntros (v_t' v_s') "Hv".
          cbn. iExists (fill K_t' (of_val v_t')), (fill K_s' (of_val v_s')), K_t, K_s.
          rewrite !fill_comp. do 2 (iSplitR; first auto).
          rewrite sim_eq. by iApply "Hcall".
      + iRight. iDestruct "Hstep" as (e_s' σ_s') "(% & Hstate & Hrec)".
        iExists (fill K_s e_s'), σ_s'. iFrame. iSplitR.
        { iPureIntro. by apply fill_prim_step_tc. }
        cbn. iExists e_t'', e_s', K_t, K_s.
        do 2 (iSplitR; first auto).
        rewrite sim_eq. iApply "Hrec".
    - (* simply thread through everything *)
      iModIntro. iRight; iRight.
      iDestruct "Hcall" as (f K_t' v_t K_s' v_s σ_s') "(-> & % & Hval & Hstate & Hrec)".
      iExists f, (comp_ectx K_t K_t'), v_t, (comp_ectx K_s K_s'), v_s, σ_s'.
      iSplitR; first by rewrite fill_comp.
      iSplitR. { iPureIntro. rewrite -fill_comp. by apply fill_prim_step_rtc. }
      iFrame.
      iIntros (v_t' v_s') "Hv". iSpecialize ("Hrec" with "Hv"). cbn.
      iExists (fill K_t' (of_val v_t')), (fill K_s' (of_val v_s')), K_t, K_s.
      iSplitR; first by rewrite -fill_comp. iSplitR; first by rewrite -fill_comp.
      rewrite sim_eq. iApply "Hrec".
  Qed.

  (** Corollaries *)
  Lemma sim_call_inline Ω P_t P_s v_t v_s K_t K_s f Φ :
    P_t !! f = Some K_t →
    P_s !! f = Some K_s →
    ⊢ progs_are P_t P_s ∗ Ω v_t v_s ∗ sim_ectx Ω K_t K_s Φ -∗ (of_call f v_t) ⪯{Ω} (of_call f v_s) {{Φ}}.
  Proof.
    intros Htgt Hsrc. iIntros "(#Prog & Val & Sim)".
    rewrite sim_unfold. iIntros (P_t' σ_t P_s' σ_s) "[SI %]".
    iModIntro. iRight. iLeft.
    rewrite /progs_are; iDestruct ("Prog" with "SI") as "[% %]"; subst P_t' P_s'; iClear "Prog".
    iSplit.
    - iPureIntro. eapply head_prim_reducible. eexists _, _. by eapply call_head_step_intro.
    - iIntros (e_t' σ_t' Hstep). iModIntro.
     pose proof (prim_step_call_inv P_t empty_ectx f v_t e_t' σ_t σ_t') as (K_t' & Heq & -> & ->);
      first by rewrite fill_empty.
      rewrite fill_empty in Hstep. iRight.
      iExists _, _; iFrame; iSplit.
      + iPureIntro. eapply tc_once, head_prim_step, call_head_step_intro, Hsrc.
      + rewrite fill_empty; assert (K_t' = K_t) as -> by naive_solver. iApply ("Sim" with "Val").
  Qed.

  Lemma sim_frame_r Ω e_t e_s R Φ :
    e_t ⪯{Ω} e_s {{ Φ }} ∗ R ⊢ e_t ⪯{Ω} e_s {{λ v_t v_s, Φ v_t v_s ∗ R}}.
  Proof.
    iIntros "[Hsim HR]". iApply (sim_mono with "[HR] [Hsim//]"). iIntros (v_t v_s) "H". iFrame.
  Qed.

  Lemma sim_frame_l Ω e_t e_s R Φ :
    R ∗ e_t ⪯{Ω} e_s {{ Φ }} ⊢ e_t ⪯{Ω} e_s {{λ v_t v_s, R ∗ Φ v_t v_s}}.
  Proof.
    iIntros "[HR Hsim]". iApply (sim_mono with "[HR] [Hsim//]"). iIntros (v_t v_s) "H". iFrame.
  Qed.

  Lemma sim_wand Ω e_t e_s Φ Ψ :
    e_t ⪯{Ω} e_s {{ Φ }} -∗ (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) -∗ e_t ⪯{Ω} e_s {{ Ψ }}.
  Proof. iIntros "H Hv". iApply (sim_mono with "[Hv//] [H//]"). Qed.

  Lemma sim_wand_l Ω e_t e_s Φ Ψ :
    (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) ∗ e_t ⪯{Ω} e_s {{ Φ }} ⊢ e_t ⪯{Ω} e_s {{ Ψ }}.
  Proof. iIntros "[Hv H]". iApply (sim_wand with "[H//] [Hv//]"). Qed.

  Lemma sim_wand_r Ω e_t e_s Φ Ψ :
    e_t ⪯{Ω} e_s {{ Φ }} ∗ (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) ⊢ e_t ⪯{Ω} e_s {{ Ψ }}.
  Proof. iIntros "[H Hv]". iApply (sim_wand with "[H//] [Hv//]"). Qed.

  Lemma sim_stutter_source Ω e_t e_s Φ :
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
       ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
        state_interp P_t σ_t' P_s σ_s ∗ e_t' ⪯{Ω} e_s {{ Φ }}) -∗
    e_t ⪯{Ω} e_s {{ Φ }}.
  Proof.
    iIntros "H". rewrite (sim_unfold Ω Φ e_t e_s). iIntros (????) "[H1 H2]".
    iMod ("H" with "H1") as "H". iModIntro. iRight; iLeft. iDestruct "H" as "(% & Hnext)".
    iSplitR. { by iPureIntro. }
    iIntros (e_t' σ_t') "Hstep". iMod ("Hnext" with "Hstep") as "[Hstate Hsim]".
    iModIntro. iLeft. iFrame.
  Qed.

  Lemma sim_step_source Ω e_t e_s Φ :
    (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗ ∃ e_s' σ_s',
      ⌜rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t P_s σ_s' ∗
      e_t ⪯{Ω} e_s' {{ Φ }}) -∗
    e_t ⪯{Ω} e_s {{ Φ }}.
  Proof.
    rewrite sim_unfold. iIntros "Hsource" (P_t σ_t P_s σ_s) "[Hstate %]".
    iMod ("Hsource" with "Hstate") as (e_s' σ_s') "(% & Hstate & Hsim)".
    rename H0 into Hsrc_rtc.
    rewrite {1}sim_unfold.
    iMod ("Hsim" with "[Hstate]") as "Hsim".
    { iFrame. iPureIntro. by eapply not_reach_stuck_pres_rtc. }
    iModIntro. iDestruct "Hsim" as "[Hval | [Hstep | Hcall]]".
    - iLeft. iDestruct "Hval" as (v_t v_s σ_s'') "(Hval & % & Hstate & Hphi)".
      iExists v_t, v_s, σ_s''. iFrame. iPureIntro. by etrans.
    - iDestruct "Hstep" as "(%&Hstep)". iRight; iLeft.
      iSplitR; first by iPureIntro.
      iIntros (e_t' σ_t') "Hprim". iMod ("Hstep" with "Hprim") as "[Hstutter | Hred]"; iModIntro.
      + (* which path we want to take depends on the rtc we have *)
        apply rtc_inv_tc in Hsrc_rtc as [[= <- <-] | Hsrc_tc].
        { (* no step, just mirror the stuttering *) iLeft. iFrame. }
        (* we have actually taken a source step *)
        iRight. iExists e_s', σ_s'. iFrame. by iPureIntro.
      + iRight. iDestruct "Hred" as (e_s'' σ_s'') "(% & Hstate & Hsim)".
        iExists e_s'', σ_s''. iFrame. iPureIntro.
        apply rtc_inv_tc in Hsrc_rtc as [[= <- <-] | Hsrc_tc]; first done.
        by etrans.
    - iDestruct "Hcall" as (f K_t v_t K_s v_s σ_s'') "(-> & % & Hv & Hstate & Hsim)".
      iRight; iRight. iExists f, K_t, v_t, K_s, v_s, σ_s''. iFrame.
      iSplitR; first done. iPureIntro. by etrans.
  Qed.

  (* the step case of the simulation relation, but the two cases are combined into an rtc in the source *)
  Lemma sim_step_target Ω e_t e_s Φ:
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' σ_t',
        ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
          ∃ e_s' σ_s', ⌜rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗
            state_interp P_t σ_t' P_s σ_s' ∗ e_t' ⪯{Ω} e_s' {{ Φ }}) -∗
    e_t ⪯{Ω} e_s {{ Φ }}.
  Proof.
    iIntros "H". rewrite (sim_unfold Ω Φ e_t e_s). iIntros (????) "[Hstate %]".
    iMod ("H" with "Hstate") as "[Hred H]". iModIntro. iRight; iLeft.
    iFrame. iIntros (e_t' σ_t') "Hstep". iMod ("H" with "Hstep") as "H". iModIntro.
    iDestruct "H" as (e_s' σ_s') "(%&H2&H3)".
    apply rtc_inv_tc in H0 as [[= -> ->] | H0].
    - iLeft. iFrame.
    - iRight; iExists e_s', σ_s'. iFrame. by iPureIntro.
  Qed.

  (** ** source_red judgment *)
  (** source_red allows to focus the reasoning on the source value
    (while being able to switch back and forth to the full simulation at any point) *)
  Definition source_red_rec (Ψ : prog Λ → expr Λ → state Λ → PROP) (rec : exprO → PROP) e_s :=
    (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗
      (∃ e_s' σ_s', ⌜prim_step P_s (e_s, σ_s) (e_s', σ_s')⌝ ∗
        state_interp P_t σ_t P_s σ_s' ∗ rec e_s')
      ∨ (state_interp P_t σ_t P_s σ_s ∗ Ψ P_s e_s σ_s))%I.

  Lemma source_red_mon Ψ l1 l2 :
    □ (∀ e, l1 e -∗ l2 e) -∗ ∀ e, source_red_rec Ψ  l1 e -∗ source_red_rec Ψ l2 e.
  Proof.
    iIntros "Hmon" (e) "Hl1". rewrite /source_red_rec.
    iIntros (????) "Hstate". iMod ("Hl1" with "Hstate") as "[Hstep | Hstuck]".
    - iDestruct "Hstep" as (e_s' σ_s') "(?&?&?)". iModIntro. iLeft.
      iExists e_s', σ_s'. iFrame. by iApply "Hmon".
    - iModIntro; iRight. iFrame.
  Qed.

  Instance source_red_mono Ψ : BiMonoPred (source_red_rec Ψ).
  Proof.
    constructor.
    - iIntros (l1 l2) "H". by iApply source_red_mon.
    - intros l Hne n e1 e2 Heq. apply (discrete_iff _ _) in Heq as ->. done.
  Qed.

  Definition source_red_def Ψ := bi_least_fixpoint (source_red_rec Ψ).
  Lemma source_red_unfold Ψ e_s : source_red_def Ψ e_s ⊣⊢ source_red_rec Ψ (source_red_def Ψ) e_s.
  Proof. by rewrite /source_red_def least_fixpoint_unfold. Qed.

  Definition source_red_aux : seal (flip source_red_def).
  Proof. by eexists. Qed.
  Definition source_red := source_red_aux.(unseal).
  Lemma source_red_eq : source_red = flip source_red_def.
  Proof. rewrite -source_red_aux.(seal_eq) //. Qed.

  Lemma source_red_strong_ind Ψ (Ψi : expr Λ → PROP) :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO, source_red_rec Ψ (λ e', Ψi e' ∧ source_red_def Ψ e') e -∗ Ψi e) -∗
    ∀ e : exprO, source_red_def Ψ e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /source_red_def.
    by iApply (@least_fixpoint_strong_ind _ _ (source_red_rec Ψ) _ Ψi).
  Qed.

  Lemma source_red_ind Ψ (Ψi : expr Λ → PROP) :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO, source_red_rec Ψ Ψi e -∗ Ψi e) -∗
    ∀ e : exprO, source_red_def Ψ e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /source_red_def.
    by iApply (@least_fixpoint_ind _ _ (source_red_rec Ψ) Ψi).
  Qed.

  Lemma source_red_elim Ψ e_s :
    source_red e_s Ψ -∗
    ∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗
      ∃ e_s' σ_s', ⌜rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ Ψ P_s e_s' σ_s' ∗ state_interp P_t σ_t P_s σ_s'.
  Proof.
    iIntros "H". rewrite source_red_eq.
    iApply (source_red_ind _ (λ e_s, ∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗
        ∃ e_s' σ_s', ⌜rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ Ψ P_s e_s' σ_s' ∗ state_interp P_t σ_t P_s σ_s')%I);
    last by rewrite /flip.
    clear e_s. iModIntro. iIntros (e_s) "IH". iIntros (P_s σ_s P_t σ_t) "HSI".
    rewrite /source_red_rec.
    iMod ("IH" with "HSI") as "IH".
    iDestruct "IH" as "[Hstep | [Hstate Hp]]"; first last.
    { iModIntro. iExists e_s, σ_s. iFrame. by iPureIntro. }
    iDestruct "Hstep" as (e_s' σ_s') "(% & Hstate & IH)".
    iMod ("IH" with "Hstate") as (e_s'' σ_s'') "(% & Hp & Hs)". iModIntro.
    iExists e_s'', σ_s''; iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma source_red_base Ψ e_s :
    (∀ P_s σ_s, |==> Ψ P_s e_s σ_s) -∗ source_red e_s Ψ.
  Proof.
    iIntros "Hpsi". rewrite source_red_eq /flip source_red_unfold /source_red_rec.
    iIntros (P_s σ_s P_t σ_t) "Hstate". iRight. iMod ("Hpsi" $! P_s σ_s). iModIntro. iFrame.
  Qed.

  Lemma source_red_step Ψ e_s :
    (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗
      (∃ e_s' σ_s', ⌜prim_step P_s (e_s, σ_s) (e_s', σ_s')⌝ ∗
        state_interp P_t σ_t P_s σ_s' ∗ source_red e_s' Ψ)) -∗
    source_red e_s Ψ.
  Proof.
    iIntros "Hstep". rewrite source_red_eq /flip source_red_unfold /source_red_rec.
    iIntros (P_s σ_s P_t σ_t) "Hstate". iLeft. iMod ("Hstep" with "Hstate"). iModIntro. iFrame.
  Qed.

  Lemma source_red_sim Ω e_s e_t Φ :
    (source_red e_s (λ _ e_s' _, e_t ⪯{Ω} e_s' {{Φ}})) -∗
    e_t ⪯{Ω} e_s {{Φ}}.
  Proof.
    iIntros "Hsource". iPoseProof (source_red_elim with "Hsource") as "Hsource".
    iApply sim_step_source. iIntros (????) "Hstate".
    iMod ("Hsource" with "Hstate") as (e_s' σ_s') "(?&?&?)".
    iModIntro. iExists e_s', σ_s'. iFrame.
  Qed.

  (** * Definition of source_stuck *)
  Definition source_stuck e_s := source_red e_s (λ P_s e_s σ_s, ⌜ stuck P_s e_s σ_s ⌝%I).

  Lemma source_stuck_reach_stuck e_s :
    source_stuck e_s -∗
      ∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗ ⌜ reach_stuck P_s e_s σ_s ⌝.
  Proof.
    iIntros "H" (????) "Hstate".
    iMod (source_red_elim with "H Hstate") as (e_s' σ_s') "(%&%&_)".
    iModIntro; iPureIntro. exists e_s', σ_s'. eauto.
  Qed.

  Lemma source_stuck_sim Ω e_s e_t Φ :
    ⊢ source_stuck e_s -∗ e_t ⪯{Ω} e_s {{ Φ }}.
  Proof.
    iIntros "H". rewrite sim_unfold. iIntros (????) "[Hs %]".
    iMod (source_stuck_reach_stuck with "H Hs") as "%".
    exfalso. by apply H.
  Qed.

  Lemma stuck_source_stuck e_s :
    (∀ P_s σ_s, ⌜ stuck P_s e_s σ_s ⌝) -∗ source_stuck e_s.
  Proof.
    iIntros "Hstuck". rewrite /source_stuck source_red_eq /flip source_red_unfold.
    iIntros (????) "Hstate". iModIntro; iRight. iFrame. eauto.
  Qed.

  Lemma source_stuck_fill e_s K_s :
    source_stuck e_s -∗ source_stuck (fill K_s e_s).
  Proof.
    iIntros "He".
    iApply (source_red_ind _ (λ e_s, (source_stuck (fill K_s e_s)%I))); last by rewrite /source_stuck source_red_eq /flip.
    iModIntro. clear e_s. iIntros (e_s).
    rewrite /source_stuck source_red_eq /flip source_red_unfold.
    iIntros "He" (????) "Hstate". iMod ("He" with "Hstate") as "[Hstep | [Hstate %]]"; iModIntro;
      last by iRight; iFrame; iPureIntro; apply fill_stuck.
    iLeft. iDestruct "Hstep" as (e_s' σ_s') "(%&?&Hsource)".
    iExists (fill K_s e_s'), σ_s'. iFrame. iPureIntro.
    by apply fill_prim_step.
  Qed.

  (** Source reduction to a value *)
  Definition source_eval e_s Φ := source_red e_s (λ P_s e_s σ_s, ∃ v_s, ⌜ (to_val e_s) = Some v_s ⌝ ∗ Φ v_s)%I.

  Lemma source_red_bind e_s K_s Ψ :
    source_eval e_s (λ v_s, source_red (fill K_s (of_val v_s)) Ψ) -∗
    source_red (fill K_s e_s) Ψ.
  Proof.
    iIntros "He".
    iApply (source_red_ind _ (λ e_s, source_red (fill K_s e_s) Ψ)%I); last by rewrite /source_eval source_red_eq /flip .
    iModIntro. clear e_s. iIntros (e_s) "IH". rewrite source_red_eq /flip source_red_unfold.
    iIntros (????) "Hstate". iMod ("IH" with "Hstate") as "IH".
    iDestruct "IH" as "[Hstep | [Hstate Hval]]".
    { iModIntro. iDestruct "Hstep" as (e_s' σ_s') "(%&?&?)". iLeft.
      iExists (fill K_s e_s'), σ_s'. iFrame. iPureIntro.
      by apply fill_prim_step. }
    iDestruct "Hval" as (v_s) "(% & Hval)".
    rewrite source_red_unfold.
    iMod ("Hval" with "Hstate") as "[Hstep | Hval]"; iModIntro; rewrite -(of_to_val _ _ H);
    eauto.
  Qed.

  Lemma source_stuck_bind e_s K_s :
    source_eval e_s (λ v_s, source_stuck (fill K_s (of_val v_s))) -∗
    source_stuck (fill K_s e_s).
  Proof. iIntros "Hstuck". rewrite /source_stuck. by iApply source_red_bind. Qed.

  Lemma source_eval_bind e_s K_s Φ :
    source_eval e_s (λ v_s, source_eval (fill K_s (of_val v_s)) Φ) -∗
    source_eval (fill K_s e_s) Φ.
  Proof. iIntros "Hval". iApply source_red_bind. iApply "Hval". Qed.

  (** ** same thing for target *)
  Definition target_red_rec (Ψ : expr Λ → PROP) (rec : exprO → PROP) e_t :=
    (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗
      (⌜ reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
        state_interp P_t σ_t' P_s σ_s ∗ rec e_t')
      ∨ (state_interp P_t σ_t P_s σ_s ∗ Ψ e_t))%I.

  Lemma target_red_mon Ψ l1 l2 :
    □ (∀ e, l1 e -∗ l2 e) -∗ ∀ e, target_red_rec Ψ l1 e -∗ target_red_rec Ψ l2 e.
  Proof.
    iIntros "Hmon" (e) "Hl1". rewrite /source_red_rec.
    iIntros (????) "Hstate". iMod ("Hl1" with "Hstate") as "[[Hred Hstep] | Hstuck]".
    - iModIntro. iLeft. iFrame.
      iIntros (e_t' σ_t') "Hprim". iMod ("Hstep" with "Hprim") as "[Hstate Hprim]".
      iModIntro. iFrame. by iApply "Hmon".
    - iModIntro; iRight. iFrame.
  Qed.

  Instance target_red_mono Ψ : BiMonoPred (target_red_rec Ψ).
  Proof.
    constructor.
    - iIntros (l1 l2) "H". by iApply target_red_mon.
    - intros l Hne n e1 e2 Heq. apply (discrete_iff _ _) in Heq as ->. done.
  Qed.

  Definition target_red_def Ψ := bi_least_fixpoint (target_red_rec Ψ).
  Lemma target_red_unfold Ψ e_t : target_red_def Ψ e_t ⊣⊢ target_red_rec Ψ (target_red_def Ψ) e_t.
  Proof. by rewrite /target_red_def least_fixpoint_unfold. Qed.

  Definition target_red_aux : seal (flip target_red_def).
  Proof. by eexists. Qed.
  Definition target_red := target_red_aux.(unseal).
  Lemma target_red_eq : target_red = flip target_red_def.
  Proof. rewrite -target_red_aux.(seal_eq) //. Qed.

  Lemma target_red_strong_ind Ψ (Ψi : expr Λ → PROP) :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO, target_red_rec Ψ (λ e', Ψi e' ∧ target_red_def Ψ e') e -∗ Ψi e) -∗
    ∀ e : exprO, target_red_def Ψ e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /target_red_def.
    by iApply (@least_fixpoint_strong_ind _ _ (target_red_rec Ψ) _ Ψi).
  Qed.

  Lemma target_red_ind Ψ (Ψi : expr Λ → PROP) :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO, target_red_rec Ψ Ψi e -∗ Ψi e) -∗
    ∀ e : exprO, target_red_def Ψ e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /target_red_def.
    by iApply (@least_fixpoint_ind _ _ (target_red_rec Ψ) Ψi).
  Qed.

  Lemma target_red_base Ψ e_t :
    (|==> Ψ e_t) -∗ target_red e_t Ψ.
  Proof.
    iIntros "Hpsi". rewrite target_red_eq /flip target_red_unfold /target_red_rec.
    iIntros (P_s σ_s P_t σ_t) "Hstate". iRight. iMod ("Hpsi"). iModIntro. iFrame.
  Qed.

  Lemma target_red_step Ψ e_t :
    (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗
      (⌜ reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
        state_interp P_t σ_t' P_s σ_s ∗ target_red e_t' Ψ)) -∗
    target_red e_t Ψ .
  Proof.
    iIntros "Hstep". rewrite target_red_eq /flip target_red_unfold /target_red_rec.
    iIntros (P_s σ_s P_t σ_t) "Hstate". iLeft. iMod ("Hstep" with "Hstate"). iModIntro. iFrame.
  Qed.

  Lemma target_red_sim Ω e_s e_t Φ :
    (target_red e_t (λ e_t', e_t' ⪯{Ω} e_s {{ Φ }})) -∗
    e_t ⪯{Ω} e_s {{ Φ }}.
  Proof.
    iIntros "Htarget". rewrite target_red_eq.
    iApply (target_red_ind _ (λ e_t, e_t ⪯{Ω} e_s {{ Φ }})%I); last by rewrite /flip.
    iModIntro. clear e_t. iIntros (e_t) "Htarget".
    rewrite sim_unfold. iIntros (????) "[Hstate Hnreach]".
    iMod ("Htarget" with "Hstate") as "[[Hred Hstep] | [Hstate Hsim]]".
    - iModIntro. iRight; iLeft. iFrame. iIntros (e_t' σ_t') "Hprim".
      (* stuttering step *) iLeft.
      iMod ("Hstep" with "Hprim") as "Hstep". iModIntro; iFrame.
    - rewrite {1}sim_unfold. by iMod ("Hsim" with "[$Hstate $Hnreach]").
  Qed.

  (** target eval to a value *)
  Definition target_eval e_t Φ := target_red e_t (λ e_t, ∃ v_t, ⌜ (to_val e_t) = Some v_t ⌝ ∗ Φ v_t)%I.

  Lemma target_red_bind e_t K_t Ψ :
    target_eval e_t (λ v_t, target_red (fill K_t (of_val v_t)) Ψ) -∗
    target_red (fill K_t e_t) Ψ.
  Proof.
    iIntros "He".
    iApply (target_red_ind _ (λ e_t, target_red (fill K_t e_t) Ψ)%I); last by rewrite /target_eval target_red_eq /flip.
    iModIntro. clear e_t. iIntros (e_t) "IH". rewrite target_red_eq /flip target_red_unfold.
    iIntros (????) "Hstate". iMod ("IH" with "Hstate") as "IH".
    iDestruct "IH" as "[[% Hstep] | [Hstate Hval]]"; first last.
    - iDestruct "Hval" as (v_s) "(% & Hval)". rewrite target_red_unfold.
      iMod ("Hval" with "Hstate") as "[Hstep | Hval]"; iModIntro; rewrite -(of_to_val _ _ H);
        eauto.
    - rename H into Hred. iModIntro. iLeft. iSplitR; first by eauto using fill_reducible.
      iIntros (e_t' σ_t') "%". rename H into Hprim.
      eapply fill_reducible_prim_step in Hprim as (e_t'' & -> & H); last done.
      by iMod ("Hstep" with "[% //]").
  Qed.
End fix_lang.

