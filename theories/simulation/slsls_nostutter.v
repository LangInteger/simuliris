(** * Simpler relation without stuttering using just a greatest fp. *)
From iris.bi Require Import bi lib.fixpoint.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import relations language.
From simuliris.simulation Require Export simulation.
From iris.prelude Require Import options.
Import bi.

Section fix_lang.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language}.
  Context {val_rel : val Λ → val Λ → PROP}.
  Context {s : SimulLang PROP Λ val_rel}.

  Set Default Proof Using "Type*".

  Implicit Types
    (e_s e_t e: expr Λ)
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ)
    (Φ Ψ : val Λ → val Λ → PROP).


  Definition step_nostutter Φ (greatest_rec : exprO * exprO → PROP) : exprO * exprO → PROP:=
    λ '(e_s, e_t), (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ -∗ |==>
      (* value case *)
      (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')⌝ ∗
        state_interp P_t σ_t P_s σ_s' ∗ Φ v_t v_s)

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
        ∃ e_s' σ_s', ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗ 
          greatest_rec (e_s', e_t'))

      ∨ (* call case *)
      (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
        ⌜rtc (prim_step P_s) (e_s, σ_s) (fill K_s (of_call f v_s), σ_s')⌝ ∗
        val_rel v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
        (∀ v_t v_s, val_rel v_t v_s -∗ greatest_rec (fill K_s (of_val v_s), fill K_t (of_val v_t))))
    )%I.

  Definition sim_nostutter_def Φ :=
    bi_greatest_fixpoint (step_nostutter Φ).

  Instance step_nostutter_proper:
    Proper ((pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡)))
      ==> (pointwise_relation _ (≡))
      ==> (≡) ==> (≡)) (step_nostutter).
  Proof. solve_proper. Qed.

  Instance step_nostutter_mono Φ:
    BiMonoPred (step_nostutter Φ).
  Proof.
    constructor.
    - intros g1 g2. iIntros "#H".
      iIntros ([e_s e_t]) "Hg". rewrite /step_nostutter.
      iIntros (P_t σ_t P_s σ_s) "Ha".
      iMod ("Hg" with "Ha") as "[Hval | [Hstep | Hcall]]"; iModIntro.
      + iLeft. iApply "Hval".
      + iRight; iLeft. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
        iIntros (e_t' σ_t') "Hstep". iMod ("Hr" with "Hstep") as "Hstep"; iModIntro.
        iDestruct "Hstep" as (e_s' σ_s') "(H1& H2 &H3)".
        iExists (e_s'), (σ_s'). iFrame. by iApply "H".
      + iRight; iRight. iDestruct "Hcall" as (f K_t v_t K_s v_s σ_s') "(H1& H2& H3& H4&H5)".
        iExists (f), (K_t), (v_t), (K_s), (v_s), (σ_s'). iFrame.
        iIntros (? ?) "H1". iApply "H". by iApply "H5".
    - intros g Hne n e1 e2 Heq.
      apply (discrete_iff _ _) in Heq as ->. done.
  Qed.

  Lemma sim_nostutter_def_unfold Φ e_s e_t:
    sim_nostutter_def Φ (e_s, e_t) ⊣⊢ step_nostutter Φ (sim_nostutter_def Φ) (e_s, e_t).
  Proof. by rewrite /sim_nostutter_def greatest_fixpoint_unfold. Qed.

  Definition sim_nostutter_aux : seal (λ e_t e_s Φ, @sim_nostutter_def Φ (e_s, e_t)).
  Proof. by eexists. Qed.
  Global Instance sim_nostutter : Sim s := sim_nostutter_aux.(unseal).
  Lemma sim_nostutter_eq : sim (Sim:=sim_nostutter) = λ e_t e_s Φ, @sim_nostutter_def Φ (e_s, e_t).
  Proof. by rewrite <-sim_nostutter_aux.(seal_eq). Qed.

  Lemma sim_nostutter_unfold e_t e_s Φ:
    sim (Sim:=sim_nostutter) e_t e_s Φ ⊣⊢
    (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ -∗ |==>
      (* value case *)
        (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')⌝ ∗
          state_interp P_t σ_t P_s σ_s' ∗ Φ v_t v_s)

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
        ∃ e_s' σ_s', ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗
        sim e_t' e_s' Φ)

      ∨ (* call case *)
      (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
        ⌜rtc (prim_step P_s) (e_s, σ_s) (fill K_s (of_call f v_s), σ_s')⌝ ∗
        val_rel v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
        sim_ectx K_t K_s Φ)
    )%I.
  Proof.
    by rewrite /sim_ectx !sim_nostutter_eq /uncurry sim_nostutter_def_unfold /step_nostutter.
  Qed.

  Lemma sim_nostutter_coind Φ (Ψ : exprO → exprO → PROP):
    Proper ((≡) ==> (≡) ==> (≡)) Ψ →
    (□ ∀ e_t e_s, Ψ e_t e_s -∗ step_nostutter Φ (λ '(e_s', e_t'), Ψ e_t' e_s') (e_s, e_t)) -∗
    (∀ e_t e_s, Ψ e_t e_s -∗ e_t ⪯ e_s {{ Φ }}).
  Proof.
    iIntros (Hp) "#IH". iIntros (e_t e_s) "H".
    rewrite sim_nostutter_eq /sim_nostutter_def.
    set (Ψ_curry := (λ '(e_t, e_s), Ψ e_s e_t)).
    assert (NonExpansive Ψ_curry) as Hne.
    { intros ? [e1 e2] [e1' e2'] [H1 H2]. rewrite /Ψ_curry. cbn in H1, H2.
      apply equiv_dist, Hp.
      - by apply (discrete_iff _ _) in H1.
      - by apply (discrete_iff _ _) in H2.
    }

    iApply (greatest_fixpoint_coind (step_nostutter Φ) Ψ_curry with "[]").
    { iModIntro. iIntros ([e_s' e_t']) "H'". by iApply "IH". }
    iApply "H".
  Qed.

  Global Instance sim_nostutter_proper :
    Proper (eq ==> eq ==>
      (pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> (≡)) sim.
  Proof.
    intros e e' -> e1 e1' -> p1 p2 Heq2.
    rewrite !sim_nostutter_eq. apply greatest_fixpoint_proper; solve_proper.
  Qed.

  Lemma sim_nostutter_value Φ v_t v_s :
    ⊢ Φ v_t v_s -∗ (of_val v_t) ⪯ (of_val v_s) {{ Φ }}.
  Proof.
    iIntros "Hv". rewrite sim_nostutter_unfold. iIntros (????) "[Hstate Hreach]".
    iModIntro. iLeft. iExists (v_t), (v_s), (σ_s). iFrame.
    iSplitL; first by rewrite to_of_val. eauto.
  Qed.

  Lemma sim_nostutter_call P_t P_s v_t v_s K_t K_s f Φ :
    P_t !! f = Some K_t →
    P_s !! f = Some K_s →
    progs_are P_t P_s -∗
    val_rel v_t v_s -∗
    sim_ectx K_t K_s Φ -∗
    (of_call f v_t) ⪯ (of_call f v_s) {{ Φ }}.
  Proof.
    intros Htgt Hsrc. iIntros "#Prog Val Sim".
    rewrite sim_nostutter_unfold. iIntros (P_t' σ_t P_s' σ_s) "[SI %]".
    iModIntro. iRight. iLeft.
    rewrite /progs_are; iDestruct ("Prog" with "SI") as "[% %]"; subst P_t' P_s'; iClear "Prog".
    iSplit.
    - iPureIntro. eapply head_prim_reducible. eexists _, _. by eapply call_head_step_intro.
    - iIntros (e_t' σ_t' Hstep). iModIntro.
     pose proof (prim_step_call_inv P_t empty_ectx f v_t e_t' σ_t σ_t') as (K_t' & Heq & -> & ->);
      first by rewrite fill_empty.
      rewrite fill_empty in Hstep.
      iExists _, _; iFrame; iSplit.
      + iPureIntro. eapply tc_once, head_prim_step, call_head_step_intro, Hsrc.
      + rewrite fill_empty; assert (K_t' = K_t) as -> by naive_solver. iApply ("Sim" with "Val").
  Qed.

  Lemma bupd_sim_nostutter Φ e_t e_s :
    ⊢ (|==> e_t ⪯ e_s {{Φ}}) -∗ e_t ⪯ e_s {{ Φ }}.
  Proof.
    iIntros "Hv". rewrite sim_nostutter_unfold. iIntros (????) "H". iMod "Hv". iApply ("Hv" with "H").
  Qed.

  Lemma sim_nostutter_mono Φ Φ' :
    ⊢ (∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s)
       -∗ ∀ e_s e_t : exprO, e_t ⪯ e_s {{ Φ }} -∗ e_t ⪯ e_s {{ Φ' }}.
  Proof.
    iIntros "Hmon".
    iIntros (e_s e_t) "H".
    iApply (sim_nostutter_coind Φ' (λ e_t e_s, e_t ⪯ e_s {{ Φ }} ∗ (∀ v_t v_s : val Λ, Φ v_t v_s -∗ Φ' v_t v_s))%I); last by iFrame.
    iModIntro. clear e_t e_s. iIntros (e_t e_s) "[H Hpost]".
    rewrite sim_nostutter_eq sim_nostutter_def_unfold.
    rewrite /step_nostutter.
    iIntros (????) "Hs". iSpecialize ("H" with "Hs"). iMod "H". iModIntro.
    iDestruct "H" as "[Hval | [Hred | Hcall]]".
    - iLeft. iDestruct "Hval" as (v_t v_s σ_s') "(?&?&?&?)". iExists v_t, v_s, σ_s'. iFrame. by iApply "Hpost".
    - iRight; iLeft. iDestruct "Hred" as "[Hred Hstep]". iFrame.
    - iRight; iRight. iFrame.
  Qed.

  (* TODO: currently just copied and adapted from the full lemma above; we don't need the factorisation for this simpler simulation *)
  Definition bind_pred_nostutter Φ := uncurry (λ '(e_s, e_t), ∃ e_t' e_s' (K_t K_s : ectx Λ),
    ⌜e_t = fill K_t e_t'⌝ ∧ ⌜e_s = fill K_s e_s'⌝ ∧
     e_t' ⪯ e_s' {{λ v_t v_s : val Λ, fill K_t (of_val v_t) ⪯ fill K_s (of_val v_s) {{Φ}}}})%I.

  (* Lemma used two times in the proof of the bind lemma (for the value cases of the inner and outer induction) *)
  Lemma sim_bind_val_nostutter P_s e_s σ_s v_s σ_s' e_t v_t K_t σ_t P_t K_s Φ:
      rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s') →
      to_val e_t = Some v_t →
      (¬ reach_stuck P_s (fill K_s e_s) σ_s) →
      ⊢ fill K_t (of_val v_t) ⪯ fill K_s (of_val v_s) {{Φ}} -∗
        state_interp P_t σ_t P_s σ_s' -∗ |==>

        (* val case *)
        (∃ (v_t' v_s' : val Λ) σ_s'', ⌜to_val (fill K_t e_t) = Some v_t'⌝ ∗
          ⌜rtc (prim_step P_s) (fill K_s e_s, σ_s) (of_val v_s', σ_s'')⌝ ∗
          state_interp P_t σ_t P_s σ_s'' ∗ Φ v_t' v_s')

        ∨ (* red case *)
         ⌜reducible P_t (fill K_t e_t) σ_t⌝ ∗
         (∀ e_t' σ_t',
            ⌜prim_step P_t (fill K_t e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
              (∃ e_s' σ_s'',
               ⌜tc (prim_step P_s) (fill K_s e_s, σ_s) (e_s', σ_s'')⌝ ∗ state_interp P_t σ_t' P_s σ_s'' ∗
               bind_pred_nostutter Φ e_s' e_t'))
        ∨ (* call case *)
          (∃ (f : string) (K_t' : ectx Λ) (v_t' : val Λ) (K_s' : ectx Λ) (v_s' : val Λ) σ_s'',
            ⌜fill K_t e_t = fill K_t' (of_call f v_t')⌝ ∗
            ⌜rtc (prim_step P_s) (fill K_s e_s, σ_s) (fill K_s' (of_call f v_s'), σ_s'')⌝ ∗
            val_rel v_t' v_s' ∗ state_interp P_t σ_t P_s σ_s'' ∗
            (∀ v_t'' v_s'' : val Λ, val_rel v_t'' v_s'' -∗
              bind_pred_nostutter Φ (fill K_s' (of_val v_s'')) (fill K_t' (of_val v_t'')))).
  Proof.
    (* unfold Hpost to examine the result and combine the two simulation proofs *)
    iIntros (H0 H Hnreach) "Hpost Hstate".
    rewrite {1}sim_nostutter_eq {1}sim_nostutter_def_unfold.
    rewrite {1}/step_nostutter.
    iMod ("Hpost" with "[Hstate]") as "Hpost".
    { iFrame. iPureIntro. intros Hstuck.
      eapply Hnreach, prim_step_rtc_reach_stuck; last done.
      by apply fill_prim_step_rtc. }
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
      iDestruct "Hstep" as (e_s' σ_s'') "(%&Hstate& Hrec)".
      iExists e_s', σ_s''. iFrame. iSplitR.
      { iPureIntro. eapply tc_rtc_l; by eauto using fill_prim_step_rtc. }
      cbn. iExists e_t', e_s', empty_ectx, empty_ectx. rewrite !fill_empty.
      do 2 (iSplitR; first auto).
      iApply sim_nostutter_mono. 2: { rewrite sim_nostutter_eq. iApply "Hrec". }
      iIntros (??) "H". rewrite !fill_empty.
      by iApply sim_nostutter_value.
    + iDestruct "Hcall" as (f K_t' v_t' K_s' v_s' σ_s'') "(%&%&Hvrel&Hstate&Hcall)".
      (* CA on the reduction of fill K_s v_s to fill K_s' (f v_s') to see if we need to take a step or do the call *)
      iRight; iRight.
      iExists f, K_t', v_t', K_s', v_s', σ_s''. iFrame.
      iSplitR. { iPureIntro. by rewrite -H1 (of_to_val _ _ H). }
      iSplitR. { iPureIntro. etrans; by eauto using fill_prim_step_rtc. }
      iIntros (v_t'' v_s'') "Hvrel". cbn.
      iExists (fill K_t' (of_val v_t'')), (fill K_s' (of_val v_s'')), empty_ectx, empty_ectx.
      rewrite !fill_empty. do 2 (iSplitR; first auto).
      iApply sim_nostutter_mono; first last.
      { rewrite sim_nostutter_eq. by iApply "Hcall". }
      iIntros (??) "H". rewrite !fill_empty. by iApply sim_nostutter_value.
  Qed.

  Lemma sim_nostutter_bind e_t e_s K_t K_s Φ:
    ⊢ e_t ⪯ e_s {{λ v_t v_s : val Λ, fill K_t (of_val v_t) ⪯ fill K_s (of_val v_s) {{Φ}} }}
      -∗ fill K_t e_t ⪯ fill K_s e_s {{Φ}}.
  Proof.
    iIntros "H".
    iApply (sim_nostutter_coind Φ (λ e_t' e_s', bind_pred_nostutter Φ e_s' e_t')%I).
    2: { iExists e_t, e_s, K_t, K_s. iFrame. eauto. }
    iModIntro. clear e_t e_s K_t K_s.
    iIntros (e_t' e_s') "IH".
    iDestruct "IH" as (e_t e_s K_t K_s) "[-> [-> H]]".
    rewrite {1}sim_nostutter_eq {1}sim_nostutter_def_unfold.
    rewrite /step_nostutter.

    iIntros (????) "[Hs %]". rename H into Hnreach.
    iMod ("H" with "[Hs]") as "H".
    { iFrame. iPureIntro. contradict Hnreach. by apply fill_reach_stuck. }
    iDestruct "H" as "[Hval | [Hstep | Hcall]]".
    - iDestruct "Hval" as (v_t v_s σ_s') "(%& %&Hstate&Hpost)".
      by iApply (sim_bind_val_nostutter with "[Hpost] [Hstate]").
    - (* simply thread through everything *)
      iModIntro. iRight; iLeft. iDestruct "Hstep" as "[% Hstep]".
      iSplitR. { iPureIntro. by apply fill_reducible. }
      iIntros (e_t' σ_t') "%".
      destruct (fill_reducible_prim_step _ _ _ _ _ _ H H0) as (e_t'' & -> & H1).
      iMod ("Hstep" with "[]") as "Hstep". { iPureIntro. apply H1. }
      iModIntro.
      iDestruct "Hstep" as (e_s' σ_s') "(% & Hstate & Hrec)".
      iExists (fill K_s e_s'), σ_s'. iFrame. iSplitR.
      { iPureIntro. by apply fill_prim_step_tc. }
      cbn. iExists e_t'', e_s', K_t, K_s.
      do 2 (iSplitR; first auto).
      rewrite sim_nostutter_eq. iApply "Hrec".
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
      rewrite sim_nostutter_eq. iApply "Hrec".
  Qed.

End fix_lang.

