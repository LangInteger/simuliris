
From iris Require Import bi bi.lib.fixpoint bi.updates bi.derived_laws.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import language slsls.



Section fix_lang.
  Context {PROP : bi}.

  Context {Λ : language}.
  Context {s : simul_lang PROP Λ}.
  Context {PROP_bupd : BiBUpd PROP}.
  Context {PROP_affine : BiAffine PROP}.

  Implicit Types
    (e_s e_t e: exprO (Λ := Λ))
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ).

Section global_no_stuttering.
  Definition global_step_nostutter (Φ : val Λ → val Λ → PROP) (greatest_rec : exprO * exprO → PROP) : exprO * exprO → PROP:=
    λ '(e_t, e_s), (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ -∗ |==>
      (* value case *)
      (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')⌝ ∗
      state_interp P_t σ_t P_s σ_s' ∗ Φ v_t v_s)

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
        ∃ e_s' σ_s', ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗
        greatest_rec (e_t', e_s'))
    )%I.

  Definition global_sim_nostutter_def (Φ : val Λ → val Λ → PROP) :=
    bi_greatest_fixpoint (global_step_nostutter Φ).

  Instance global_step_nostutter_proper Φ rec:
    Proper ((≡) ==> (≡)) (global_step_nostutter Φ rec).
  Proof. solve_proper. Qed.

  Instance global_step_nostutter_mono (Φ : val Λ → val Λ → PROP):
    BiMonoPred (global_step_nostutter Φ).
  Proof.
    constructor.
    - intros g1 g2. iIntros "#H".
      iIntros ([e_s e_t]) "Hg". rewrite /step_nostutter.
      iIntros (P_t σ_t P_s σ_s) "Ha".
      iMod ("Hg" with "Ha") as "[Hval | Hstep]"; iModIntro.
      + iLeft. iApply "Hval".
      + iRight. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
        iIntros (e_t' σ_t') "Hstep". iMod ("Hr" with "Hstep") as "Hstep"; iModIntro.
        iDestruct "Hstep" as (e_s' σ_s') "(H1& H2 &H3)".
        iExists (e_s'), (σ_s'). iFrame. by iApply "H".
  - intros g Hne n e1 e2 Heq.
    apply discrete_iff in Heq as ->. reflexivity. apply _.
  Qed.

  Lemma global_sim_nostutter_def_unfold Φ e_t e_s:
    global_sim_nostutter_def Φ (e_t, e_s) ⊣⊢ global_step_nostutter Φ (global_sim_nostutter_def Φ) (e_t, e_s).
  Proof. by rewrite /global_sim_nostutter_def greatest_fixpoint_unfold. Qed.

  Definition global_sim_nostutter_aux : seal (λ e_t e_s Φ, @global_sim_nostutter_def Φ (e_t, e_s)). by eexists. Qed.
  Definition gsim_expr := ((global_sim_nostutter_aux).(unseal)).
  Definition gsim_expr_eq : gsim_expr = λ e_t e_s Φ, @global_sim_nostutter_def Φ (e_t, e_s).
    by rewrite <- (global_sim_nostutter_aux).(seal_eq). Defined.

  Lemma gsim_expr_unfold_nostutter e_t e_s Φ:
    gsim_expr e_t e_s Φ ⊣⊢
    (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ -∗ |==>
      (* value case *)
      (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')⌝ ∗
      state_interp P_t σ_t P_s σ_s' ∗ Φ v_t v_s)

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
        ∃ e_s' σ_s', ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗
        gsim_expr e_t' e_s' Φ)
    )%I.
    Proof.
      by rewrite !gsim_expr_eq global_sim_nostutter_def_unfold /global_step_nostutter.
    Qed.
End global_no_stuttering.

Section local_to_global.

  Definition local_rel P_t P_s : PROP :=
    (□ ∀ f K_s, ⌜P_s !! f = Some K_s⌝ → ∃ K_t, ⌜P_t !! f = Some K_t⌝ ∗ sim_ectx (sim:=sim_nostutter) K_t K_s val_rel)%I.
  Typeclasses Opaque local_rel.

  Global Instance local_rel_persistent P_s P_t: Persistent (local_rel P_s P_t).
  Proof. rewrite /local_rel; apply _. Qed.

  Lemma gsim_coind (Φ : exprO * exprO → PROP) (Post: val Λ → val Λ → PROP) `{NonExpansive Φ}:
    □ (∀ e_t e_s, Φ (e_t, e_s) -∗ global_step_nostutter Post Φ (e_t, e_s)) -∗
    ∀ e_t e_s, Φ (e_t, e_s) -∗ gsim_expr e_t e_s Post.
  Proof.
    iIntros "#H" (e_t e_s). rewrite gsim_expr_eq.
    remember (e_t, e_s) as p; clear Heqp e_s e_t.
    iApply (greatest_fixpoint_coind with "[H]").
    iModIntro. iIntros ([e_s e_t]). iApply "H".
  Qed.

  Definition progs_are P_t P_s : PROP :=
    (□ ∀ P_s' P_t' σ_s σ_t, state_interp P_t' σ_t P_s' σ_s → ⌜P_t' = P_t⌝ ∧ ⌜P_s' = P_s⌝)%I.
  Typeclasses Opaque progs_are.

  Global Instance progs_are_persistent P_s P_t: Persistent (progs_are P_s P_t).
  Proof. rewrite /progs_are; apply _. Qed.

  Lemma local_to_global P_t P_s e_t e_s:
    local_rel P_t P_s -∗
    progs_are P_t P_s  -∗
    sim (Sim:=sim_nostutter) e_t e_s val_rel -∗
    gsim_expr e_t e_s val_rel.
  Proof.
    iIntros "#Hloc #Hprog Hsim".
    iApply (gsim_coind (λ '(e_t, e_s), sim e_t e_s val_rel) with "[] Hsim"); last clear e_t e_s.
    { by intros n [] [] [-> ->]. }
    iModIntro. rewrite /global_step_nostutter.
    iIntros (e_t e_s). erewrite sim_nostutter_unfold.
    iIntros "Hsim" (P_t' σ_t P_s' σ_s) "[Hstate %]".
    rewrite /progs_are; iDestruct ("Hprog" with "Hstate") as "[% %]"; subst P_t' P_s'.
    iMod ("Hsim" with "[$Hstate //]") as "[Hsim|[Hsim|Hsim]]"; iModIntro; [by eauto..|].
    iDestruct "Hsim" as (f K_t v_t K_s v_s σ_s') "(% & % & Hval & Hstate & Hcont)".
    subst e_t. iRight.

    (* the function is in the source table *)
    edestruct (@reach_call_in_prg Λ) as [K_f_s Hdef_s]; [by eauto..|].

    (* we prove reducibility and the step relation *)
    iSplit.
    - iAssert (∃ K_f_t, ⌜P_t !! f = Some K_f_t⌝)%I as (K_f_t) "%".
      { rewrite /local_rel; iDestruct ("Hloc" $! _ _ Hdef_s) as (K_f_t) "[% _]"; by eauto. }
      iPureIntro. eexists _, _.
      by apply fill_prim_step, head_prim_step, call_head_step_intro.
    - iIntros (e_t' σ_t' Hstep).
      apply prim_step_call_inv in Hstep as (K_f_t & Hdef & -> & ->).
      iModIntro. iExists (fill K_s (fill K_f_s (of_val v_s))), σ_s'.
      iFrame. iSplit.
      + iPureIntro. eapply tc_rtc_l; first by eauto.
        constructor. by apply fill_prim_step, head_prim_step, call_head_step_intro.
      + iApply sim_nostutter_bind. iApply (sim_nostutter_mono with "Hcont [Hval]").
        rewrite /local_rel; iDestruct ("Hloc" $! _ _ Hdef_s) as (K_f_t') "[% Hcont]".
        assert (K_f_t' = K_f_t) as -> by naive_solver.
        by iApply "Hcont".
  Qed.

End local_to_global.
End fix_lang.






