(** * SLSLS, Separation Logic Stuttering Local Simulation *)

From iris Require Import bi bi.lib.fixpoint bi.updates.
From iris.proofmode Require Import tactics.
From simuliris Require Import simulation.language.

Inductive prim_step_rtc {Λ} P : expr Λ → state Λ → expr Λ → state Λ → Prop :=
  | head_rtc_base e σ: prim_step_rtc P e σ e σ
  | head_rtc_step e1 e2 e3 σ1 σ2 σ3 : prim_step P e1 σ1 e2 σ2 → prim_step_rtc P e2 σ2 e3 σ3 → prim_step_rtc P e1 σ1 e3 σ3.
Hint Constructors prim_step_rtc : core.

Inductive prim_step_tc {Λ} P : expr Λ → state Λ → expr Λ → state Λ → Prop :=
  | head_tc_base e e' σ σ' : prim_step P e σ e' σ' → prim_step_tc P e σ e' σ'
  | head_tc_step e1 e2 e3 σ1 σ2 σ3 : prim_step P e1 σ1 e2 σ2 → prim_step_tc P e2 σ2 e3 σ3 → prim_step_tc P e1 σ1 e3 σ3.
Hint Constructors prim_step_tc : core.

Definition reach_stuck {Λ : language} (P : prog Λ) (e : expr Λ) (σ : state Λ) :=
  ∃ e' σ', prim_step_rtc P e σ e' σ' ∧ stuck P e' σ'.

Class simul_lang (PROP : bi) (Λ : language) := {
  (* state interpretation *)
  state_interp : prog Λ → state Λ → prog Λ → state Λ → PROP;
  (* value relation that restricts values passed to functions *)
  val_rel : val Λ → val Λ → PROP;
}.
Hint Mode simul_lang + - : typeclass_instances.

(** Typeclass for the simulation relation so we can use the definitions with
   greatest+least fp (stuttering) or just greatest fp (no stuttering). *)
(* TODO: remove this TC once we don't need the no-stutter version anymore*)
Class Sim {PROP : bi} {Λ : language} (s : simul_lang PROP Λ) := sim : expr Λ → expr Λ → (val Λ → val Λ → PROP) → PROP.
Hint Mode Sim + + - : typeclass_instances.

(* discrete OFE instance for expr *)
Definition exprO {Λ : language} := leibnizO (expr Λ).

Section fix_lang.
  Context {PROP : bi}.

  Context {Λ : language}.
  Context {s : simul_lang PROP Λ}.

  Definition sim_expr {sim : Sim s} e_t e_s Φ := sim e_t e_s Φ.
  Definition sim_ectx {sim : Sim s} K_t K_s Φ :=
    (∀ v_t v_s, val_rel v_t v_s -∗ sim_expr (fill K_t (of_val v_t)) (fill K_s (of_val v_s)) Φ)%I.

  Implicit Types
    (e_s e_t e: expr Λ)
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ).


  Context {PROP_bupd : BiBUpd PROP}.
  Context {PROP_affine : BiAffine PROP}.

  Section stuttering.
    (** Simulation relation with stuttering *)

    Definition least_step (Φ : val Λ → val Λ → PROP) (greatest_rec : expr Λ → expr Λ → PROP) (e_s : exprO) (least_rec : exprO → PROP) (e_t : exprO) :=
      (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ¬ ⌜reach_stuck P_s e_s σ_s⌝ -∗ |==>
        (* value case *)
        (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜prim_step_rtc P_s e_s σ_s (of_val v_s) σ_s'⌝ ∗ Φ v_t v_s)

        ∨ (* step case *)
        (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t'⌝ -∗ |==>
          (* stuttering *)
          (state_interp P_t σ_t' P_s σ_s ∗ least_rec e_t') ∨
          (* take a step *)
          (∃ e_s' σ_s', ⌜prim_step_tc P_s e_s σ_s e_s' σ_s'⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗ greatest_rec e_s' e_t'))

        ∨ (* call case *)
        (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
          ⌜prim_step_rtc P_s e_s σ_s (fill K_s (of_call f v_s)) σ_s'⌝ ∗
          val_rel v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
          (∀ v_t v_s, val_rel v_t v_s -∗ greatest_rec (fill K_s (of_val v_s)) (fill K_t (of_val v_t))))
      )%I.

    Lemma least_step_mon Φ l1 l2 g1 g2 e_s:
      ⊢ <pers> (∀ e, l1 e -∗ l2 e)
      → <pers> (∀ e_s e_t, g1 e_s e_t -∗ g2 e_s e_t)
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

    Definition sim_def (Φ : val Λ → val Λ → PROP) :=
      bi_greatest_fixpoint (greatest_step Φ).

    Lemma sim_def_unfold Φ e_s e_t:
      sim_def Φ (e_s, e_t) ⊣⊢ greatest_step Φ (sim_def Φ) (e_s, e_t).
    Proof. by rewrite /sim_def greatest_fixpoint_unfold. Qed.

    Lemma sim_def_least_def_unfold Φ e_s e_t :
      sim_def Φ (e_s, e_t) ⊣⊢ least_def Φ (uncurry (sim_def Φ)) e_s e_t.
    Proof. by rewrite sim_def_unfold. Qed.

    Definition sim_aux : seal (λ e_t e_s Φ, @sim_def Φ (e_s, e_t)). by eexists. Qed.
    Instance sim_stutter : Sim s. exact ((sim_aux).(unseal)). Defined.
    Definition sim_eq : sim_stutter = λ e_t e_s Φ, @sim_def Φ (e_s, e_t). by rewrite <- (sim_aux).(seal_eq). Defined.

    Lemma sim_expr_unfold Φ e_t e_s:
      sim_expr (sim:=sim_stutter) e_t e_s Φ ⊣⊢
      (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ¬ ⌜reach_stuck P_s e_s σ_s⌝ -∗ |==>
        (* value case *)
          (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜prim_step_rtc P_s e_s σ_s (of_val v_s) σ_s'⌝ ∗ Φ v_t v_s)

        ∨ (* step case *)
        (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t'⌝ -∗ |==>
          (state_interp P_t σ_t' P_s σ_s ∗ sim_expr (sim:=sim_stutter) e_t' e_s Φ) ∨
          (∃ e_s' σ_s', ⌜prim_step_tc P_s e_s σ_s e_s' σ_s'⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗
          sim_expr (sim:=sim_stutter) e_t' e_s' Φ))

        ∨ (* call case *)
        (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
          ⌜prim_step_rtc P_s e_s σ_s (fill K_s (of_call f v_s)) σ_s'⌝ ∗
          val_rel v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
          sim_ectx (sim:=sim_stutter) K_t K_s Φ)
      )%I.
    Proof.
      rewrite /sim_ectx /sim_expr !sim_eq /uncurry sim_def_unfold /greatest_step.
      rewrite least_def_unfold /least_step.
      by setoid_rewrite <-sim_def_least_def_unfold.
    Qed.

  End stuttering.

  Section no_stuttering.
    (** Simpler relation without stuttering using just a greatest fp. *)

    Definition step_nostutter (Φ : val Λ → val Λ → PROP) (greatest_rec : exprO * exprO → PROP) : exprO * exprO → PROP:=
      λ '(e_s, e_t), (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ¬ ⌜reach_stuck P_s e_s σ_s⌝ -∗ |==>
        (* value case *)
        (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜prim_step_rtc P_s e_s σ_s (of_val v_s) σ_s'⌝ ∗ Φ v_t v_s)

        ∨ (* step case *)
        (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t'⌝ -∗ |==>
          ∃ e_s' σ_s', ⌜prim_step_tc P_s e_s σ_s e_s' σ_s'⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗ greatest_rec (e_s', e_t'))

        ∨ (* call case *)
        (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
          ⌜prim_step_rtc P_s e_s σ_s (fill K_s (of_call f v_s)) σ_s'⌝ ∗
          val_rel v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
          (∀ v_t v_s, val_rel v_t v_s -∗ greatest_rec (fill K_s (of_val v_s), fill K_t (of_val v_t))))
      )%I.

    Definition sim_nostutter_def (Φ : val Λ → val Λ → PROP) :=
      bi_greatest_fixpoint (step_nostutter Φ).

    Instance step_nostutter_proper Φ rec:
      Proper ((≡) ==> (≡)) (step_nostutter Φ rec).
    Proof. solve_proper. Qed.

    Instance step_nostutter_mono (Φ : val Λ → val Λ → PROP):
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
        apply discrete_iff in Heq as ->. reflexivity. apply _.
    Qed.

    Lemma sim_nostutter_def_unfold Φ e_s e_t:
      sim_nostutter_def Φ (e_s, e_t) ⊣⊢ step_nostutter Φ (sim_nostutter_def Φ) (e_s, e_t).
    Proof. by rewrite /sim_nostutter_def greatest_fixpoint_unfold. Qed.

    Definition sim_nostutter_aux : seal (λ e_t e_s Φ, @sim_nostutter_def Φ (e_s, e_t)). by eexists. Qed.
    Instance sim_nostutter : Sim s. exact ((sim_nostutter_aux).(unseal)). Defined.
    Definition sim_nostutter_eq : sim_nostutter = λ e_t e_s Φ, @sim_nostutter_def Φ (e_s, e_t).
      by rewrite <- (sim_nostutter_aux).(seal_eq). Defined.

    Lemma sim_expr_unfold_nostutter e_t e_s Φ:
      sim_expr (sim:=sim_nostutter) e_t e_s Φ ⊣⊢
      (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ¬ ⌜reach_stuck P_s e_s σ_s⌝ -∗ |==>
        (* value case *)
          (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜prim_step_rtc P_s e_s σ_s (of_val v_s) σ_s'⌝ ∗ Φ v_t v_s)

        ∨ (* step case *)
        (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t'⌝ -∗ |==>
          ∃ e_s' σ_s', ⌜prim_step_tc P_s e_s σ_s e_s' σ_s'⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗
          sim_expr (sim:=sim_nostutter) e_t' e_s' Φ)

        ∨ (* call case *)
        (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
          ⌜prim_step_rtc P_s e_s σ_s (fill K_s (of_call f v_s)) σ_s'⌝ ∗
          val_rel v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
          sim_ectx (sim:=sim_nostutter) K_t K_s Φ)
      )%I.
    Proof.
      by rewrite /sim_ectx /sim_expr !sim_nostutter_eq /uncurry sim_nostutter_def_unfold /step_nostutter.
    Qed.
  End no_stuttering.
End fix_lang.
