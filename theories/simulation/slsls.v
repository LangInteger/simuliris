(** * SLSLS, Separation Logic Stuttering Local Simulation *)

From iris Require Import bi.bi bi.lib.fixpoint.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import relations language.

Class simul_lang (PROP : bi) (Λ : language) := {
  (* state interpretation *)
  state_interp : prog Λ → state Λ → prog Λ → state Λ → PROP;
  (* value relation that restricts values passed to functions *)
  val_rel : val Λ → val Λ → PROP;
}.
#[global]
Hint Mode simul_lang + - : typeclass_instances.

Definition progs_are {Λ PROP} `{simul_lang PROP Λ} (P_t P_s: prog Λ) : PROP :=
  (□ ∀ P_t' P_s' σ_t σ_s, state_interp P_t' σ_t P_s' σ_s → ⌜P_t' = P_t⌝ ∧ ⌜P_s' = P_s⌝)%I.
#[global]
Hint Mode progs_are - - - + + : typeclass_instances.
Typeclasses Opaque progs_are.

Global Instance progs_are_persistent {Λ} {PROP} `{s: simul_lang PROP Λ} (P_s P_t: prog Λ): Persistent (@progs_are Λ PROP s P_s P_t).
Proof. rewrite /progs_are; apply _. Qed.

(** Typeclass for the simulation relation so we can use the definitions with
   greatest+least fp (stuttering) or just greatest fp (no stuttering). *)
(* TODO: remove this TC once we don't need the no-stutter version anymore*)
Class Sim {PROP : bi} {Λ : language} (s : simul_lang PROP Λ) := sim : expr Λ → expr Λ → (val Λ → val Λ → PROP) → PROP.
#[global]
Hint Mode Sim - - - : typeclass_instances.

(* FIXME: the notation with binders somehow does not work *)
(*Notation "et '⪯' es {{ v_t v_s , P }}" := (sim et es (λ v_t v_s, P)) (at level 40, v_t pattern, v_s pattern) : bi_scope.*)
Notation "et '⪯' es {{ Φ }}" := (sim et es Φ) (at level 40) : bi_scope.

(* discrete OFE instance for expr *)
Definition exprO {Λ : language} := leibnizO (expr Λ).
Instance expr_equiv {Λ} : Equiv (expr Λ). apply exprO. Defined.

Section fix_lang.
  Context {PROP : bi}.

  Context {Λ : language}.
  Context {s : simul_lang PROP Λ}.

  Definition sim_ectx {sim : Sim s} K_t K_s Φ :=
    (∀ v_t v_s, val_rel v_t v_s -∗ sim (fill K_t (of_val v_t)) (fill K_s (of_val v_s)) Φ)%I.

  Implicit Types
    (e_s e_t e: exprO (Λ := Λ))
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ).


  Context {PROP_bupd : BiBUpd PROP}.
  Context {PROP_affine : BiAffine PROP}.

  Section stuttering.
    (** Simulation relation with stuttering *)

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

        ∨ (* call case *)
        (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
          ⌜rtc (prim_step P_s) (e_s, σ_s) (fill K_s (of_call f v_s), σ_s')⌝ ∗
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

    Lemma sim_unfold Φ e_t e_s:
      sim (Sim:=sim_stutter) e_t e_s Φ ⊣⊢
      (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ -∗ |==>
        (* value case *)
          (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')⌝ ∗
            state_interp P_t σ_t P_s σ_s' ∗ Φ v_t v_s)

        ∨ (* step case *)
        (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
          (state_interp P_t σ_t' P_s σ_s ∗ sim (Sim:=sim_stutter) e_t' e_s Φ) ∨
          (∃ e_s' σ_s', ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗
          sim (Sim:=sim_stutter) e_t' e_s' Φ))

        ∨ (* call case *)
        (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
          ⌜rtc (prim_step P_s) (e_s, σ_s) (fill K_s (of_call f v_s), σ_s')⌝ ∗
          val_rel v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
          sim_ectx (sim:=sim_stutter) K_t K_s Φ)
      )%I.
    Proof.
      rewrite /sim_ectx /sim !sim_eq /uncurry sim_def_unfold /greatest_step.
      rewrite least_def_unfold /least_step.
      by setoid_rewrite <-sim_def_least_def_unfold.
    Qed.

    (* any post-fixed point is included in the gfp *)
    Lemma sim_coind Φ (Ψ : exprO → exprO → PROP):
      Proper ((≡) ==> (≡) ==> (≡)) Ψ →
      ⊢ (□ ∀ e_t e_s, Ψ e_t e_s -∗ greatest_step Φ (λ '(e_s, e_t), Ψ e_t e_s) (e_s, e_t))
        -∗ ∀ e_t e_s, Ψ e_t e_s -∗ sim e_t e_s Φ.
    Proof.
      iIntros (Hp) "#H". iIntros (e_t e_s) "H0".
      rewrite /sim sim_eq /sim_def.

      set (Ψ_curry := (λ '(e_t, e_s), Ψ e_s e_t)).
      assert (NonExpansive Ψ_curry) as Hne.
      { intros ? [e1 e2] [e1' e2'] [H1 H2]. rewrite /Ψ_curry. cbn in H1, H2.
        apply equiv_dist, Hp. now apply discrete_iff in H1. now apply discrete_iff in H2.
      }
      iApply (greatest_fixpoint_coind (greatest_step Φ) Ψ_curry).
      { iModIntro. iIntros ([e_s' e_t']). iApply "H". }
      iApply "H0".
    Qed.


    (* TODO: not sure yet if this lemma is useful. if not, remove *)
    Lemma sim_strong_ind' (e_s : exprO) Φ (Ψ : exprO → exprO → (val Λ → val Λ → PROP) → PROP):
      Proper ((≡) ==> (≡) ==> (pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> (≡)) Ψ →
      ⊢ (□ ∀ e_t, least_step Φ (uncurry (sim_def Φ)) e_s
              (λ e_t', Ψ e_t' e_s Φ ∧ least_def Φ (uncurry (sim_def Φ)) e_s e_t')
            e_t -∗ Ψ e_t e_s Φ)
        -∗ ∀ e_t : exprO, (e_t ⪯ e_s {{ Φ }}) -∗ Ψ e_t e_s Φ.
    Proof.
      iIntros (Hp) "#IH". iIntros (e_t).
      rewrite /sim sim_eq /sim_def.
      rewrite greatest_fixpoint_unfold {2}/greatest_step /least_def.

      change (bi_greatest_fixpoint (greatest_step Φ)) with (sim_def Φ).
      set (g_rec := least_step Φ (uncurry (sim_def Φ)) e_s).

      set (Ψ' := (λ e_t, Ψ e_t e_s Φ) : exprO → PROP).
      iAssert ((□ (∀ e_t : exprO, g_rec (λ e_t' : exprO, Ψ' e_t' ∧ bi_least_fixpoint g_rec e_t') e_t -∗ Ψ' e_t)))%I as "#H".
      { iModIntro. iApply "IH". }
      iPoseProof (least_fixpoint_strong_ind g_rec Ψ' with "H") as "Htemp".
      unfold Ψ'. iApply "Htemp".
    Qed.

    (* TODO: not sure yet if this lemma is useful. if not, remove *)
    Lemma sim_ind' (e_s : exprO) Φ (Ψ : exprO → exprO → (val Λ → val Λ → PROP) → PROP):
      Proper ((≡) ==> (≡) ==> (pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> (≡)) Ψ →
      ⊢ (□ ∀ e_t, least_step Φ (uncurry (sim_def Φ)) e_s (λ e_t', Ψ e_t' e_s Φ) e_t -∗ Ψ e_t e_s Φ)
        -∗ ∀ e_t : exprO, e_t ⪯ e_s {{Φ}} -∗ Ψ e_t e_s Φ.
    Proof.
      iIntros (Hp) "#IH". iApply sim_strong_ind'. iModIntro.
      iIntros (e_t) "H". iApply "IH".
      iApply least_step_mon. 3: iApply "H". 2: auto.
      iModIntro. by iIntros (e) "[H _]".
    Qed.

    Lemma sim_strong_ind greatest_rec (e_s : exprO) Φ (Ψ : exprO → PROP):
      Proper ((≡) ==> (≡)) Ψ →
      ⊢ (□ ∀ e_t, least_step Φ greatest_rec e_s
            (λ e_t', Ψ e_t' ∧ least_def Φ greatest_rec e_s e_t')
          e_t -∗ Ψ e_t)
        -∗ ∀ e_t : exprO, least_def Φ greatest_rec e_s e_t -∗ Ψ e_t.
    Proof.
      iIntros (Hp) "#H". iApply least_fixpoint_strong_ind.
      iModIntro. iIntros (e_t) "IH". by iApply "H".
    Qed.

    Lemma sim_ind greatest_rec (e_s : exprO) Φ (Ψ : exprO → PROP):
      Proper ((≡) ==> (≡)) Ψ →
      ⊢ (□ ∀ e_t, least_step Φ greatest_rec e_s Ψ e_t -∗ Ψ e_t)
        -∗ ∀ e_t : exprO, least_def Φ greatest_rec e_s e_t -∗ Ψ e_t.
    Proof. iIntros (Hp) "#H". iApply least_fixpoint_ind. iModIntro. iIntros (e_t) "IH". by iApply "H". Qed.

    Instance sim_proper :
      Proper (eq ==> eq ==> (pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> (≡)) sim.
    Proof.
      intros e e' -> e1 e1' -> p1 p2 Heq2.
      rewrite /sim !sim_eq. apply greatest_fixpoint_proper; last reflexivity.
      intros p3 [e3 e3']. rewrite /greatest_step /least_def.
      apply least_fixpoint_proper; last reflexivity. solve_proper.
    Qed.

    Lemma sim_value Φ v_t v_s:
      ⊢ (Φ v_t v_s) -∗ (of_val v_t) ⪯ (of_val v_s) {{Φ}}.
    Proof.
      iIntros "Hv". rewrite sim_unfold. iIntros (????) "[Hstate Hreach]".
      iModIntro. iLeft. iExists (v_t), (v_s), (σ_s). iFrame.
      iSplitL. by rewrite to_of_val. eauto.
    Qed.

    Lemma sim_stutter_incl Φ e_s e_t:
      ⊢ least_def Φ (uncurry (sim_def Φ)) e_s e_t
        -∗ e_t ⪯ e_s {{Φ}}.
    Proof. iIntros "H". by rewrite /sim sim_eq sim_def_unfold /greatest_step. Qed.

    Lemma bupd_sim Φ e_t e_s:
      ⊢ (|==> e_t ⪯ e_s {{Φ}}) -∗ e_t ⪯ e_s {{Φ}}.
    Proof.
      iIntros "Hv". rewrite sim_unfold. iIntros (????) "H". iMod "Hv". iApply ("Hv" with "H").
    Qed.

    Lemma sim_bupd Φ e_t e_s:
      ⊢ (e_t ⪯ e_s {{λ v_t v_s, |==> Φ v_t v_s}}) -∗ e_t ⪯ e_s {{Φ}}.
    Proof.
      iIntros "Hv".
      iApply (sim_coind Φ (λ e_t e_s, e_t ⪯ e_s {{λ v_t v_s, |==> Φ v_t v_s}})%I); last by iFrame.
      iModIntro. clear e_t e_s. iIntros (e_t e_s) "Hv". 
      rewrite sim_unfold /greatest_step least_def_unfold /least_step.
      iIntros (????) "H". iMod ("Hv" with "H") as "Hv". 
      iDestruct "Hv" as "[Hv | [H | H]]". 
      - iDestruct "Hv" as (v_t v_s σ_s') "(H1 & H2 & H3 & >H4)". 
        iModIntro. iLeft. iExists v_t, v_s, σ_s'. iFrame. 
      - iModIntro. iRight; iLeft. iDestruct "H" as "[Hred H]"; iFrame. 
        iIntros (??) "Hs". iMod ("H" with "Hs") as "[[? Hs] | Hs]"; iModIntro. 
        + iLeft. iFrame. 
          iApply sim_ind. 2: { rewrite /sim sim_eq sim_def_least_def_unfold. iFrame. } 
          iModIntro. clear e_t' P_t P_s σ_t' σ_t σ_s. iIntros (e_t') "IH". 
          rewrite least_def_unfold !/least_step. 
          iIntros (????) "H". iMod ("IH" with "H") as "Hv". 
          iDestruct "Hv" as "[Hv | [H | H]]". 
          * iDestruct "Hv" as (v_t v_s σ_s') "(H1 & H2 & H3 & >H4)". 
            iModIntro. iLeft. iExists v_t, v_s, σ_s'. iFrame. 
          * iModIntro. iRight; iLeft. iDestruct "H" as "[Hred H]"; iFrame. 
            iIntros (??) "Hs". iMod ("H" with "Hs") as "[[? Hs] | Hs]"; iModIntro. 
            { iLeft. iFrame. } 
            iRight. rewrite /sim sim_eq. iFrame. 
          * iModIntro. iRight; iRight. rewrite /sim sim_eq. iFrame. 
        + iRight. iFrame. 
      - iModIntro. iRight; iRight. iFrame. 
    Qed.

    (* we change the predicate beause at every recursive ocurrence,
       we give back ownership of the monotonicity assumption *)
    Lemma least_def_mono rec Φ Φ':
      ⊢ (∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s)
        -∗ ∀ e_s e_t : exprO, least_def Φ rec e_s e_t -∗
        least_def Φ' (λ e_s e_t, rec e_s e_t ∗ ∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) e_s e_t.
    Proof.
      iIntros "Hmon" (e_s e_t). iIntros "Hleast". iRevert "Hmon".
      iApply (sim_ind _ _ _ (λ e_t, (∀ v_t v_s : val Λ, Φ v_t v_s -∗ Φ' v_t v_s) -∗ least_def Φ' (λ e_s e_t, rec e_s e_t ∗ ∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) e_s e_t)%I with "[] Hleast"); clear e_t.
      iModIntro. iIntros (e_t) "IH Hmon". rewrite least_def_unfold /least_step.
      iIntros (P_t σ_t P_s σ_s) "H". iMod ("IH" with "H") as "IH". iModIntro.
      iDestruct "IH" as "[Hval | [Hstep | Hcall]]".
      - iLeft. iDestruct "Hval" as (v_t v_s σ_s') "(?&?&?&?)". iExists v_t, v_s, σ_s'. iFrame. by iApply "Hmon".
      - iRight; iLeft. iDestruct "Hstep" as "[$ Hstep]". iIntros (e_t' σ_t' Hstep).
        iMod ("Hstep" with "[//]") as "[Hstep|Hstep]".
        + iModIntro. iLeft. iDestruct "Hstep" as "[$ H]". by iApply "H".
        + iModIntro. iRight. iFrame "Hmon". eauto.
      - iRight; iRight. by iFrame "Hmon".
    Qed.

    Lemma sim_mono Φ Φ':
      ⊢ (∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s)
         -∗ ∀ e_s e_t : exprO, e_t ⪯ e_s {{Φ}} -∗ e_t ⪯ e_s {{Φ'}}.
    Proof.
      iIntros "Hmon" (e_s e_t) "H".
      iApply (sim_coind Φ' (λ e_t e_s, e_t ⪯ e_s {{Φ}} ∗ (∀ v_t v_s : val Λ, Φ v_t v_s -∗ Φ' v_t v_s))%I); last by iFrame.
      iModIntro. clear e_t e_s. iIntros (e_t e_s) "[H Hmon]".
      rewrite /sim sim_eq sim_def_unfold.
      rewrite /greatest_step !least_def_unfold /least_step.
      iIntros (????) "Hs". iSpecialize ("H" with "Hs"). iMod "H". iModIntro.
      iDestruct "H" as "[Hval | [Hred | Hcall]]".
      - iLeft. iDestruct "Hval" as (v_t v_s σ_s') "(?&?&?&?)". iExists v_t, v_s, σ_s'. iFrame. by iApply "Hmon".
      - iRight; iLeft. iDestruct "Hred" as "[Hred Hstep]". iFrame.
        iIntros (e_t' σ_t') "Hprim". iMod ("Hstep" with "Hprim") as "[Hstutter | Hstep]"; iModIntro.
        + iLeft. iDestruct "Hstutter" as "[Hstate Hleast]". iFrame. by iApply (least_def_mono with "Hmon").
        + iRight. by iFrame.
      - iRight; iRight. iFrame.
    Qed.

    (* TODO: clean up the bind lemma proof *)
    (* coinduction predicate used for the bind lemma *)
    Definition bind_pred Φ := uncurry (λ '(e_s, e_t), ∃ e_t' e_s' (K_t K_s : ectx Λ),
      ⌜e_t = fill K_t e_t'⌝ ∧ ⌜e_s = fill K_s e_s'⌝ ∧
       e_t' ⪯ e_s' {{λ v_t v_s : val Λ, fill K_t (of_val v_t) ⪯ fill K_s (of_val v_s) {{Φ}}}})%I.

    (* Lemma used two times in the proof of the bind lemma (for the value cases of the inner and outer induction) *)
    Lemma sim_bind_val P_s e_s σ_s v_s σ_s' e_t v_t K_t σ_t P_t K_s Φ:
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
                (* stutter *)
                state_interp P_t σ_t' P_s σ_s ∗ least_def Φ (bind_pred Φ) (fill K_s e_s) e_t'
                ∨ (* step *)
                (∃ e_s' σ_s'',
                 ⌜tc (prim_step P_s) (fill K_s e_s, σ_s) (e_s', σ_s'')⌝ ∗ state_interp P_t σ_t' P_s σ_s'' ∗
                 bind_pred Φ e_s' e_t'))
          ∨ (* call case *)
            (∃ (f : string) (K_t' : ectx Λ) (v_t' : val Λ) (K_s' : ectx Λ) (v_s' : val Λ) σ_s'',
              ⌜fill K_t e_t = fill K_t' (of_call f v_t')⌝ ∗
              ⌜rtc (prim_step P_s) (fill K_s e_s, σ_s) (fill K_s' (of_call f v_s'), σ_s'')⌝ ∗
              val_rel v_t' v_s' ∗ state_interp P_t σ_t P_s σ_s'' ∗
              (∀ v_t'' v_s'' : val Λ, val_rel v_t'' v_s'' -∗
                bind_pred Φ (fill K_s' (of_val v_s'')) (fill K_t' (of_val v_t'')))).
    Proof.
      (* unfold Hpost to examine the result and combine the two simulation proofs *)
      iIntros (H0 H Hnreach) "Hpost Hstate".
      rewrite {1}/sim {1}sim_eq {1}sim_def_unfold.
      rewrite {1}/greatest_step !least_def_unfold /least_step.
      iMod ("Hpost" with "[Hstate]") as "Hpost".
      { iFrame. iPureIntro. intros Hstuck. eapply Hnreach, prim_step_rtc_reach_stuck.
        by apply fill_prim_step_rtc. assumption. }
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
            rewrite !fill_empty. do 2 (iSplitL ""; first auto).
            iApply sim_mono. 2: { rewrite /sim sim_eq. iApply "H". }
            iIntros (v_t' v_s') "Hv". rewrite !fill_empty. by iApply sim_value.
          }
          {
            iRight. iExists (fill K_s (of_val v_s)), σ_s'. iFrame.
            iSplitR "Hstutter".
            { iPureIntro. by apply fill_prim_step_tc. }
            cbn. iExists e_t', (fill K_s (of_val v_s)), empty_ectx, empty_ectx. rewrite !fill_empty.
            do 2 (iSplitL ""; first auto).
            iApply sim_mono. 2: { iApply sim_stutter_incl. iApply "Hstutter". }
            iIntros (v_t' v_s') "Hv". rewrite !fill_empty. by iApply sim_value.
          }
        * iDestruct "Hstep" as (e_s' σ_s'') "(%&Hstate& Hrec)". iRight.
          iExists e_s', σ_s''. iFrame. iSplitL "".
          { iPureIntro. eapply tc_rtc_l; by eauto using fill_prim_step_rtc. }
          cbn. iExists e_t', e_s', empty_ectx, empty_ectx. rewrite !fill_empty.
          do 2 (iSplitL ""; first auto).
          iApply sim_mono. 2: { rewrite /sim sim_eq. iApply "Hrec". }
          iIntros (??) "H". rewrite !fill_empty.
          by iApply sim_value.
      + iDestruct "Hcall" as (f K_t' v_t' K_s' v_s' σ_s'') "(%&%&Hvrel&Hstate&Hcall)".
        (* CA on the reduction of fill K_s v_s to fill K_s' (f v_s') to see if we need to take a step or do the call *)
        iRight; iRight.
        iExists f, K_t', v_t', K_s', v_s', σ_s''. iFrame.
        iSplitL "". { iPureIntro. by rewrite -H1 (of_to_val _ _ H). }
        iSplitL "". { iPureIntro. etrans; eauto using fill_prim_step_rtc. }
        iIntros (v_t'' v_s'') "Hvrel". cbn.
        iExists (fill K_t' (of_val v_t'')), (fill K_s' (of_val v_s'')), empty_ectx, empty_ectx.
        rewrite !fill_empty. do 2 (iSplitL ""; first auto).
        iApply sim_mono; first last.
        { rewrite /sim sim_eq. by iApply "Hcall". }
        iIntros (??) "H". rewrite !fill_empty. by iApply sim_value.
    Qed.

    Lemma sim_bind e_t e_s K_t K_s Φ:
      ⊢ e_t ⪯ e_s {{λ v_t v_s : val Λ, fill K_t (of_val v_t) ⪯ fill K_s (of_val v_s) {{Φ}} }}
        -∗ fill K_t e_t ⪯ fill K_s e_s {{Φ}}.
    Proof.
      iIntros "H".
      iApply (sim_coind Φ (λ e_t' e_s', bind_pred Φ e_s' e_t')%I).
      2: { iExists e_t, e_s, K_t, K_s. iFrame. eauto. }
      iModIntro. clear e_t e_s K_t K_s.
      iIntros (e_t' e_s') "IH".
      iDestruct "IH" as (e_t e_s K_t K_s) "[-> [-> H]]".
      rewrite {1}/sim {1}sim_eq {1}sim_def_unfold.
      rewrite /greatest_step !least_def_unfold /least_step.

      iIntros (????) "[Hs %]". rename H into Hnreach.
      iMod ("H" with "[Hs]") as "H".
      { iFrame. iPureIntro. contradict Hnreach. by apply fill_reach_stuck. }
      iDestruct "H" as "[Hval | [Hstep | Hcall]]".
      - iDestruct "Hval" as (v_t v_s σ_s') "(%& %&Hstate&Hpost)".
        by iApply (sim_bind_val with "[Hpost] [Hstate]").
      - (* simply thread through everything *)
        iModIntro. iRight; iLeft. iDestruct "Hstep" as "[% Hstep]".
        iSplitL "". { iPureIntro. by apply fill_reducible. }
        iIntros (e_t' σ_t') "%".
        destruct (fill_reducible_prim_step _ _ _ _ _ _ H H0) as (e_t'' & -> & H1).
        iMod ("Hstep" with "[]") as "Hstep". { iPureIntro. apply H1. }
        iModIntro. iDestruct "Hstep" as "[[Hstate Hstutter] | Hstep]".
        + iLeft. iFrame.
          (* inner induction *)
          iApply (sim_ind _ _ _ (λ e_t'', least_def Φ (bind_pred Φ) (fill K_s e_s) (fill K_t e_t''))%I); last done.
          clear H0 H1 e_t'' H e_t σ_t P_t Hnreach P_s σ_s.
          iModIntro. iIntros (e_t'') "IH". rewrite least_def_unfold /least_step.
          iIntros (????) "[Hstate %]". iMod ("IH" with "[Hstate ]") as "IH".
          { iFrame. iPureIntro. contradict H. by apply fill_reach_stuck. }
          iDestruct "IH" as "[Hval | [Hred | Hcall]]".
          * iDestruct "Hval" as (v_t v_s σ_s') "(% & % & Hstate & Hrec)".
            by iApply (sim_bind_val with "[Hrec] [Hstate]").
          * iModIntro. iDestruct "Hred" as "[% Hred]". iRight; iLeft. iSplitL "".
            { iPureIntro. by apply fill_reducible. }
            iIntros (e_t' σ_t'') "%".
            destruct (fill_reducible_prim_step _ _ _ _ _ _ H0 H1) as (e_t''' & -> & H2).
            iMod ("Hred" with "[ //]") as "[Hstutter | Hstep]"; iModIntro.
            by iLeft.
            iRight. iDestruct "Hstep" as (e_s' σ_s') "(%&Hstate&Hrec)".
            iExists (fill K_s e_s'), σ_s'. iFrame. iSplitL "".
            { iPureIntro. by apply fill_prim_step_tc. }
            cbn. iExists e_t''', e_s', K_t, K_s. do 2 (iSplitL ""; first auto).
            by rewrite /sim sim_eq.
          * iModIntro. iDestruct "Hcall" as (f K_t' v_t K_s' v_s σ_s') "(-> & % & Hv & Hstate & Hcall)".
            iRight; iRight. iExists f, (comp_ectx K_t K_t'), v_t, (comp_ectx K_s K_s'), v_s, σ_s'.
            iSplitL "". { by rewrite fill_comp. }
            iSplitL "". { iPureIntro. rewrite -fill_comp. by apply fill_prim_step_rtc. }
            iFrame. iIntros (v_t' v_s') "Hv".
            cbn. iExists (fill K_t' (of_val v_t')), (fill K_s' (of_val v_s')), K_t, K_s.
            rewrite !fill_comp. do 2 (iSplitL ""; first auto).
            rewrite /sim sim_eq. by iApply "Hcall".
        + iRight. iDestruct "Hstep" as (e_s' σ_s') "(% & Hstate & Hrec)".
          iExists (fill K_s e_s'), σ_s'. iFrame. iSplitL "".
          { iPureIntro. by apply fill_prim_step_tc. }
          cbn. iExists e_t'', e_s', K_t, K_s.
          do 2 (iSplitL ""; first auto).
          rewrite /sim sim_eq. iApply "Hrec".
      - (* simply thread through everything *)
        iModIntro. iRight; iRight.
        iDestruct "Hcall" as (f K_t' v_t K_s' v_s σ_s') "(-> & % & Hval & Hstate & Hrec)".
        iExists f, (comp_ectx K_t K_t'), v_t, (comp_ectx K_s K_s'), v_s, σ_s'.
        iSplitL "". by rewrite fill_comp.
        iSplitL "". { iPureIntro. rewrite -fill_comp. by apply fill_prim_step_rtc. }
        iFrame.
        iIntros (v_t' v_s') "Hv". iSpecialize ("Hrec" with "Hv"). cbn.
        iExists (fill K_t' (of_val v_t')), (fill K_s' (of_val v_s')), K_t, K_s.
        iSplitL "". by rewrite -fill_comp. iSplitL "". by rewrite -fill_comp.
        rewrite /sim sim_eq. iApply "Hrec".
    Qed.


    (** Corollaries *)
    Lemma sim_call P_t P_s v_t v_s K_t K_s f Φ:
      P_t !! f = Some K_t →
      P_s !! f = Some K_s →
      ⊢ progs_are P_t P_s ∗ val_rel v_t v_s ∗ sim_ectx K_t K_s Φ -∗ (of_call f v_t) ⪯ (of_call f v_s) {{Φ}}.
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

    Lemma sim_frame_r e_t e_s R Φ :
      e_t ⪯ e_s {{Φ}} ∗ R ⊢ e_t ⪯ e_s {{λ v_t v_s, Φ v_t v_s ∗ R}}.
    Proof.
      iIntros "[Hsim HR]". iApply (sim_mono with "[HR] [Hsim//]"). iIntros (v_t v_s) "H". iFrame.
    Qed.

    Lemma sim_frame_l e_t e_s R Φ :
      R ∗ e_t ⪯ e_s {{Φ}} ⊢ e_t ⪯ e_s {{λ v_t v_s, R ∗ Φ v_t v_s}}.
    Proof.
      iIntros "[HR Hsim]". iApply (sim_mono with "[HR] [Hsim//]"). iIntros (v_t v_s) "H". iFrame.
    Qed.

    Lemma sim_wand e_t e_s Φ Ψ:
      e_t ⪯ e_s {{Φ}} -∗ (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) -∗ e_t ⪯ e_s {{Ψ}}.
    Proof. iIntros "H Hv". iApply (sim_mono with "[Hv//] [H//]"). Qed.

    Lemma sim_wand_l e_t e_s Φ Ψ:
      (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) ∗ e_t ⪯ e_s {{Φ}} ⊢ e_t ⪯ e_s {{Ψ}}.
    Proof. iIntros "[Hv H]". iApply (sim_wand with "[H//] [Hv//]"). Qed.

    Lemma sim_wand_r e_t e_s Φ Ψ:
      e_t ⪯ e_s {{Φ}} ∗ (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) ⊢ e_t ⪯ e_s {{Ψ}}.
    Proof. iIntros "[H Hv]". iApply (sim_wand with "[H//] [Hv//]"). Qed.

    Lemma sim_stutter_source e_t e_s Φ:
      ⊢ (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ==∗ ⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t',
          ⌜ prim_step P_t (e_t, σ_t) (e_t', σ_t') ⌝ ==∗ state_interp P_t σ_t' P_s σ_s ∗ e_t' ⪯ e_s {{ Φ }}) -∗
        e_t ⪯ e_s {{ Φ }}.
    Proof.
      iIntros "H". rewrite (sim_unfold Φ e_t e_s). iIntros (????) "[H1 H2]".
      iMod ("H" with "H1") as "H". iModIntro. iRight; iLeft. iDestruct "H" as "(% & Hnext)".
      iSplitL "". { by iPureIntro. }
      iIntros (e_t' σ_t') "Hstep". iMod ("Hnext" with "Hstep") as "[Hstate Hsim]".
      iModIntro. iLeft. iFrame.
    Qed.

    (* the step case of the simulation relation, but the two cases are combined into an rtc in the source *)
    Lemma sim_step_target e_t e_s Φ: 
      ⊢ ( ∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ==∗ ⌜ reducible P_t e_t σ_t⌝ ∗ (∀ e_t' σ_t', 
          ⌜ prim_step P_t (e_t, σ_t) (e_t', σ_t') ⌝ ==∗ ∃ e_s' σ_s', 
          ⌜ rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s') ⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗ e_t' ⪯ e_s' {{Φ}})) -∗ 
        e_t ⪯ e_s {{Φ}}.
    Proof. 
      iIntros "H". rewrite (sim_unfold Φ e_t e_s). iIntros (????) "[Hstate %]".
      iMod ("H" with "Hstate") as "[Hred H]". iModIntro. iRight; iLeft. 
      iFrame. iIntros (e_t' σ_t') "Hstep". iMod ("H" with "Hstep") as "H". iModIntro. 
      iDestruct "H" as (e_s' σ_s') "(%&H2&H3)". 
      apply rtc_inv_tc in H0 as [[= -> ->] | H0]. 
      - iLeft. iFrame. 
      - iRight; iExists e_s', σ_s'. iFrame. by iPureIntro.
    Qed.
  End stuttering.

  Section no_stuttering.
    (** Simpler relation without stuttering using just a greatest fp. *)

    Definition step_nostutter (Φ : val Λ → val Λ → PROP) (greatest_rec : exprO * exprO → PROP) : exprO * exprO → PROP:=
      λ '(e_s, e_t), (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ -∗ |==>
        (* value case *)
        (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')⌝ ∗
          state_interp P_t σ_t P_s σ_s' ∗ Φ v_t v_s)

        ∨ (* step case *)
        (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
          ∃ e_s' σ_s', ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗ greatest_rec (e_s', e_t'))

        ∨ (* call case *)
        (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
          ⌜rtc (prim_step P_s) (e_s, σ_s) (fill K_s (of_call f v_s), σ_s')⌝ ∗
          val_rel v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
          (∀ v_t v_s, val_rel v_t v_s -∗ greatest_rec (fill K_s (of_val v_s), fill K_t (of_val v_t))))
      )%I.

    Definition sim_nostutter_def (Φ : val Λ → val Λ → PROP) :=
      bi_greatest_fixpoint (step_nostutter Φ).

    Instance step_nostutter_proper:
      Proper ((pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡)))
        ==> (pointwise_relation _ (≡))
        ==> (≡) ==> (≡)) (step_nostutter).
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

    Lemma sim_nostutter_unfold e_t e_s Φ:
      sim (Sim:=sim_nostutter) e_t e_s Φ ⊣⊢
      (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ -∗ |==>
        (* value case *)
          (∃ v_t v_s σ_s', ⌜to_val e_t = Some v_t⌝ ∗ ⌜rtc (prim_step P_s) (e_s, σ_s) (of_val v_s, σ_s')⌝ ∗
            state_interp P_t σ_t P_s σ_s' ∗ Φ v_t v_s)

        ∨ (* step case *)
        (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ -∗ |==>
          ∃ e_s' σ_s', ⌜tc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗
          sim (Sim:=sim_nostutter) e_t' e_s' Φ)

        ∨ (* call case *)
        (∃ f K_t v_t K_s v_s σ_s', ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
          ⌜rtc (prim_step P_s) (e_s, σ_s) (fill K_s (of_call f v_s), σ_s')⌝ ∗
          val_rel v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
          sim_ectx (sim:=sim_nostutter) K_t K_s Φ)
      )%I.
    Proof.
      by rewrite /sim_ectx /sim !sim_nostutter_eq /uncurry sim_nostutter_def_unfold /step_nostutter.
    Qed.

    Lemma sim_nostutter_coind Φ (Ψ : exprO → exprO → PROP):
      Proper ((≡) ==> (≡) ==> (≡)) Ψ →
      ⊢ (□ ∀ e_t e_s, Ψ e_t e_s -∗ step_nostutter Φ (λ '(e_s', e_t'), Ψ e_t' e_s') (e_s, e_t))
        → (∀ e_t e_s, Ψ e_t e_s -∗ e_t ⪯ e_s {{Φ}}).
    Proof.
      iIntros (Hp) "#IH". iIntros (e_t e_s) "H".
      rewrite /sim sim_nostutter_eq /sim_nostutter_def.
      set (Ψ_curry := (λ '(e_t, e_s), Ψ e_s e_t)).
      assert (NonExpansive Ψ_curry) as Hne.
      { intros ? [e1 e2] [e1' e2'] [H1 H2]. rewrite /Ψ_curry. cbn in H1, H2.
        apply equiv_dist, Hp. now apply discrete_iff in H1. now apply discrete_iff in H2.
      }

      iApply (greatest_fixpoint_coind (step_nostutter Φ) Ψ_curry with "[]").
      { iModIntro. iIntros ([e_s' e_t']) "H'". by iApply "IH". }
      iApply "H".
    Qed.

    Instance sim_nostutter_proper :
      Proper (eq ==> eq ==> (pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> (≡)) sim.
    Proof.
      intros e e' -> e1 e1' -> p1 p2 Heq2.
      rewrite /sim !sim_nostutter_eq. apply greatest_fixpoint_proper; solve_proper.
    Qed.

    Lemma sim_nostutter_value Φ v_t v_s:
      ⊢ Φ v_t v_s -∗ (of_val v_t) ⪯ (of_val v_s) {{Φ}}.
    Proof.
      iIntros "Hv". rewrite sim_nostutter_unfold. iIntros (????) "[Hstate Hreach]".
      iModIntro. iLeft. iExists (v_t), (v_s), (σ_s). iFrame.
      iSplitL. by rewrite to_of_val. eauto.
    Qed.

    Lemma sim_nostutter_call P_t P_s v_t v_s K_t K_s f Φ:
      P_t !! f = Some K_t →
      P_s !! f = Some K_s →
      ⊢ progs_are P_t P_s ∗ val_rel v_t v_s ∗ sim_ectx K_t K_s Φ -∗ (of_call f v_t) ⪯ (of_call f v_s) {{Φ}}.
    Proof.
      intros Htgt Hsrc. iIntros "(#Prog & Val & Sim)".
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

    Lemma bupd_sim_nostutter Φ e_t e_s:
      ⊢ (|==> e_t ⪯ e_s {{Φ}}) -∗ e_t ⪯ e_s {{Φ}}.
    Proof.
      iIntros "Hv". rewrite sim_nostutter_unfold. iIntros (????) "H". iMod "Hv". iApply ("Hv" with "H").
    Qed.

    Lemma sim_nostutter_mono Φ Φ':
      ⊢ (∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s)
         -∗ ∀ e_s e_t : exprO, e_t ⪯ e_s {{Φ}} -∗ e_t ⪯ e_s {{Φ'}}.
    Proof.
      iIntros "Hmon".
      iIntros (e_s e_t) "H".
      iApply (sim_nostutter_coind Φ' (λ e_t e_s, e_t ⪯ e_s {{Φ}} ∗ (∀ v_t v_s : val Λ, Φ v_t v_s -∗ Φ' v_t v_s))%I); last by iFrame.
      iModIntro. clear e_t e_s. iIntros (e_t e_s) "[H Hpost]".
      rewrite /sim sim_nostutter_eq sim_nostutter_def_unfold.
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
      rewrite {1}/sim {1}sim_nostutter_eq {1}sim_nostutter_def_unfold.
      rewrite {1}/step_nostutter.
      iMod ("Hpost" with "[Hstate]") as "Hpost".
      { iFrame. iPureIntro. intros Hstuck. eapply Hnreach, prim_step_rtc_reach_stuck.
        by apply fill_prim_step_rtc. assumption. }
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
        iExists e_s', σ_s''. iFrame. iSplitL "".
        { iPureIntro. eapply tc_rtc_l; by eauto using fill_prim_step_rtc. }
        cbn. iExists e_t', e_s', empty_ectx, empty_ectx. rewrite !fill_empty.
        do 2 (iSplitL ""; first auto).
        iApply sim_nostutter_mono. 2: { rewrite /sim sim_nostutter_eq. iApply "Hrec". }
        iIntros (??) "H". rewrite !fill_empty.
        by iApply sim_nostutter_value.
      + iDestruct "Hcall" as (f K_t' v_t' K_s' v_s' σ_s'') "(%&%&Hvrel&Hstate&Hcall)".
        (* CA on the reduction of fill K_s v_s to fill K_s' (f v_s') to see if we need to take a step or do the call *)
        iRight; iRight.
        iExists f, K_t', v_t', K_s', v_s', σ_s''. iFrame.
        iSplitL "". { iPureIntro. by rewrite -H1 (of_to_val _ _ H). }
        iSplitL "". { iPureIntro. etrans; by eauto using fill_prim_step_rtc. }
        iIntros (v_t'' v_s'') "Hvrel". cbn.
        iExists (fill K_t' (of_val v_t'')), (fill K_s' (of_val v_s'')), empty_ectx, empty_ectx.
        rewrite !fill_empty. do 2 (iSplitL ""; first auto).
        iApply sim_nostutter_mono; first last.
        { rewrite /sim sim_nostutter_eq. by iApply "Hcall". }
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
      rewrite {1}/sim {1}sim_nostutter_eq {1}sim_nostutter_def_unfold.
      rewrite /step_nostutter.

      iIntros (????) "[Hs %]". rename H into Hnreach.
      iMod ("H" with "[Hs]") as "H".
      { iFrame. iPureIntro. contradict Hnreach. by apply fill_reach_stuck. }
      iDestruct "H" as "[Hval | [Hstep | Hcall]]".
      - iDestruct "Hval" as (v_t v_s σ_s') "(%& %&Hstate&Hpost)".
        by iApply (sim_bind_val_nostutter with "[Hpost] [Hstate]").
      - (* simply thread through everything *)
        iModIntro. iRight; iLeft. iDestruct "Hstep" as "[% Hstep]".
        iSplitL "". { iPureIntro. by apply fill_reducible. }
        iIntros (e_t' σ_t') "%".
        destruct (fill_reducible_prim_step _ _ _ _ _ _ H H0) as (e_t'' & -> & H1).
        iMod ("Hstep" with "[]") as "Hstep". { iPureIntro. apply H1. }
        iModIntro.
        iDestruct "Hstep" as (e_s' σ_s') "(% & Hstate & Hrec)".
        iExists (fill K_s e_s'), σ_s'. iFrame. iSplitL "".
        { iPureIntro. by apply fill_prim_step_tc. }
        cbn. iExists e_t'', e_s', K_t, K_s.
        do 2 (iSplitL ""; first auto).
        rewrite /sim sim_nostutter_eq. iApply "Hrec".
      - (* simply thread through everything *)
        iModIntro. iRight; iRight.
        iDestruct "Hcall" as (f K_t' v_t K_s' v_s σ_s') "(-> & % & Hval & Hstate & Hrec)".
        iExists f, (comp_ectx K_t K_t'), v_t, (comp_ectx K_s K_s'), v_s, σ_s'.
        iSplitL "". by rewrite fill_comp.
        iSplitL "". { iPureIntro. rewrite -fill_comp. by apply fill_prim_step_rtc. }
        iFrame.
        iIntros (v_t' v_s') "Hv". iSpecialize ("Hrec" with "Hv"). cbn.
        iExists (fill K_t' (of_val v_t')), (fill K_s' (of_val v_s')), K_t, K_s.
        iSplitL "". by rewrite -fill_comp. iSplitL "". by rewrite -fill_comp.
        rewrite /sim sim_nostutter_eq. iApply "Hrec".
    Qed.



  End no_stuttering.
End fix_lang.

