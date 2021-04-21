(** * SLSLS, Separation Logic Stuttering Local Simulation *)

From iris.bi Require Import bi.
From iris.proofmode Require Import tactics.
From simuliris.logic Require Import fixpoints.
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
  Notation expr_rel := (@exprO Λ -d> @exprO Λ -d> PROP).
  Definition lift_post (Φ: val Λ → val Λ → PROP) :=
    (λ e_t e_s, ∃ v_t v_s, ⌜e_t = of_val v_t⌝ ∗ ⌜e_s = of_val v_s⌝ ∗ Φ v_t v_s)%I.

  Section sim_def.
  Context (val_rel : val Λ → val Λ → PROP).
  Definition sim_expr_inner (greatest_rec : expr_rel -d> expr_rel) (least_rec : expr_rel -d> expr_rel) : expr_rel -d> expr_rel :=
    λ Φ e_t e_s,
    (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜safe P_s e_s σ_s⌝ -∗ |==>
      (* base case *)
      (∃ e_s' σ_s', ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗
        state_interp P_t σ_t P_s σ_s' ∗ Φ e_t e_s')

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ -∗ |==>
        (* stuttering *)
        (⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s ∗ least_rec Φ e_t' e_s) ∨
        (* take a step *)
        (∃ e_s' e_s'' σ_s' σ_s'' efs_s,
          ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗
          ⌜prim_step P_s e_s' σ_s' e_s'' σ_s'' efs_s⌝ ∗
          ⌜length efs_t = length efs_s⌝ ∗
          state_interp P_t σ_t' P_s σ_s'' ∗ greatest_rec Φ e_t' e_s' ∗ [∗ list] e_t; e_s ∈ efs_t; efs_s, greatest_rec (lift_post val_rel) e_t e_s))

      ∨ (* call case *)
      (∃ f K_t v_t K_s v_s σ_s',
        ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
        ⌜no_forks P_s e_s σ_s (fill K_s (of_call f v_s)) σ_s'⌝ ∗
        val_rel v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
        (∀ v_t v_s, val_rel v_t v_s -∗ greatest_rec Φ (fill K_t (of_val v_t)) (fill K_s (of_val v_s)) ))
    )%I.

  Lemma sim_expr_inner_mono l1 l2 g1 g2:
    ⊢ □ (∀ Φ e_t e_s, l1 Φ e_t e_s -∗ l2 Φ e_t e_s)
    → □ (∀ Φ e_t e_s, g1 Φ e_t e_s -∗ g2 Φ e_t e_s)
    → ∀ Φ e_t e_s, sim_expr_inner g1 l1 Φ e_t e_s -∗ sim_expr_inner g2 l2 Φ e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ e_t e_s) "Hsim".
    rewrite /sim_expr_inner. iIntros (P_t σ_t P_s σ_s) "Ha".
    iMod ("Hsim" with "Ha") as "[Hval | [Hstep | Hcall]]"; iModIntro.
    + iLeft. iApply "Hval".
    + iRight; iLeft. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". by iApply "Hleast". }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & %Hlen & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame. iSplit; first done.
      iSplitL "H5"; first by iApply "Hgreatest".
      iApply (big_sepL2_wand with "H6 []"); simpl.
      iRevert (efs_s Hlen); clear; iInduction efs_t as [|e_t efs_t] "IHt";
      iIntros (efs_s Hlen); destruct efs_s as [|e_s efs_s]; simpl; [naive_solver..|].
      iSplitL ""; first iApply "Hgreatest".
      assert (length efs_t = length efs_s) as Hlen' by naive_solver.
      iSpecialize ("IHt" $! efs_s Hlen'). done.
    + iRight; iRight. iDestruct "Hcall" as (f K_t v_t K_s v_s σ_s') "(H1& H2& H3& H4&H5)".
      iExists (f), (K_t), (v_t), (K_s), (v_s), (σ_s'). iFrame.
      iIntros (? ?) "H1". iApply "Hgreatest". by iApply "H5".
  Qed.

  (* the strongest monotonicity lemma we can prove, allows for changing the post condition and recursive occurrences *)
  Lemma sim_expr_inner_strong_mono l1 l2 g1 g2:
    ⊢ □ (∀ Φ Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, l1 Φ e_t e_s -∗ l2 Ψ e_t e_s)
    → □ (∀ Φ Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, g1 Φ e_t e_s -∗ g2 Ψ e_t e_s)
    → ∀ Φ Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, sim_expr_inner g1 l1 Φ e_t e_s -∗ sim_expr_inner g2 l2 Ψ e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ Ψ) "HΦΨ". iIntros (e_t e_s) "Hsim".
    rewrite /sim_expr_inner. iIntros (P_t σ_t P_s σ_s) "Ha".
    iMod ("Hsim" with "Ha") as "[Hval | [Hstep | Hcall]]"; iModIntro.
    + iLeft. iDestruct "Hval" as (e_s' σ_s') "(Hnf & SI & HΦ)".
      iExists e_s', σ_s'. iFrame. by iApply "HΦΨ".
    + iRight; iLeft. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". by iApply ("Hleast" with "HΦΨ H1"). }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & %Hlen & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame. iSplit; first done.
      iSplitL "H5 HΦΨ"; first by iApply ("Hgreatest" with "HΦΨ H5").
      iApply (big_sepL2_wand with "H6 []"); simpl.
      iRevert (efs_s Hlen); clear; iInduction efs_t as [|e_t efs_t] "IHt";
      iIntros (efs_s Hlen); destruct efs_s as [|e_s efs_s]; simpl; [naive_solver..|].
      iSplitL "".
      { iApply ("Hgreatest" $! (lift_post val_rel) (lift_post val_rel) with "[]").
        iIntros (e_t' e_s') "$". }
      assert (length efs_t = length efs_s) as Hlen' by naive_solver.
      iSpecialize ("IHt" $! efs_s Hlen'). done.
    + iRight; iRight. iDestruct "Hcall" as (f K_t v_t K_s v_s σ_s') "(H1& H2& H3& H4&H5)".
      iExists (f), (K_t), (v_t), (K_s), (v_s), (σ_s'). iFrame.
      iIntros (? ?) "H1". iApply ("Hgreatest" with "HΦΨ [H5 H1]").
      by iApply "H5".
  Qed.

  Instance sim_expr_inner_ne:
    ∀n, Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n) sim_expr_inner.
  Proof.
    intros n G1 G2 HG L1 L2 HL Φ Ψ HΦΨ e_t e_t' Ht%discrete_iff%leibniz_equiv e_s e_s' Hs%discrete_iff%leibniz_equiv; [|apply _..].
    subst; rewrite /sim_expr_inner.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG).
  Qed.

  Instance sim_expr_inner_proper:
    Proper ((equiv ==> equiv) ==> (equiv ==> equiv) ==> equiv ==> equiv ==> equiv ==> equiv) sim_expr_inner.
  Proof.
    intros G1 G2 HG L1 L2 HL Φ Ψ HΦΨ e_t e_t' Ht%leibniz_equiv e_s e_s' Hs%leibniz_equiv.
    subst; rewrite /sim_expr_inner.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG).
  Qed.

  Instance least_def_mono greatest_rec :
    NonExpansive (greatest_rec) →
    BiMonoPred (λ (least_rec: prodO (prodO (exprO -d> exprO -d> PROP) exprO) exprO -d> PROP), curry3 (sim_expr_inner greatest_rec (uncurry3 least_rec))).
  Proof.
    intros Hg; constructor.
    - intros L1 L2 HL1 HL2. iIntros "#H" (x).
      destruct x as ((Φ & e_t) & e_s); simpl.
      iApply (sim_expr_inner_mono with "[] []"); iModIntro; clear.
      { iIntros (G e_t e_s); unfold uncurry3; iApply "H". }
      iIntros (G e_t e_s) "$".
    - intros l Hne n x y Heq.
      destruct x as ((Φ & e_t) & e_s); simpl.
      destruct y as ((Ψ & e_t') & e_s'); simpl.
      destruct Heq as [[Heq1 Heq2] Heq3]; simpl in Heq1, Heq2, Heq3.
      eapply sim_expr_inner_ne; eauto.
      + eapply Hg.
      + intros ?????; rewrite /uncurry3. eapply Hne.
        repeat split; simpl; done.
  Qed.

  Definition least_def (greatest_rec : expr_rel -d> expr_rel) : expr_rel -d> expr_rel :=
    uncurry3 (bi_least_fixpoint (λ (least_rec: prodO (prodO (exprO -d> exprO -d> PROP) exprO) exprO → PROP), curry3 (sim_expr_inner greatest_rec (uncurry3 least_rec)))).

  Lemma curry3_uncurry3 {X Y Z A: ofe} (f: X * Y * Z -> A) (x: prodO (prodO X Y) Z):
    f x ≡ curry3 (uncurry3 f) x.
  Proof.
    destruct x as [[x y] z]; reflexivity.
  Qed.


  Instance uncurry3_ne {A B C D: ofe} (G: prodO (prodO A B) C -d> D):
    NonExpansive G → NonExpansive (uncurry3 G: A -d> B -d> C -d> D).
  Proof.
    intros Hne ??????; simpl.
    rewrite /uncurry3. eapply Hne. repeat f_equiv. done.
  Qed.

  Instance greatest_def_mono :
    BiMonoPred (λ (greatest_rec: prodO (prodO (exprO -d> exprO -d> PROP) exprO) exprO → PROP), curry3 (least_def (uncurry3 greatest_rec))).
  Proof.
    constructor.
    - intros G1 G2 HG1 HG2. iStartProof. iIntros "#H" (x).
      rewrite /least_def. rewrite -!(curry3_uncurry3).
      iRevert (x). iApply least_fixpoint_ind. iModIntro.
      iIntros (x) "Hinner". erewrite least_fixpoint_unfold; last first.
      { eapply least_def_mono, _. }
      destruct x as ((Φ & e_t) & e_s); simpl.
      iApply (sim_expr_inner_mono with "[] [] Hinner").
      { iModIntro. iIntros (Φ' e_t' e_s') "$". }
      iModIntro; iIntros (Φ' e_t' e_s'); by iApply "H".
    - intros G Hne n x y Heq. rewrite /least_def -!curry3_uncurry3.
      eapply least_fixpoint_ne'; last done.
      intros L HL m [[Φ e_t] e_s] [[Ψ e_t'] e_s'] Heq'; simpl.
      eapply sim_expr_inner_ne; [| |eapply Heq'..].
      + eapply uncurry3_ne, Hne.
      + eapply uncurry3_ne, HL.
  Qed.

  Definition greatest_def : expr_rel -d> expr_rel :=
    uncurry3 (bi_greatest_fixpoint (λ (greatest_rec: prodO (prodO (exprO -d> exprO -d> PROP) exprO) exprO → PROP), curry3 (least_def (uncurry3 greatest_rec)))).


  Lemma greatest_def_unfold Φ e_t e_s:
    greatest_def Φ e_t e_s ≡ least_def greatest_def Φ e_t e_s.
  Proof.
    rewrite {1}/greatest_def {1}/uncurry3 greatest_fixpoint_unfold {1}/curry3 //=.
  Qed.

  Lemma least_def_unfold G Φ e_t e_s:
    NonExpansive G →
    least_def G Φ e_t e_s ≡ sim_expr_inner G (least_def G) Φ e_t e_s.
  Proof.
    intros ?; rewrite {1}/least_def {1}/uncurry3 least_fixpoint_unfold {1}/curry3 //=.
  Qed.

  Instance greatest_def_ne: NonExpansive greatest_def.
  Proof. eapply @uncurry3_ne. solve_proper. Qed.

  Instance greatest_def_proper: Proper (equiv ==> equiv ==> equiv ==> equiv) greatest_def.
  Proof.
    intros Φ Ψ Heq e_t e_t' <-%leibniz_equiv e_s e_s' <-%leibniz_equiv.
    revert e_t e_s. change (greatest_def Φ ≡ greatest_def Ψ).
    eapply ne_proper; first apply _. done.
  Qed.

  Lemma greatest_def_fixpoint Φ e_t e_s:
    greatest_def Φ e_t e_s ≡ sim_expr_inner greatest_def greatest_def Φ e_t e_s.
  Proof.
    rewrite greatest_def_unfold least_def_unfold.
    eapply sim_expr_inner_proper; eauto.
    - eapply ne_proper, _.
    - intros Φ' Ψ' Heq. intros ??. rewrite -greatest_def_unfold.
      f_equiv. done.
  Qed.

  End sim_def.

  Implicit Types (Ω : val Λ → val Λ → PROP).

  Definition sim_expr_aux : seal (λ Ω, greatest_def Ω).
  Proof. by eexists. Qed.
  Global Instance sim_expr_stutter : SimE s := (sim_expr_aux).(unseal).
  Lemma sim_expr_eq : sim_expr = λ Ω Φ e_t e_s, @greatest_def Ω Φ e_t e_s.
  Proof. rewrite -sim_expr_aux.(seal_eq) //. Qed.

  Lemma lift_post_val Φ v_t v_s : Φ v_t v_s -∗ lift_post Φ (of_val v_t) (of_val v_s).
  Proof. iIntros "?"; iExists v_t, v_s; eauto using to_of_val. Qed.
  Definition sim_def Ω (Φ : val Λ → val Λ → PROP) e_t e_s  :=
    sim_expr Ω (lift_post Φ) e_t e_s.
  Global Instance sim_stutter : Sim s := sim_def.

  Lemma sim_expr_fixpoint Ω Φ e_t e_s:
    sim_expr Ω Φ e_t e_s ⊣⊢ sim_expr_inner Ω (sim_expr Ω) (sim_expr Ω) Φ e_t e_s.
  Proof.
    rewrite sim_expr_eq greatest_def_fixpoint //.
  Qed.

  Lemma sim_expr_unfold Ω Φ e_t e_s:
    sim_expr Ω Φ e_t e_s ⊣⊢
    (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜safe P_s e_s σ_s⌝ -∗ |==>
      (* base case *)
      (∃ e_s' σ_s', ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗
        state_interp P_t σ_t P_s σ_s' ∗ Φ e_t e_s')

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ -∗ |==>
        (* stuttering *)
        (⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s ∗ sim_expr Ω Φ e_t' e_s) ∨
        (* take a step *)
        (∃ e_s' e_s'' σ_s' σ_s'' efs_s,
          ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗
          ⌜prim_step P_s e_s' σ_s' e_s'' σ_s'' efs_s⌝ ∗
          ⌜length efs_t = length efs_s⌝ ∗
          state_interp P_t σ_t' P_s σ_s'' ∗ sim_expr Ω Φ e_t' e_s' ∗ [∗ list] e_t; e_s ∈ efs_t; efs_s, sim_expr Ω (lift_post Ω) e_t e_s))

      ∨ (* call case *)
      (∃ f K_t v_t K_s v_s σ_s',
        ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
        ⌜no_forks P_s e_s σ_s (fill K_s (of_call f v_s)) σ_s'⌝ ∗
        Ω v_t v_s ∗ state_interp P_t σ_t P_s σ_s' ∗
        sim_expr_ectx Ω K_t K_s Φ)
    )%I.
  Proof.
    rewrite /sim_expr_ectx sim_expr_fixpoint /sim_expr_inner //.
  Qed.
(*
  (* any post-fixed point is included in the gfp *)
  Lemma sim_expr_coind Ω Φ (Ψ : exprO → exprO → PROP) :
    Proper ((≡) ==> (≡) ==> (≡)) Ψ →
    ⊢ (□ ∀ e_t e_s, Ψ e_t e_s -∗ greatest_step Ω Φ (λ '(e_s, e_t), Ψ e_t e_s) (e_s, e_t))
      -∗ ∀ e_t e_s, Ψ e_t e_s -∗ sim_expr Ω e_t e_s Φ.
  Proof.
    iIntros (Hp) "#H". iIntros (e_t e_s) "H0".
    rewrite sim_expr_eq /sim_expr_def.

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

  Global Instance sim_expr_proper :
    Proper ((pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> eq ==> eq ==>
      (pointwise_relation (expr Λ) (pointwise_relation (expr Λ) (≡))) ==> (≡)) sim_expr.
  Proof.
    intros o1 o2 H e e' -> e1 e1' -> p1 p2 Heq2.
    rewrite !sim_expr_eq. apply greatest_fixpoint_proper; last done.
    intros p3 [e3 e3']. rewrite /greatest_step /least_def.
    apply least_fixpoint_proper; last done. solve_proper.
  Qed.
  Global Instance sim_proper :
    Proper ((pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> eq ==> eq ==>
      (pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> (≡)) sim.
  Proof.
    intros o1 o2 H e e' -> e1 e1' -> p1 p2 Heq2.
    rewrite /sim /sim_stutter /sim_def /lift_post. solve_proper.
  Qed.

  Lemma sim_expr_base Ω Φ e_t e_s :
    ⊢ (Φ e_t e_s) -∗ e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "He". rewrite sim_expr_unfold. iIntros (????) "[Hstate Hreach]".
    iModIntro. iLeft. iExists e_s, σ_s. iFrame. eauto.
  Qed.

  Lemma sim_value Ω Φ v_t v_s:
    ⊢ Φ v_t v_s -∗ of_val v_t ⪯{Ω} of_val v_s {{ Φ }}.
  Proof.
    iIntros "Hv". iApply sim_expr_base.
    iExists v_t, v_s. iFrame; by rewrite !to_of_val.
  Qed.

  Lemma bupd_sim Ω Φ e_t e_s:
    ⊢ (|==> e_t ⪯{Ω} e_s [{ Φ }]) -∗ e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "Hv". rewrite sim_expr_unfold. iIntros (????) "H". iMod "Hv". iApply ("Hv" with "H").
  Qed.

  (* we change the predicate beause at every recursive ocurrence,
     we give back ownership of the monotonicity assumption *)
  Lemma least_def_mono rec Ω Φ Φ' :
    (∀ e_t e_s, Φ e_t e_s -∗ Φ' e_t e_s) -∗
    ∀ e_s e_t,
    least_def Ω Φ rec e_s e_t -∗
    least_def Ω Φ' (λ e_s e_t, rec e_s e_t ∗ ∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) e_s e_t.
  Proof.
    iIntros "Hmon" (e_s e_t). iIntros "Hleast". iRevert "Hmon".
    iApply (sim_ind _ _ _ _ (λ e_t, (∀ e_t e_s : expr Λ, Φ e_t e_s -∗ Φ' e_t e_s) -∗ least_def Ω Φ' (λ e_s e_t, rec e_s e_t ∗ ∀ e_t e_s, Φ e_t e_s -∗ Φ' e_t e_s) e_s e_t)%I with "[] Hleast"); clear e_t.
    iModIntro. iIntros (e_t) "IH Hmon". rewrite least_def_unfold /least_step.
    iIntros (P_t σ_t P_s σ_s) "H". iMod ("IH" with "H") as "IH". iModIntro.
    iDestruct "IH" as "[Hval | [Hstep | Hcall]]".
    - iLeft. iDestruct "Hval" as (e_s' σ_s') "(?&?&?)".
      iExists e_s', σ_s'. iFrame. by iApply "Hmon".
    - iRight; iLeft. iDestruct "Hstep" as "[$ Hstep]".
      iIntros (e_t' σ_t' Hstep).
      iMod ("Hstep" with "[//]") as "[Hstep|Hstep]".
      + iModIntro. iLeft. iDestruct "Hstep" as "[$ H]". by iApply "H".
      + iModIntro. iRight. iFrame "Hmon". eauto.
    - iRight; iRight. by iFrame "Hmon".
  Qed.

  Lemma sim_expr_mono Ω Φ Φ' :
    (∀ e_t e_s, Φ e_t e_s -∗ Φ' e_t e_s) -∗
    ∀ e_s e_t : exprO, e_t ⪯{Ω} e_s [{ Φ }] -∗ e_t ⪯{Ω} e_s [{ Φ' }].
  Proof.
    iIntros "Hmon" (e_s e_t) "Ha".
    iApply (sim_expr_coind Ω Φ' (λ e_t e_s, e_t ⪯{Ω} e_s [{ Φ }] ∗ (∀ e_t e_s : expr Λ, Φ e_t e_s -∗ Φ' e_t e_s))%I); last by iFrame.
    iModIntro. clear e_t e_s. iIntros (e_t e_s) "[Ha Hmon]".
    rewrite sim_expr_eq sim_expr_def_unfold.
    rewrite /greatest_step !least_def_unfold /least_step.
    iIntros (????) "Hs". iSpecialize ("Ha" with "Hs"). iMod "Ha". iModIntro.
    iDestruct "Ha" as "[Hval | [Hred | Hcall]]".
    - iLeft. iDestruct "Hval" as (e_s' σ_s') "(?&?&?)".
      iExists e_s', σ_s'. iFrame. by iApply "Hmon".
    - iRight; iLeft. iDestruct "Hred" as "[Hred Hstep]". iFrame.
      iIntros (e_t' σ_t') "Hprim".
      iMod ("Hstep" with "Hprim") as "[Hstutter | Hstep]"; iModIntro.
      + iLeft. iDestruct "Hstutter" as "[Hstate Hleast]". iFrame.
        by iApply (least_def_mono with "Hmon").
      + iRight. by iFrame.
    - iRight; iRight. iFrame.
  Qed.

  Lemma lift_post_mon Φ Φ' :
    (∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) -∗ (∀ e_t e_s, lift_post Φ e_t e_s -∗ lift_post Φ' e_t e_s).
  Proof.
    iIntros "Hmon" (e_t e_s). rewrite /lift_post. iIntros "He".
    iDestruct "He" as (v_t v_s) "(-> & -> & Hp)". iExists v_t, v_s. do 2 (iSplitR; first done).
    by iApply "Hmon".
  Qed.
  Lemma sim_mono Ω Φ Φ' :
    (∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) -∗
    ∀ e_s e_t : exprO, e_t ⪯{Ω} e_s {{ Φ }} -∗ e_t ⪯{Ω} e_s {{ Φ' }}.
  Proof.
    iIntros "Hmon" (e_s e_t) "Ha". iApply (sim_expr_mono with "[Hmon] Ha").
    by iApply lift_post_mon.
  Qed.

  Lemma sim_expr_bupd Ω Φ e_t e_s:
    (e_t ⪯{Ω} e_s [{ λ e_t' e_s', |==> Φ e_t' e_s' }]) -∗ e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "Hv".
    iApply (sim_expr_coind Ω Φ (λ e_t e_s, e_t ⪯{Ω} e_s [{λ e_t' e_s', |==> Φ e_t' e_s'}])%I); last by iFrame.
    iModIntro. clear e_t e_s. iIntros (e_t e_s) "Hv".
    rewrite sim_expr_unfold /greatest_step least_def_unfold /least_step.
    iIntros (????) "H". iMod ("Hv" with "H") as "Hv".
    iDestruct "Hv" as "[Hv | [H | H]]".
    - iDestruct "Hv" as (e_s' σ_s') "(H1 & H2 & >H3)".
      iModIntro. iLeft. iExists e_s', σ_s'. iFrame.
    - iModIntro. iRight; iLeft. iDestruct "H" as "[Hred H]"; iFrame.
      iIntros (??) "Hs". iMod ("H" with "Hs") as "[[? Hs] | Hs]"; iModIntro.
      + iLeft. iFrame.
        iApply sim_ind. 2: { rewrite sim_expr_eq sim_expr_def_least_def_unfold. iFrame. }
        iModIntro. clear e_t' P_t P_s σ_t' σ_t σ_s. iIntros (e_t') "IH".
        rewrite least_def_unfold !/least_step.
        iIntros (????) "H". iMod ("IH" with "H") as "Hv".
        iDestruct "Hv" as "[Hv | [H | H]]".
        * iDestruct "Hv" as (e_s' σ_s') "(H1 & H2 & >H3)".
          iModIntro. iLeft. iExists e_s', σ_s'. iFrame.
        * iModIntro. iRight; iLeft. iDestruct "H" as "[Hred H]"; iFrame.
          iIntros (??) "Hs". iMod ("H" with "Hs") as "[[? Hs] | Hs]"; iModIntro.
          { iLeft. iFrame. }
          iRight. rewrite sim_expr_eq. iFrame.
        * iModIntro. iRight; iRight. rewrite sim_expr_eq. iFrame.
      + iRight. iFrame.
    - iModIntro. iRight; iRight. iFrame.
  Qed.
  Lemma sim_bupd Ω Φ e_t e_s:
    (e_t ⪯{Ω} e_s {{ λ v_t v_s, |==> Φ v_t v_s }}) -∗ e_t ⪯{Ω} e_s {{ Φ }}.
  Proof.
    iIntros "Hv". iApply sim_expr_bupd.
    iApply (sim_expr_mono with "[] Hv").
    iIntros (e_t' e_s') "Ha". rewrite /lift_post.
    iDestruct "Ha" as (v_t v_s) "(-> & -> & >Ha)". iModIntro.
    iExists v_t, v_s. iFrame. iSplit; done.
  Qed.

  (* TODO: clean up the bind lemma proof *)
  (* coinduction predicate used for the bind lemma *)
  Definition bind_pred Ω Φ := uncurry (λ '(e_s, e_t), ∃ e_t' e_s' (K_t K_s : ectx Λ),
    ⌜e_t = fill K_t e_t'⌝ ∧ ⌜e_s = fill K_s e_s'⌝ ∧
     e_t' ⪯{Ω} e_s' [{ λ e_t'' e_s'', fill K_t e_t'' ⪯{Ω} fill K_s e_s'' [{ Φ }] }])%I.

  (* Lemma used two times in the proof of the bind lemma (for the value cases of the inner and outer induction) *)
  Lemma sim_expr_bind_base Ω P_s e_s σ_s σ_s' e_s' e_t K_t σ_t P_t K_s Φ :
      rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s') →
      (¬ reach_stuck P_s (fill K_s e_s) σ_s) →
      ⊢ fill K_t e_t ⪯{Ω} fill K_s e_s' [{ Φ }] -∗
      state_interp P_t σ_t P_s σ_s' -∗ |==>

        (* base case *)
        (∃ e_s'' σ_s'',
          ⌜rtc (prim_step P_s) (fill K_s e_s, σ_s) (e_s'', σ_s'')⌝ ∗
          state_interp P_t σ_t P_s σ_s'' ∗ Φ (fill K_t e_t) e_s'')

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
    iIntros (Hs Hnreach) "Hpost Hstate".
    rewrite {1}sim_expr_eq {1}sim_expr_def_unfold.
    rewrite {1}/greatest_step !least_def_unfold /least_step.
    iMod ("Hpost" with "[Hstate]") as "Hpost".
    { iFrame. iPureIntro. intros Hstuck. eapply Hnreach, prim_step_rtc_reach_stuck; last done.
       by apply fill_prim_step_rtc. }
    iModIntro.
    iDestruct "Hpost" as "[Hv | [Hstep | Hcall]]".
    + iLeft. iDestruct "Hv" as (e_s'' σ_s'') "(% & Hstate & Hpost)".
      iExists e_s'', σ_s''. iFrame.
      iPureIntro. etrans; eauto using fill_prim_step_rtc.
    + iRight; iLeft. iDestruct "Hstep" as "[% Hstep]". iSplitR "Hstep"; first done.
      iIntros (e_t' σ_t') "%". iMod ("Hstep" with "[//]") as "Hstep".
      iModIntro. iDestruct "Hstep" as "[[Hstate Hstutter] | Hstep]".
      * (* CA on the reduction of e_s to v_s to check if we need to stutter or not *)
        apply (rtc_inv_tc) in Hs as [Heq | H3].
        { injection Heq as ??; subst. iLeft. iFrame. iApply least_def_mon. 2: iApply "Hstutter".
          iModIntro. iIntros ([e_s e_t'']) "H".
          iExists e_t'', e_s, empty_ectx, empty_ectx.
          rewrite !fill_empty. do 2 (iSplitR; first auto).
          iApply sim_expr_mono. 2: { rewrite sim_expr_eq. iApply "H". }
          iIntros (v_t' v_s') "Hv". rewrite !fill_empty. by iApply sim_expr_base.
        }
        {
          iRight. iExists (fill K_s e_s'), σ_s'. iFrame.
          iSplitR "Hstutter".
          { iPureIntro. by apply fill_prim_step_tc. }
          cbn. iExists e_t', (fill K_s e_s'), empty_ectx, empty_ectx. rewrite !fill_empty.
          do 2 (iSplitR; first by auto).
          iApply sim_expr_mono; first last.
          { rewrite sim_expr_eq sim_expr_def_unfold /greatest_step. iApply "Hstutter". }
          iIntros (v_t' v_s') "Hv". rewrite !fill_empty. by iApply sim_expr_base.
        }
      * iDestruct "Hstep" as (e_s'' σ_s'') "(%&Hstate& Hrec)". iRight.
        iExists e_s'', σ_s''. iFrame. iSplitR.
        { iPureIntro. eapply tc_rtc_l; by eauto using fill_prim_step_rtc. }
        cbn. iExists e_t', e_s'', empty_ectx, empty_ectx. rewrite !fill_empty.
        do 2 (iSplitR; first auto).
        iApply sim_expr_mono. 2: { rewrite sim_expr_eq. iApply "Hrec". }
        iIntros (??) "H". rewrite !fill_empty.
        by iApply sim_expr_base.
    + iDestruct "Hcall" as (f K_t' v_t' K_s' v_s' σ_s'') "(%&%&Hvrel&Hstate&Hcall)".
      (* CA on the reduction of fill K_s v_s to fill K_s' (f v_s') to see if we need to take a step or do the call *)
      iRight; iRight.
      iExists f, K_t', v_t', K_s', v_s', σ_s''. iFrame.
      iSplitR; first done.
      iSplitR. { iPureIntro. etrans; eauto using fill_prim_step_rtc. }
      iIntros (v_t'' v_s'') "Hvrel". cbn.
      iExists (fill K_t' (of_val v_t'')), (fill K_s' (of_val v_s'')), empty_ectx, empty_ectx.
      rewrite !fill_empty. do 2 (iSplitR; first auto).
      iApply sim_expr_mono; first last.
      { rewrite sim_expr_eq. by iApply "Hcall". }
      iIntros (??) "H". rewrite !fill_empty. by iApply sim_expr_base.
  Qed.

  Lemma sim_expr_bind Ω e_t e_s K_t K_s Φ :
    e_t ⪯{Ω} e_s [{ λ e_t' e_s', fill K_t e_t' ⪯{Ω} fill K_s e_s' [{ Φ }] }] -∗
    fill K_t e_t ⪯{Ω} fill K_s e_s [{ Φ }].
  Proof.
    iIntros "H".
    iApply (sim_expr_coind Ω Φ (λ e_t' e_s', bind_pred Ω Φ e_s' e_t')%I).
    2: { iExists e_t, e_s, K_t, K_s. iFrame. eauto. }
    iModIntro. clear e_t e_s K_t K_s.
    iIntros (e_t' e_s') "IH".
    iDestruct "IH" as (e_t e_s K_t K_s) "[-> [-> H]]".
    rewrite {1}sim_expr_eq {1}sim_expr_def_unfold.
    rewrite /greatest_step !least_def_unfold /least_step.

    iIntros (????) "[Hs %Hnreach]". iMod ("H" with "[Hs]") as "H".
    { iFrame. iPureIntro. contradict Hnreach. by apply fill_reach_stuck. }
    iDestruct "H" as "[Hval | [Hstep | Hcall]]".
    - iDestruct "Hval" as (e_s' σ_s') "(%& Hstate&Hpost)".
      by iApply (sim_expr_bind_base with "Hpost Hstate").
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
        * iDestruct "Hval" as (e_s' σ_s') "(% & Hstate & Hrec)".
          by iApply (sim_expr_bind_base with "Hrec Hstate").
        * iModIntro. iDestruct "Hred" as "[% Hred]". iRight; iLeft. iSplitR.
          { iPureIntro. by apply fill_reducible. }
          iIntros (e_t' σ_t'') "%".
          destruct (fill_reducible_prim_step _ _ _ _ _ _ H0 H1) as (e_t''' & -> & H2).
          iMod ("Hred" with "[ //]") as "[Hstutter | Hstep]"; iModIntro; first by iLeft.
          iRight. iDestruct "Hstep" as (e_s' σ_s') "(%&Hstate&Hrec)".
          iExists (fill K_s e_s'), σ_s'. iFrame. iSplitR.
          { iPureIntro. by apply fill_prim_step_tc. }
          cbn. iExists e_t''', e_s', K_t, K_s. do 2 (iSplitR; first auto).
          by rewrite sim_expr_eq.
        * iModIntro. iDestruct "Hcall" as (f K_t' v_t K_s' v_s σ_s') "(-> & % & Hv & Hstate & Hcall)".
          iRight; iRight. iExists f, (comp_ectx K_t K_t'), v_t, (comp_ectx K_s K_s'), v_s, σ_s'.
          iSplitR. { by rewrite fill_comp. }
          iSplitR. { iPureIntro. rewrite -fill_comp. by apply fill_prim_step_rtc. }
          iFrame. iIntros (v_t' v_s') "Hv".
          cbn. iExists (fill K_t' (of_val v_t')), (fill K_s' (of_val v_s')), K_t, K_s.
          rewrite !fill_comp. do 2 (iSplitR; first auto).
          rewrite sim_expr_eq. by iApply "Hcall".
      + iRight. iDestruct "Hstep" as (e_s' σ_s') "(% & Hstate & Hrec)".
        iExists (fill K_s e_s'), σ_s'. iFrame. iSplitR.
        { iPureIntro. by apply fill_prim_step_tc. }
        cbn. iExists e_t'', e_s', K_t, K_s.
        do 2 (iSplitR; first auto).
        rewrite sim_expr_eq. iApply "Hrec".
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
      rewrite sim_expr_eq. iApply "Hrec".
  Qed.

  Lemma sim_bind Ω e_t e_s K_t K_s Φ :
    e_t ⪯{Ω} e_s {{ λ v_t v_s, fill K_t (of_val v_t) ⪯{Ω} fill K_s (of_val v_s) [{ Φ }] }} -∗
    fill K_t e_t ⪯{Ω} fill K_s e_s [{ Φ }].
  Proof.
    iIntros "Ha". iApply sim_expr_bind.
    iApply (sim_expr_mono with "[] Ha").
    rewrite /lift_post.
    iIntros (e_t' e_s') "Hv". iDestruct "Hv" as (v_t v_s) "(%Hv_t & %Hv_s & Hsim)".
    rewrite -(of_to_val _ _ Hv_t). rewrite -(of_to_val _ _ Hv_s).
    iApply "Hsim".
  Qed.

  (** Corollaries *)
  Lemma sim_call_inline Ω P_t P_s v_t v_s K_t K_s f Φ :
    P_t !! f = Some K_t →
    P_s !! f = Some K_s →
    ⊢ progs_are P_t P_s ∗ Ω v_t v_s ∗ sim_ectx Ω K_t K_s Φ -∗ (of_call f v_t) ⪯{Ω} (of_call f v_s) {{Φ}}.
  Proof.
    intros Htgt Hsrc. iIntros "(#Prog & Val & Sim)".
    rewrite /sim /sim_stutter /sim_def sim_expr_unfold. iIntros (P_t' σ_t P_s' σ_s) "[SI %]".
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
      + rewrite fill_empty; assert (K_t' = K_t) as -> by naive_solver.
        iSpecialize ("Sim" with "Val"). done.
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
  Proof. iIntros "H Hv". iApply (sim_mono with "Hv H"). Qed.

  Lemma sim_wand_l Ω e_t e_s Φ Ψ :
    (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) ∗ e_t ⪯{Ω} e_s {{ Φ }} ⊢ e_t ⪯{Ω} e_s {{ Ψ }}.
  Proof. iIntros "[Hv H]". iApply (sim_wand with "H Hv"). Qed.

  Lemma sim_wand_r Ω e_t e_s Φ Ψ :
    e_t ⪯{Ω} e_s {{ Φ }} ∗ (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) ⊢ e_t ⪯{Ω} e_s {{ Ψ }}.
  Proof. iIntros "[H Hv]". iApply (sim_wand with "H Hv"). Qed.

  Lemma sim_expr_wand Ω e_t e_s Φ Ψ :
    e_t ⪯{Ω} e_s [{ Φ }] -∗ (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) -∗ e_t ⪯{Ω} e_s [{ Ψ }].
  Proof. iIntros "H Hv". iApply (sim_expr_mono with "Hv H"). Qed.

  (** Update the SI. Useful when we use the SI to encode invariants. *)
  Definition update_si (P : PROP) :=
    (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ==∗ state_interp P_t σ_t P_s σ_s ∗ P)%I.
  Instance update_si_proper : Proper ((≡) ==> (≡)) update_si.
  Proof. solve_proper. Qed.
  Lemma sim_update_si Ω e_t e_s Φ :
    update_si (e_t ⪯{Ω} e_s [{ Φ }]) -∗ e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "Hupd". rewrite {2}(sim_expr_unfold Ω Φ e_t e_s).
    iIntros (????) "[Hstate Hnreach]". iMod ("Hupd" with "Hstate") as "[Hstate Hsim]".
    rewrite {1}sim_expr_unfold. iApply "Hsim". iFrame.
  Qed.

  Lemma sim_step_source Ω e_t e_s Φ :
    (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s ⌝ ==∗ ∃ e_s' σ_s',
      ⌜rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ state_interp P_t σ_t P_s σ_s' ∗
      e_t ⪯{Ω} e_s' [{ Φ }]) -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    rewrite sim_expr_unfold. iIntros "Hsource" (P_t σ_t P_s σ_s) "[Hstate %]".
    iMod ("Hsource" with "[$Hstate //]") as (e_s' σ_s') "(% & Hstate & Hsim)".
    rename H0 into Hsrc_rtc.
    rewrite {1}sim_expr_unfold.
    iMod ("Hsim" with "[Hstate]") as "Hsim".
    { iFrame. iPureIntro. by eapply not_reach_stuck_pres_rtc. }
    iModIntro. iDestruct "Hsim" as "[Hval | [Hstep | Hcall]]".
    - iLeft. iDestruct "Hval" as (e_s'' σ_s'') "(% & Hstate & Hphi)".
      iExists e_s'', σ_s''. iFrame. iPureIntro. by etrans.
    - iDestruct "Hstep" as "(%&Hstep)". iRight; iLeft.
      iSplitR; first by iPureIntro.
      iIntros (e_t' σ_t') "Hprim". iMod ("Hstep" with "Hprim") as "[Hstutter | Hred]"; iModIntro.
      + (* which path we want to take depends on the rtc we have *)
        apply rtc_inv_tc in Hsrc_rtc as [ [= -> ->] | Hsrc_tc].
        { (* no step, just mirror the stuttering *) iLeft. iFrame. }
        (* we have actually taken a source step *)
        iRight. iExists e_s', σ_s'. iFrame. by iPureIntro.
      + iRight. iDestruct "Hred" as (e_s'' σ_s'') "(% & Hstate & Hsim)".
        iExists e_s'', σ_s''. iFrame. iPureIntro.
        apply rtc_inv_tc in Hsrc_rtc as [ [= -> ->] | Hsrc_tc]; first done.
        by etrans.
    - iDestruct "Hcall" as (f K_t v_t K_s v_s σ_s'') "(-> & % & Hv & Hstate & Hsim)".
      iRight; iRight. iExists f, K_t, v_t, K_s, v_s, σ_s''. iFrame.
      iSplitR; first done. iPureIntro. by etrans.
  Qed.

  (* the step case of the simulation relation, but the two cases are combined into an rtc in the source *)
  Lemma sim_step_target Ω e_t e_s Φ:
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' σ_t',
        ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
          ∃ e_s' σ_s', ⌜rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗
            state_interp P_t σ_t' P_s σ_s' ∗ e_t' ⪯{Ω} e_s' [{ Φ }]) -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "Hsim". rewrite sim_expr_unfold. iIntros (????) "[Hstate %]".
    iMod ("Hsim" with "[$Hstate ]") as "[Hred Hsim]"; first done. iModIntro. iRight; iLeft.
    iFrame. iIntros (e_t' σ_t') "Hstep". iMod ("Hsim" with "Hstep") as (e_s' σ_s') "(%Hs & ? & ?)".
    iModIntro.
    apply rtc_inv_tc in Hs as [ [= -> ->] | Hs].
    - iLeft. iFrame.
    - iRight; iExists e_s', σ_s'. iFrame. by iPureIntro.
  Qed.

  (** ** source_red judgment *)
  (** source_red allows to focus the reasoning on the source value
    (while being able to switch back and forth to the full simulation at any point) *)
  Definition source_red_rec (Ψ : expr Λ → PROP) (rec : exprO → PROP) e_s :=
    (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗
      (∃ e_s' σ_s', ⌜prim_step P_s (e_s, σ_s) (e_s', σ_s')⌝ ∗
        state_interp P_t σ_t P_s σ_s' ∗ rec e_s')
      ∨ (state_interp P_t σ_t P_s σ_s ∗ Ψ e_s))%I.

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

  Hint Constructors rtc : core.
  Lemma source_red_elim Ψ e_s :
    source_red e_s Ψ -∗
    ∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗
      ∃ e_s' σ_s', ⌜rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ Ψ e_s' ∗ state_interp P_t σ_t P_s σ_s'.
  Proof.
    iIntros "H". rewrite source_red_eq.
    iApply (source_red_ind _ (λ e_s, ∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗
        ∃ e_s' σ_s', ⌜rtc (prim_step P_s) (e_s, σ_s) (e_s', σ_s')⌝ ∗ Ψ e_s' ∗ state_interp P_t σ_t P_s σ_s')%I);
    last by rewrite /flip.
    clear e_s. iModIntro. iIntros (e_s) "IH". iIntros (P_s σ_s P_t σ_t) "[HSI %]".
    rewrite /source_red_rec.
    iMod ("IH" with "[$HSI //]") as "IH".
    iDestruct "IH" as "[Hstep | [Hstate Hp]]"; first last.
    { iModIntro. iExists e_s, σ_s. iFrame. by iPureIntro. }
    iDestruct "Hstep" as (e_s' σ_s') "(% & Hstate & IH)".
    iMod ("IH" with "[$Hstate]") as (e_s'' σ_s'') "(% & Hp & Hs)".
    { iPureIntro. eapply not_reach_stuck_pres_rtc; by eauto. }
    iModIntro. iExists e_s'', σ_s''; iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma source_red_base Ψ e_s :
    (|==> Ψ e_s) -∗ source_red e_s Ψ.
  Proof.
    iIntros "Hpsi". rewrite source_red_eq /flip source_red_unfold /source_red_rec.
    iIntros (P_s σ_s P_t σ_t) "[Hstate %]". iRight. iMod ("Hpsi"). iModIntro. iFrame.
  Qed.

  Lemma source_red_step Ψ e_s :
    (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ∗ ⌜¬ reach_stuck P_s e_s σ_s⌝ ==∗
      (∃ e_s' σ_s', ⌜prim_step P_s (e_s, σ_s) (e_s', σ_s')⌝ ∗
        state_interp P_t σ_t P_s σ_s' ∗ source_red e_s' Ψ)) -∗
    source_red e_s Ψ.
  Proof.
    iIntros "Hstep". rewrite source_red_eq /flip source_red_unfold /source_red_rec.
    iIntros (P_s σ_s P_t σ_t) "Hstate". iLeft. iMod ("Hstep" with "Hstate"). iModIntro. iFrame.
  Qed.

  Lemma source_red_sim_expr Ω e_s e_t Φ :
    (source_red e_s (λ e_s', e_t ⪯{Ω} e_s' [{ Φ }])) -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "Hsource". iPoseProof (source_red_elim with "Hsource") as "Hsource".
    iApply sim_step_source. iIntros (????) "Hstate".
    iMod ("Hsource" with "Hstate") as (e_s' σ_s') "(?&?&?)".
    iModIntro. iExists e_s', σ_s'. iFrame.
  Qed.

  Lemma source_red_stuck e_s Ψ :
    (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗ ⌜stuck P_s e_s σ_s⌝) -∗
    source_red e_s Ψ.
  Proof.
    iIntros "Hstuck". rewrite source_red_eq /flip source_red_unfold /source_red_rec.
    iIntros (????) "[Hstate %]". iMod ("Hstuck" with "Hstate") as "%".
    exfalso; apply H. exists e_s, σ_s; done.
  Qed.

  Lemma source_red_bind e_s K_s Ψ :
    source_red e_s (λ e_s', source_red (fill K_s e_s') Ψ) -∗
    source_red (fill K_s e_s) Ψ.
  Proof.
    iIntros "He".
    iApply (source_red_ind _ (λ e_s, source_red (fill K_s e_s) Ψ)%I); last by rewrite source_red_eq /flip .
    iModIntro. clear e_s. iIntros (e_s) "IH". rewrite source_red_eq /flip source_red_unfold.
    iIntros (????) "[Hstate %]". iMod ("IH" with "[$Hstate]") as "IH".
    { iPureIntro. contradict H. by eapply fill_reach_stuck. }
    iDestruct "IH" as "[Hstep | [Hstate Hred]]".
    { iModIntro. iDestruct "Hstep" as (e_s' σ_s') "(%&?&?)". iLeft.
      iExists (fill K_s e_s'), σ_s'. iFrame. iPureIntro.
      by apply fill_prim_step. }
    rewrite source_red_unfold.
    iMod ("Hred" with "[$Hstate//]") as "[Hstep | Hred]"; iModIntro; eauto.
  Qed.

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

  Instance target_red_rec_mono Ψ : BiMonoPred (target_red_rec Ψ).
  Proof.
    constructor.
    - iIntros (l1 l2) "H". by iApply target_red_mon.
    - intros l Hne n e1 e2 Heq. apply (discrete_iff _ _) in Heq as ->. done.
  Qed.

  Definition target_red_def Ψ := bi_least_fixpoint (target_red_rec Ψ).
  Lemma target_red_def_unfold Ψ e_t : target_red_def Ψ e_t ⊣⊢ target_red_rec Ψ (target_red_def Ψ) e_t.
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

  Lemma target_red_unfold e_t Ψ :
    target_red e_t Ψ ⊣⊢
      ∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗
        (⌜ reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
          state_interp P_t σ_t' P_s σ_s ∗ target_red e_t' Ψ)
        ∨ (state_interp P_t σ_t P_s σ_s ∗ Ψ e_t).
  Proof. rewrite target_red_eq; simpl. by rewrite target_red_def_unfold. Qed.

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
    iIntros "Hpsi". rewrite target_red_unfold.
    iIntros (P_s σ_s P_t σ_t) "Hstate". iRight. iMod ("Hpsi"). iModIntro. iFrame.
  Qed.

  Lemma target_red_step Ψ e_t :
    (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ==∗
      (⌜ reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t', ⌜prim_step P_t (e_t, σ_t) (e_t', σ_t')⌝ ==∗
        state_interp P_t σ_t' P_s σ_s ∗ target_red e_t' Ψ)) -∗
    target_red e_t Ψ .
  Proof.
    iIntros "Hstep". rewrite target_red_unfold.
    iIntros (P_s σ_s P_t σ_t) "Hstate". iLeft. iMod ("Hstep" with "Hstate"). iModIntro. iFrame.
  Qed.

  Lemma target_red_sim_expr Ω e_s e_t Φ :
    (target_red e_t (λ e_t', e_t' ⪯{Ω} e_s [{ Φ }])) -∗
    e_t ⪯{Ω} e_s [{ Φ }].
  Proof.
    iIntros "Htarget". rewrite target_red_eq.
    iApply (target_red_ind _ (λ e_t, e_t ⪯{Ω} e_s [{ Φ }])%I); last by rewrite /flip.
    iModIntro. clear e_t. iIntros (e_t) "Htarget".
    rewrite sim_expr_unfold. iIntros (????) "[Hstate Hnreach]".
    iMod ("Htarget" with "Hstate") as "[[Hred Hstep] | [Hstate Hsim]]".
    - iModIntro. iRight; iLeft. iFrame. iIntros (e_t' σ_t') "Hprim".
      (* stuttering step *) iLeft.
      iMod ("Hstep" with "Hprim") as "Hstep". iModIntro; iFrame.
    - rewrite {1}sim_expr_unfold. by iMod ("Hsim" with "[$Hstate $Hnreach]").
  Qed.

  Lemma target_red_bind e_t K_t Ψ :
    target_red e_t (λ e_t', target_red (fill K_t e_t') Ψ) -∗
    target_red (fill K_t e_t) Ψ.
  Proof.
    iIntros "He".
    iApply (target_red_ind _ (λ e_t, target_red (fill K_t e_t) Ψ)%I); last by rewrite target_red_eq /flip.
    iModIntro. clear e_t. iIntros (e_t) "IH". rewrite target_red_eq /flip target_red_def_unfold.
    iIntros (????) "Hstate". iMod ("IH" with "Hstate") as "IH".
    iDestruct "IH" as "[[% Hstep] | [Hstate Hred]]"; first last.
    - rewrite target_red_def_unfold.
      iMod ("Hred" with "Hstate") as "[Hstep | Hred]"; iModIntro; eauto.
    - rename H into Hred. iModIntro. iLeft. iSplitR; first by eauto using fill_reducible.
      iIntros (e_t' σ_t') "%". rename H into Hprim.
      eapply fill_reducible_prim_step in Hprim as (e_t'' & -> & H); last done.
      by iMod ("Hstep" with "[% //]").
  Qed.

  Lemma target_red_mono Φ Ψ :
    (∀ e_t, Φ e_t -∗ Ψ e_t) -∗
    ∀ e_t, target_red e_t Φ -∗ target_red e_t Ψ.
  Proof.
    iIntros "Hw" (e_t) "Ht".
    iApply (target_red_ind _ (λ e_t, (∀ e_t', Φ e_t' -∗ Ψ e_t') -∗ target_red e_t Ψ)%I with "[] [Ht] Hw"); last by rewrite target_red_eq /flip.
    iModIntro. clear e_t. iIntros (e_t) "IH Hw".
    rewrite target_red_unfold. iIntros (????) "Hstate".
    iMod ("IH" with "Hstate") as "[[%Hred IH] | [Hstate Hphi]]"; iModIntro.
    - iLeft; iSplitR; first done. iIntros (??) "Hprim".
      iMod ("IH" with "Hprim") as "[?  IH]"; iModIntro; iFrame. by iApply "IH".
    - iRight. iFrame. by iApply "Hw".
  Qed.

  Lemma target_red_wand Φ Ψ e_t :
    target_red e_t Φ -∗ (∀ e_t', Φ e_t' -∗ Ψ e_t') -∗ target_red e_t Ψ.
  Proof. iIntros "Ht Hw". iApply (target_red_mono with "Hw Ht"). Qed. *)
End fix_lang.
