(** * SLSLS, Separation Logic Stuttering Local Simulation *)

From iris.bi Require Import bi.
From iris.proofmode Require Import tactics.
From simuliris.logic Require Import fixpoints.
From simuliris.simulation Require Import relations language.
From simuliris.simulation Require Export simulation slsls.
From iris.prelude Require Import options.
Import bi.

Section fix_lang.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language}.
  Context {s : SimulLang PROP Λ}.

  Set Default Proof Using "Type*".

  Implicit Types
    (e_s e_t e: expr Λ)
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ).

  Notation expr_rel := (@exprO Λ -d> @exprO Λ -d> PROP).

  Global Instance expr_rel_func_ne (F: expr_rel → expr_rel) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv; [|apply _..].
    eapply Hne, HΦ.
  Qed.


  (** Global simulation relation with stuttering *)

  Section sim_def.
  Context (val_rel : val Λ → val Λ → PROP).
  Definition gsim_expr_inner (greatest_rec : expr_rel -d> expr_rel) (least_rec : expr_rel -d> expr_rel) : expr_rel -d> expr_rel :=
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
          state_interp P_t σ_t' P_s σ_s'' ∗ greatest_rec Φ e_t' e_s'' ∗ [∗ list] e_t; e_s ∈ efs_t; efs_s, greatest_rec (lift_post val_rel) e_t e_s))
    )%I.

  Lemma gsim_expr_inner_mono l1 l2 g1 g2:
    ⊢ □ (∀ Φ e_t e_s, l1 Φ e_t e_s -∗ l2 Φ e_t e_s)
    → □ (∀ Φ e_t e_s, g1 Φ e_t e_s -∗ g2 Φ e_t e_s)
    → ∀ Φ e_t e_s, gsim_expr_inner g1 l1 Φ e_t e_s -∗ gsim_expr_inner g2 l2 Φ e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ e_t e_s) "Hsim".
    rewrite /gsim_expr_inner. iIntros (P_t σ_t P_s σ_s) "Ha".
    iMod ("Hsim" with "Ha") as "[Hval | Hstep]"; iModIntro.
    + iLeft. iApply "Hval".
    + iRight. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
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
  Qed.

  (* the strongest monotonicity lemma we can prove, allows for changing the post condition and recursive occurrences *)
  Lemma gsim_expr_inner_strong_mono l1 l2 g1 g2:
    ⊢ □ (∀ Φ Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, l1 Φ e_t e_s -∗ l2 Ψ e_t e_s)
    → □ (∀ Φ Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, g1 Φ e_t e_s -∗ g2 Ψ e_t e_s)
    → ∀ Φ Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, gsim_expr_inner g1 l1 Φ e_t e_s -∗ gsim_expr_inner g2 l2 Ψ e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ Ψ) "HΦΨ". iIntros (e_t e_s) "Hsim".
    rewrite /sim_expr_inner. iIntros (P_t σ_t P_s σ_s) "Ha".
    iMod ("Hsim" with "Ha") as "[Hval | Hstep]"; iModIntro.
    + iLeft. iDestruct "Hval" as (e_s' σ_s') "(Hnf & SI & HΦ)".
      iExists e_s', σ_s'. iFrame. by iApply "HΦΨ".
    + iRight. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
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
  Qed.

  Instance gsim_expr_inner_ne:
    ∀n, Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n) gsim_expr_inner.
  Proof.
    intros n G1 G2 HG L1 L2 HL Φ Ψ HΦΨ e_t e_t' Ht%discrete_iff%leibniz_equiv e_s e_s' Hs%discrete_iff%leibniz_equiv; [|apply _..].
    subst; rewrite /gsim_expr_inner.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG).
  Qed.

  Instance gsim_expr_inner_proper:
    Proper ((equiv ==> equiv) ==> (equiv ==> equiv) ==> equiv ==> equiv ==> equiv ==> equiv) gsim_expr_inner.
  Proof.
    intros G1 G2 HG L1 L2 HL Φ Ψ HΦΨ e_t e_t' Ht%leibniz_equiv e_s e_s' Hs%leibniz_equiv.
    subst; rewrite /gsim_expr_inner.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG).
  Qed.

  Local Instance global_least_def_body_mono greatest_rec :
    NonExpansive (greatest_rec) →
    BiMonoPred (λ (least_rec: prodO (prodO (exprO -d> exprO -d> PROP) exprO) exprO -d> PROP), curry3 (gsim_expr_inner greatest_rec (uncurry3 least_rec))).
  Proof.
    intros Hg; constructor.
    - intros L1 L2 HL1 HL2. iIntros "#H" (x).
      destruct x as ((Φ & e_t) & e_s); simpl.
      iApply (gsim_expr_inner_mono with "[] []"); iModIntro; clear.
      { iIntros (G e_t e_s); unfold uncurry3; iApply "H". }
      iIntros (G e_t e_s) "$".
    - intros l Hne n x y Heq.
      destruct x as ((Φ & e_t) & e_s); simpl.
      destruct y as ((Ψ & e_t') & e_s'); simpl.
      destruct Heq as [[Heq1 Heq2] Heq3]; simpl in Heq1, Heq2, Heq3.
      eapply gsim_expr_inner_ne; eauto.
      + eapply Hg.
      + intros ?????; rewrite /uncurry3. eapply Hne.
        repeat split; simpl; done.
  Qed.

  Definition global_least_def (greatest_rec : expr_rel -d> expr_rel) : expr_rel -d> expr_rel :=
    uncurry3 (bi_least_fixpoint (λ (least_rec: prodO (prodO (exprO -d> exprO -d> PROP) exprO) exprO → PROP), curry3 (gsim_expr_inner greatest_rec (uncurry3 least_rec)))).


  Global Instance global_least_def_ne :
    NonExpansive2 global_least_def.
  Proof.
    rewrite /global_least_def; intros n x y Heq ?????.
    rewrite {1 3}/uncurry3. apply least_fixpoint_ne; last by repeat split.
    intros ? [[] ?]; simpl.
    rewrite /gsim_expr_inner. repeat f_equiv; apply Heq.
  Qed.

  Lemma global_least_def_mono R R' Φ e_t e_s:
    NonExpansive (R': expr_rel -d> expr_rel) →
    <pers> (∀ Φ e_t e_s, R Φ e_t e_s -∗ R' Φ e_t e_s) -∗
    global_least_def R Φ e_t e_s -∗ global_least_def R' Φ e_t e_s.
  Proof.
    iIntros (Hne) "#Hmon". rewrite /global_least_def {1 3}/uncurry3.
    iIntros "Hleast". iApply (least_fixpoint_ind with "[] Hleast"); clear Φ e_t e_s.
    iModIntro. iIntros ([[Φ e_t] e_s]).
    erewrite least_fixpoint_unfold; last first.
    { eapply global_least_def_body_mono, _. }
    rewrite {1 3}/curry3.
    iApply (gsim_expr_inner_mono with "[] []").
    { iModIntro. iIntros (Φ' e_t' e_s') "$". }
      iModIntro; iIntros (Φ' e_t' e_s'); by iApply "Hmon".
  Qed.

  Lemma global_least_def_unfold G Φ e_t e_s:
    NonExpansive G →
    global_least_def G Φ e_t e_s ≡ gsim_expr_inner G (global_least_def G) Φ e_t e_s.
  Proof.
    intros ?; rewrite {1}/global_least_def {1}/uncurry3 least_fixpoint_unfold {1}/curry3 //=.
  Qed.

  Instance global_greatest_def_body_mono :
    BiMonoPred (λ (greatest_rec: prodO (prodO (exprO -d> exprO -d> PROP) exprO) exprO → PROP), curry3 (global_least_def (uncurry3 greatest_rec))).
  Proof.
    constructor.
    - intros G1 G2 HG1 HG2. iIntros "#H" (x).
      destruct x as [[Φ e_t] e_s]; rewrite /curry3.
      iApply global_least_def_mono. iModIntro.
      iIntros (Φ' e_t' e_s'); iApply "H".
    - intros G Hne n x y Heq. rewrite /global_least_def -!curry3_uncurry3.
      eapply least_fixpoint_ne'; last done.
      intros L HL m [[Φ e_t] e_s] [[Ψ e_t'] e_s'] Heq'; simpl.
      eapply gsim_expr_inner_ne; [| |eapply Heq'..].
      + eapply uncurry3_ne, Hne.
      + eapply uncurry3_ne, HL.
  Qed.

  Definition global_greatest_def : expr_rel -d> expr_rel :=
    uncurry3 (bi_greatest_fixpoint (λ (greatest_rec: prodO (prodO (exprO -d> exprO -d> PROP) exprO) exprO → PROP), curry3 (global_least_def (uncurry3 greatest_rec)))).

  Lemma global_greatest_def_unfold Φ e_t e_s:
    global_greatest_def Φ e_t e_s ≡ global_least_def global_greatest_def Φ e_t e_s.
  Proof.
    rewrite {1}/global_greatest_def {1}/uncurry3 greatest_fixpoint_unfold {1}/curry3 //=.
  Qed.

  Global Instance global_greatest_def_ne: NonExpansive global_greatest_def.
  Proof. eapply @uncurry3_ne. solve_proper. Qed.

  Global Instance global_greatest_def_proper: Proper (equiv ==> equiv ==> equiv ==> equiv) global_greatest_def.
  Proof.
    intros Φ Ψ Heq e_t e_t' <-%leibniz_equiv e_s e_s' <-%leibniz_equiv.
    revert e_t e_s. change (global_greatest_def Φ ≡ global_greatest_def Ψ).
    eapply ne_proper; first apply _. done.
  Qed.

  Lemma global_greatest_def_fixpoint Φ e_t e_s:
    global_greatest_def Φ e_t e_s ≡ gsim_expr_inner global_greatest_def global_greatest_def Φ e_t e_s.
  Proof.
    rewrite global_greatest_def_unfold global_least_def_unfold.
    eapply gsim_expr_inner_proper; eauto.
    - solve_proper.
    - intros Φ' Ψ' Heq. intros ??. rewrite -global_greatest_def_unfold.
      f_equiv. done.
  Qed.

  End sim_def.

  Implicit Types (Ω : val Λ → val Λ → PROP).

  Definition gsim_expr_aux : seal (λ Ω, global_greatest_def Ω).
  Proof. by eexists. Qed.
  Definition gsim_expr := (gsim_expr_aux).(unseal).
  Lemma gsim_expr_eq : gsim_expr = λ Ω Φ e_t e_s, @global_greatest_def Ω Φ e_t e_s.
  Proof. rewrite -gsim_expr_aux.(seal_eq) //. Qed.

  Lemma gsim_expr_fixpoint Ω Φ e_t e_s:
    gsim_expr Ω Φ e_t e_s ⊣⊢ gsim_expr_inner Ω (gsim_expr Ω) (gsim_expr Ω) Φ e_t e_s.
  Proof.
    rewrite gsim_expr_eq global_greatest_def_fixpoint //.
  Qed.

  Lemma gsim_expr_unfold Ω Φ e_t e_s:
    gsim_expr Ω Φ e_t e_s ⊣⊢
    (∀ P_t σ_t P_s σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜safe P_s e_s σ_s⌝ -∗ |==>
      (* base case *)
      (∃ e_s' σ_s', ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗
        state_interp P_t σ_t P_s σ_s' ∗ Φ e_t e_s')

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ -∗ |==>
        (* stuttering *)
        (⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s ∗ gsim_expr Ω Φ e_t' e_s) ∨
        (* take a step *)
        (∃ e_s' e_s'' σ_s' σ_s'' efs_s,
          ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗
          ⌜prim_step P_s e_s' σ_s' e_s'' σ_s'' efs_s⌝ ∗
          (* TODO: This length constraint is unnecessary as it is implied by the big_sepL2. *)
          ⌜length efs_t = length efs_s⌝ ∗
          state_interp P_t σ_t' P_s σ_s'' ∗ gsim_expr Ω Φ e_t' e_s'' ∗ [∗ list] e_t; e_s ∈ efs_t; efs_s, gsim_expr Ω (lift_post Ω) e_t e_s))
    )%I.
  Proof.
    rewrite gsim_expr_fixpoint /gsim_expr_inner //.
  Qed.

  Global Instance gsim_expr_ne Ω:
    NonExpansive (gsim_expr Ω: expr_rel → expr_rel).
  Proof. rewrite gsim_expr_eq. apply _. Qed.

  Global Instance gsim_expr_proper Ω:
    Proper ((pointwise_relation (expr Λ) (pointwise_relation (expr Λ) (≡))) ==> eq ==> eq ==> (≡)) (gsim_expr Ω).
  Proof.
    intros p1 p2 Heq2 e e' -> e1 e1' ->.
    rewrite !gsim_expr_eq. eapply global_greatest_def_proper; done.
  Qed.


  Existing Instances global_least_def_body_mono global_greatest_def_body_mono.
  (* any post-fixed point is included in the gfp *)
  Lemma gsim_expr_strong_coind Ω (F : expr_rel → expr_rel) :
    NonExpansive F →
    ⊢ (□ ∀ Φ e_t e_s, F Φ e_t e_s -∗ global_least_def Ω (λ Φ e_t e_s, F Φ e_t e_s ∨ gsim_expr Ω Φ e_t e_s) Φ e_t e_s)
      -∗ ∀ Φ e_t e_s, F Φ e_t e_s -∗ gsim_expr Ω Φ e_t e_s.
  Proof.
    iIntros (Hprop) "#HPre". iIntros (Φ e_t e_s) "HF".
    rewrite gsim_expr_eq /global_greatest_def {3}/uncurry3.
    set (F_curry := curry3 F).
    assert (NonExpansive F_curry) as Hne by eapply @curry3_ne, _.
    change (F Φ e_t e_s) with (F_curry (Φ, e_t, e_s)).
    remember (Φ, e_t, e_s) as p. rewrite -Heqp; clear Φ e_t e_s Heqp.
    iApply (greatest_fixpoint_strong_coind _ F_curry with "[] HF").
    iModIntro. iIntros ([[Φ e_t] e_s]); simpl.
    rewrite /F_curry.
    iApply ("HPre" $! Φ e_t e_s).
  Qed.

  Lemma gsim_expr_coind Ω (F : expr_rel → expr_rel) :
    NonExpansive F →
    ⊢ (□ ∀ Φ e_t e_s, F Φ e_t e_s -∗ global_least_def Ω F Φ e_t e_s)
      -∗ ∀ Φ e_t e_s, F Φ e_t e_s -∗ gsim_expr Ω Φ e_t e_s.
  Proof.
    iIntros (Hprop) "#HPre". iIntros (Φ e_t e_s) "HF".
    iApply (gsim_expr_strong_coind with "[] HF"); clear Φ e_t e_s.
    iModIntro; iIntros (Φ e_t e_s) "HF".
    iDestruct ("HPre" with "HF") as "HF".
    iApply (global_least_def_mono with "[] HF"); first by solve_proper.
    iModIntro. clear Φ e_t e_s. iIntros (Φ e_t e_s) "HF". by iLeft.
  Qed.

  Lemma global_least_def_strong_ind Ω (F R: expr_rel → expr_rel):
    NonExpansive R →
    NonExpansive F →
    ⊢ (□ ∀ Φ e_t e_s, gsim_expr_inner Ω R (λ Ψ e_t e_s, F Ψ e_t e_s ∧ global_least_def Ω R Ψ e_t e_s) Φ e_t e_s -∗ F Φ e_t e_s)
      -∗ ∀ Φ e_t e_s, global_least_def Ω R Φ e_t e_s -∗ F Φ e_t e_s.
  Proof.
    iIntros (Hne1 Hne2) "#HPre". iIntros (Φ e_t e_s) "HF".
    rewrite {2}/global_least_def {1}/uncurry3.
    set (F_curry := curry3 F).
    assert (NonExpansive F_curry) by eapply @curry3_ne, _.
    change (F Φ e_t e_s) with (F_curry (Φ, e_t, e_s)).
    remember (Φ, e_t, e_s) as p. rewrite -Heqp; clear Φ e_t e_s Heqp.
    iApply (least_fixpoint_strong_ind _ F_curry with "[] HF").
    iModIntro. iIntros ([[Φ e_t] e_s]); simpl.
    rewrite /F_curry {1}/uncurry3 {1}/curry3.
    iIntros "H". iApply "HPre". iExact "H".
  Qed.

  Lemma global_least_def_ind Ω (F R: expr_rel → expr_rel):
    NonExpansive R →
    NonExpansive F →
    ⊢ (□ ∀ Φ e_t e_s, gsim_expr_inner Ω R F Φ e_t e_s -∗ F Φ e_t e_s)
      -∗ ∀ Φ e_t e_s, global_least_def Ω R Φ e_t e_s -∗ F Φ e_t e_s.
  Proof.
    iIntros (Hne1 Hne2) "#HPre". iApply global_least_def_strong_ind.
    iModIntro. iIntros (Φ e_t e_s) "Hsim".
    iApply "HPre". iApply (gsim_expr_inner_mono with "[] [] Hsim"); last by auto.
    iModIntro. iIntros (Φ' e_t' e_s') "H". iApply bi.and_elim_l. iApply "H".
  Qed.

  (* we change the predicate beause at every recursive ocurrence,
     we give back ownership of the monotonicity assumption *)
  Lemma global_least_def_strong_mono Ω rec Φ Φ' e_t e_s:
    NonExpansive rec →
     (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗
     global_least_def Ω rec Φ e_t e_s -∗
     global_least_def Ω (λ Ψ e_t e_s, rec Φ e_t e_s ∗ (∀ e_t e_s, Φ e_t e_s ==∗ Ψ e_t e_s) ∨ rec Ψ e_t e_s) Φ' e_t e_s.
  Proof.
    iIntros (Hne) "Hmon Hleast". iRevert (Φ') "Hmon".
    pose (rec' := (λ Φ Ψ e_t e_s, rec Φ e_t e_s ∗ (∀ e_t e_s, Φ e_t e_s ==∗ Ψ e_t e_s) ∨ rec Ψ e_t e_s)%I).
    pose (F_ind := (λ Φ e_t e_s, ∀ Φ', (∀ e_t e_s : expr Λ, Φ e_t e_s ==∗ Φ' e_t e_s) -∗ global_least_def Ω (rec' Φ) Φ' e_t e_s)%I).
    assert (NonExpansive2 (rec': expr_rel -d> expr_rel -d> expr_rel)) as Rne.
    { intros m Φ' Φ'' Heq1 Ψ Ψ' Heq2 ??; rewrite /rec'.
      solve_proper_core ltac:(fun x => f_equiv || apply Heq1 || apply Heq2). }
    assert (NonExpansive (F_ind: expr_rel -d> expr_rel)).
    { clear Φ e_t e_s. intros n Φ Ψ Heq e_t e_s.
      rewrite /F_ind; do 3 f_equiv; first (repeat f_equiv; by apply Heq).
      eapply global_least_def_ne; last done. intros ?. eapply (Rne n Φ Ψ Heq). done. }
    iApply (global_least_def_ind Ω F_ind rec with "[] Hleast"); clear Φ e_t e_s.
    iModIntro. iIntros (Φ e_t e_s) "Hrec". iIntros (Φ') "Hmon".
    rewrite global_least_def_unfold /gsim_expr_inner.

    iIntros (P_t σ_t P_s σ_s) "Ha".
    iMod ("Hrec" with "Ha") as "[Hval | Hstep]".
    + iLeft. iDestruct "Hval" as (e_s' σ_s') "(Hnf & SI & HΦ)".
      iExists e_s', σ_s'. iFrame. by iApply "Hmon".
    + iModIntro; iRight. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". rewrite /F_ind. iApply ("H1" with "Hmon"). }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & %Hlen & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame. iSplit; first done.
      iSplitL "H5 Hmon"; first by rewrite /rec'; iLeft; iFrame.
      iApply (big_sepL2_persistent_wand with "H6 []").
      iModIntro. iIntros (? ?) "?"; by iRight.
  Qed.

  Lemma gsim_expr_bupd_mono Ω Φ Φ' e_t e_s:
    (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗ gsim_expr Ω Φ e_t e_s -∗ gsim_expr Ω Φ' e_t e_s.
  Proof.
    iIntros "Ha Hmon".
    iApply (gsim_expr_strong_coind Ω (λ Ψ e_t e_s, gsim_expr Ω Φ e_t e_s ∗ (∀ e_t e_s : expr Λ, Φ e_t e_s ==∗ Ψ e_t e_s))%I); last by iFrame.
    { intros n Ψ Ψ' Heq e_t' e_s'. repeat f_equiv. by eapply Heq. }
    iModIntro. clear Φ' e_t e_s. iIntros (Φ' e_t e_s) "[Ha Hmon]".
    rewrite gsim_expr_eq global_greatest_def_unfold.
    iApply (global_least_def_strong_mono with "Hmon Ha").
  Qed.

  Lemma gsim_expr_mono Ω Φ Φ' e_t e_s:
    (∀ e_t e_s, Φ e_t e_s -∗ Φ' e_t e_s) -∗ gsim_expr Ω Φ e_t e_s -∗ gsim_expr Ω Φ' e_t e_s.
  Proof.
    iIntros "Hmon Ha". iApply (gsim_expr_bupd_mono with "[Hmon] Ha").
    iIntros (??) "?". iModIntro. by iApply "Hmon".
  Qed.


  Lemma gsim_expr_inner_base Ω G L Φ e_t e_s :
    ⊢ (Φ e_t e_s) -∗ gsim_expr_inner Ω G L Φ e_t e_s.
  Proof.
    iIntros "He". rewrite /gsim_expr. iIntros (????) "[Hstate Hreach]".
    iModIntro. iLeft. iExists e_s, σ_s. iFrame. iPureIntro. constructor.
  Qed.

  Lemma gsim_expr_base Ω Φ e_t e_s :
    ⊢ (Φ e_t e_s) -∗ gsim_expr Ω Φ e_t e_s.
  Proof.
    iIntros "He". iApply gsim_expr_fixpoint. by iApply gsim_expr_inner_base.
  Qed.

  Lemma gsim_expr_bupd Ω Φ e_t e_s:
    (gsim_expr Ω (λ e_t' e_s', |==> Φ e_t' e_s') e_t e_s) -∗ gsim_expr Ω Φ e_t e_s.
  Proof.
    iIntros "H". iApply (gsim_expr_bupd_mono with "[] H").
    iIntros (??) "$".
  Qed.


  (* Bind Lemma *)
  Local Definition bind_coind_pred Ω :=
    (λ Φ e_t e_s, (∃ e_t' e_s' (K_t K_s : ectx Λ),
     ⌜e_t = fill K_t e_t'⌝ ∗ ⌜e_s = fill K_s e_s'⌝ ∗
     gsim_expr Ω (λ e_t'' e_s'', gsim_expr Ω Φ (fill K_t e_t'') (fill K_s e_s'')) e_t' e_s'))%I.

  Local Definition bind_coind_rec Ω :=
    (λ Φ e_t e_s, (∃ e_t' e_s' (K_t K_s : ectx Λ),
      ⌜e_t = fill K_t e_t'⌝ ∗ ⌜e_s = fill K_s e_s'⌝ ∗
      gsim_expr Ω (λ e_t'' e_s'', gsim_expr Ω Φ (fill K_t e_t'') (fill K_s e_s'')) e_t' e_s') ∨ gsim_expr Ω Φ e_t e_s)%I.

  Local Instance bind_coind_pred_ne Ω: NonExpansive (bind_coind_pred Ω: expr_rel → expr_rel).
  Proof.
    rewrite /bind_coind_pred. solve_proper_prepare; repeat f_equiv.
    intros ??; by f_equiv.
  Qed.

  Local Instance bind_coind_rec_ne Ω: NonExpansive (bind_coind_rec Ω: expr_rel → expr_rel).
  Proof.
    rewrite /bind_coind_pred. solve_proper_prepare; repeat f_equiv; last done.
    intros ??; by f_equiv.
  Qed.


  Lemma gsim_expr_bind Ω K_t K_s e_t e_s Φ :
    gsim_expr Ω (λ e_t' e_s', gsim_expr Ω Φ (fill K_t e_t') (fill K_s e_s')) e_t e_s -∗
    gsim_expr Ω Φ (fill K_t e_t) (fill K_s e_s).
  Proof.
    iIntros "H".
    iApply (gsim_expr_strong_coind Ω (bind_coind_pred Ω)%I); last first.
    { iExists e_t, e_s, K_t, K_s; iFrame; iSplit; by iPureIntro. }
    iModIntro. clear Φ e_t e_s K_t K_s.
    iIntros (Φ e_t' e_s') "IH". change (global_least_def Ω _ Φ e_t' e_s') with (global_least_def Ω (bind_coind_rec Ω) Φ e_t' e_s').
    iDestruct "IH" as (e_t e_s K_t K_s) "[-> [-> H]]".
    rewrite {1}gsim_expr_eq global_greatest_def_unfold.
    pose (F := (λ Ψ e_t e_s, ∀ Φ, (∀ e_t e_s, Ψ e_t e_s -∗ gsim_expr Ω Φ (fill K_t e_t) (fill K_s e_s)) -∗ global_least_def Ω (bind_coind_rec Ω) Φ (fill K_t e_t) (fill K_s e_s))%I).
    assert (NonExpansive (F: expr_rel → expr_rel)).
    { rewrite /F. intros n x y Heq ??. repeat f_equiv. apply Heq. }
    iAssert (∀ Ψ e_t e_s, global_least_def Ω (global_greatest_def Ω) Ψ e_t e_s -∗ F Ψ e_t e_s)%I as "Hgen"; last first.
    { iApply ("Hgen" with "H"). iIntros (??) "$". }
    clear Φ e_t e_s. iIntros (Ψ e_t e_s) "HL".
    iApply (global_least_def_ind with "[] HL"); clear Ψ e_t e_s.
    iModIntro. iIntros (Ψ e_t e_s) "Hinner".
    iIntros (Φ) "Hcont".
    rewrite global_least_def_unfold. rewrite /gsim_expr_inner.
    iIntros (P_t σ_t P_s σ_s) "[Hs %Hnreach]". iMod ("Hinner" with "[Hs]") as "H".
    { iFrame. iPureIntro. intros Hreach. apply Hnreach. by apply fill_reach_stuck. }
    iDestruct "H" as "[Hval | Hstep]".
    - iDestruct "Hval" as (e_s' σ_s') "(%Hstutter & Hstate & Hpost)".
      (* we prove that we can stutter the source and still end up at the right place *)
      iSpecialize ("Hcont" with "Hpost"). rewrite gsim_expr_unfold.
      iMod ("Hcont" with "[$Hstate]") as "[Val|Step]".
      + iPureIntro. by eapply safe_no_forks, fill_no_forks.
      + iModIntro. iLeft. iDestruct "Val" as (e_s'' σ_s'' Hnf') "[SI HΦ]".
        iExists e_s'', σ_s''. iFrame. iPureIntro. eapply no_forks_trans, Hnf'.
        by eapply fill_no_forks.
      + iModIntro. iRight.
        iDestruct "Step" as "($ & Step)".
        iIntros (e_t' efs_t σ_t' Hprim_t).
        iMod ("Step" with "[//]") as "[(-> & SI & Sim)|Step]".
        * destruct (no_forks_inv_r _ _ _ _ _ Hstutter) as [(-> & ->)|(e_s'' & σ_s'' & Hsteps & Hstep)].
          -- iModIntro. iLeft. iFrame. iSplit; first done.
             rewrite gsim_expr_eq global_greatest_def_unfold.
             iApply (global_least_def_mono with "[] Sim").
             clear; iModIntro. iIntros (Φ e_t e_s) "Hrec". iRight.
             by rewrite gsim_expr_eq.
          -- iModIntro. iRight.
             iExists (fill K_s e_s''), (fill K_s e_s'), σ_s'', σ_s', [].
             iSplit; first by iPureIntro; eapply fill_no_forks.
             iSplit; first by iPureIntro; eapply fill_prim_step, Hstep.
             iSplit; first done. by iFrame.
        * iDestruct "Step" as (e_s'' e_s''' σ_s'' σ_s''' efs_s Hforks) "(Hprim & Hlen & SI & Hsim & Hforks)".
          iModIntro. iRight. iExists e_s'', e_s''', σ_s'', σ_s''', efs_s. iFrame.
          iSplit; first by iPureIntro; eauto using no_forks_trans, fill_no_forks.
          iApply (big_sepL2_persistent_wand with "Hforks"). iModIntro.
          clear. iIntros (e_t e_s) "H". by iRight.
    - iModIntro. iRight. iDestruct "Hstep" as "[%Hred Hstep]".
      iSplitR. { iPureIntro. by apply fill_reducible. }
      iIntros (e_t' efs σ_t') "%Hstep".
      destruct (fill_reducible_prim_step _ _ _ _ _ _ _ Hred Hstep) as (e_t'' & -> & Hstep').
      iMod ("Hstep" with "[]") as "Hstep". { iPureIntro. apply Hstep'. }
      iModIntro. iDestruct "Hstep" as "[(Hnf & Hstate & Hstutter) | Hstep]".
      + iLeft. iFrame. by iApply "Hstutter".
      + iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs') "(%Hnf & %Hstep'' & %Hlen & Hstate & Hrec & Hfrk)".
        iExists (fill K_s e_s'), (fill K_s e_s''), σ_s', σ_s'', efs'. iFrame.
        iSplitR. { iPureIntro. by apply fill_no_forks. }
        iSplitR. { iPureIntro. by apply fill_prim_step. }
        iSplitR. { done. }
        iSplitL "Hcont Hrec".
        { iLeft. iExists e_t'', e_s'', K_t, K_s.
          do 2 (iSplitR; first done).
          iApply (gsim_expr_mono with "Hcont"); by rewrite gsim_expr_eq. }
        { iApply (big_sepL2_persistent_wand with "Hfrk").
          iModIntro. iIntros (??) "?". iRight. by rewrite gsim_expr_eq. }
  Qed.

  Lemma gsim_expr_decompose Ω e_t e_s Φ Ψ:
    gsim_expr Ω Ψ e_t e_s -∗
    (∀ e_t e_s, Ψ e_t e_s -∗ gsim_expr Ω Φ e_t e_s) -∗
    gsim_expr Ω Φ e_t e_s.
  Proof.
    iIntros "H1 H2".
    rewrite -{2}(fill_empty e_t) -{2}(fill_empty e_s).
    iApply (gsim_expr_bind _ empty_ectx empty_ectx).
    iApply (gsim_expr_mono with "[H2] H1").
    clear. iIntros (e_t e_s). by rewrite !fill_empty.
  Qed.


  Definition gjoin_expr Ω (F: expr_rel -d> expr_rel) : expr_rel -d> expr_rel :=
    λ Φ, gsim_expr Ω (λ e_t e_s, F Φ e_t e_s ∨ Φ e_t e_s)%I.

  Global Instance gjoin_expr_ne Ω F:
    NonExpansive F →
    NonExpansive (gjoin_expr Ω F).
  Proof.
    intros ???? Heq. rewrite /gjoin_expr. f_equiv.
    intros ??. repeat f_equiv; by apply Heq.
  Qed.
  Lemma gsim_expr_paco Ω F Φ e_t e_s:
    NonExpansive (F: expr_rel → expr_rel) →
    □ (∀ Φ e_t e_s, F Φ e_t e_s -∗ lock_step (gjoin_expr Ω F Φ) e_t e_s) -∗
    F Φ e_t e_s -∗ gsim_expr Ω Φ e_t e_s.
  Proof.
    iIntros (Hne) "#Hlock_step HF".
    iApply (gsim_expr_strong_coind _ (gjoin_expr Ω F)%I); last first.
    { rewrite /gjoin_expr. iApply gsim_expr_base. by iLeft. }
    iModIntro. clear Φ e_t e_s. iIntros (Φ e_t e_s) "Hs".
    rewrite {2}/gjoin_expr gsim_expr_eq global_greatest_def_unfold.
    pose (rec := (λ Φ e_t e_s, gjoin_expr Ω F Φ e_t e_s ∨ global_greatest_def Ω Φ e_t e_s)%I).
    assert (NonExpansive (rec: expr_rel → expr_rel)).
    { intros ??? Heq ??. solve_proper. }
    pose (Rec := (λ Ψ e_t e_s, ∀ Φ, (∀ e_t e_s, Ψ e_t e_s -∗ F Φ e_t e_s ∨ Φ e_t e_s) -∗ global_least_def Ω rec Φ e_t e_s)%I).
    assert (NonExpansive (Rec: expr_rel → expr_rel)).
    { intros ??? Heq ??. rewrite /Rec. repeat f_equiv. by eapply Heq. }
    iApply (global_least_def_ind _ Rec with "[] Hs []"); last auto.
    iModIntro. clear Φ e_t e_s. iIntros (Ψ e_t e_s) "Hinner".
    iIntros (Φ) "Hmon". rewrite global_least_def_unfold.
    rewrite /gsim_expr_inner.
    iIntros (P_t σ_t P_s σ_s) "[Hs %Hsafe]". iMod ("Hinner" with "[$Hs //]") as "H".
    iDestruct "H" as "[Hval | Hstep]".
    - iDestruct "Hval" as (e_s' σ_s') "(%Hstutter & Hstate & Hpost)".
      (* we prove that we can stutter the source and still end up at the right place *)
      iDestruct ("Hmon" with "Hpost") as "[HF|Hpost]"; last first.
      { iModIntro. iLeft. iExists _, _. iFrame. by iPureIntro. }
      iMod ("Hlock_step" with "HF [$Hstate ]") as "[Hred Hstep]".
      { iPureIntro. by eapply safe_no_forks. }
      iModIntro. iRight. iFrame.
      iIntros (e_t' efs_t σ_t' Hprim_t). iMod ("Hstep" with "[//]") as (e_s'' σ_s'' -> Hnfs) "[SI Hjoin]".
      iModIntro. iRight. iExists e_s', e_s'', σ_s', σ_s'', []; simpl; iFrame.
      by iPureIntro.
    - iModIntro. iRight. iDestruct "Hstep" as "[%Hred Hstep]".
      iSplitR; first done.
      iIntros (e_t' efs σ_t') "%Hstep". iMod ("Hstep" with "[//]") as "[(Hnf & Hstate & Hstutter) | Hstep]".
      + iModIntro. iLeft. iFrame. rewrite /Rec. by iApply "Hstutter".
      + iModIntro. iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs') "(%Hnf & %Hstep'' & %Hlen & Hstate & Hrec' & Hfrk)".
        iExists e_s', e_s'', σ_s', σ_s'', efs'. iFrame.
        repeat (iSplit; first done).
        iSplitL "Hmon Hrec'".
        { iLeft. iApply (gsim_expr_mono with "Hmon [Hrec']"); by rewrite gsim_expr_eq. }
        iApply (big_sepL2_persistent_wand with "Hfrk").
        iModIntro. iIntros (??) "?". by iRight.
  Qed.

  Lemma bupd_gsim_expr Ω Φ e_t e_s:
    ⊢ (|==> gsim_expr Ω Φ e_t e_s) -∗ gsim_expr Ω Φ e_t e_s.
  Proof.
    iIntros "Hv". rewrite gsim_expr_unfold. iIntros (????) "H". iMod "Hv". iApply ("Hv" with "H").
  Qed.


  Lemma gsim_step_source Ω e_t e_s Φ :
    (∀ P_s σ_s P_t σ_t, state_interp P_t σ_t P_s σ_s ∗ ⌜safe P_s e_s σ_s ⌝ ==∗
      ∃ e_s' σ_s', ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗ state_interp P_t σ_t P_s σ_s' ∗ gsim_expr Ω Φ e_t e_s') -∗
      gsim_expr Ω Φ e_t e_s.
  Proof.
    rewrite gsim_expr_unfold. iIntros "Hsource" (P_t σ_t P_s σ_s) "[Hstate %Hsafe]".
    iMod ("Hsource" with "[$Hstate //]") as (e_s' σ_s') "(%Hexec & Hstate & Hsim)".
    rewrite {1}gsim_expr_unfold.
    iMod ("Hsim" with "[Hstate]") as "Hsim".
    { iFrame. iPureIntro. by eapply safe_no_forks. }
    iModIntro. iDestruct "Hsim" as "[Hval | Hstep]".
    - iLeft. iDestruct "Hval" as (e_s'' σ_s'') "(% & Hstate & Hphi)".
      iExists e_s'', σ_s''. iFrame. iPureIntro. by eapply no_forks_trans.
    - iDestruct "Hstep" as "(%&Hstep)". iRight.
      iSplitR; first by iPureIntro.
      iIntros (e_t' efs_t σ_t') "Hprim". iMod ("Hstep" with "Hprim") as "[Hstutter | Hred]"; iModIntro.
      + (* which path we want to take depends on the rtc we have *)
        eapply no_forks_inv_r in Hexec as [(-> & ->)|(e_s'' & σ_s'' & Hnfs & Hnf)].
        { (* no step, just mirror the stuttering *) iLeft. iFrame. }
        (* we have actually taken a source step *)
        iRight. iExists e_s'', e_s', σ_s'', σ_s', [].
        iDestruct "Hstutter" as "(-> & SI & Hsim)"; simpl; iFrame.
        by iPureIntro.
      + iRight. iDestruct "Hred" as (e_s'' e_s''' σ_s'' σ_s''' efs_s) "(%Hnfs & Hstep & Hlen & Hstate & Hsim & Hfrks)".
        iExists e_s'', e_s''', σ_s'', σ_s''', efs_s. iFrame. iPureIntro.
        by eapply no_forks_trans.
  Qed.

  (* the step case of the simulation relation, but the two cases are combined into an rtc in the source *)
  Lemma gsim_step_target Ω e_t e_s Φ:
    (∀ P_t P_s σ_t σ_s, state_interp P_t σ_t P_s σ_s ∗ ⌜safe P_s e_s σ_s⌝ ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
      ∃ e_s' σ_s', ⌜efs_t = []⌝ ∗ ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗ state_interp P_t σ_t' P_s σ_s' ∗ gsim_expr Ω Φ e_t' e_s') -∗
    gsim_expr Ω Φ e_t e_s.
  Proof.
    iIntros "Hsim". rewrite gsim_expr_unfold. iIntros (????) "[Hstate %]".
    iMod ("Hsim" with "[$Hstate ]") as "[Hred Hsim]"; first done. iModIntro. iRight.
    iFrame. iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hsim" with "Hstep") as (e_s' σ_s') "(-> & %Hs & ? & ?)".
    apply no_forks_inv_r in Hs as [ [-> ->] | (e_s'' & σ_s'' & Hstep & Hsteps)].
    - iLeft. by iFrame.
    - iRight; iExists e_s'', e_s', σ_s'', σ_s', []. iModIntro; simpl; iFrame.
      by iPureIntro.
  Qed.


  (* we show that the local simulation for all functions in the program implies the global simulation *)
  Definition local_rel Ω P_t P_s : PROP :=
    (□ ∀ f K_s, ⌜P_s !! f = Some K_s⌝ → ∃ K_t, ⌜P_t !! f = Some K_t⌝ ∗ sim_ectx Ω K_t K_s Ω)%I.
  Typeclasses Opaque local_rel.

  Global Instance local_rel_persistent Ω P_s P_t : Persistent (local_rel Ω P_s P_t).
  Proof. rewrite /local_rel; apply _. Qed.

  Lemma local_to_global Ω P_t P_s Φ e_t e_s:
    local_rel Ω P_t P_s -∗
    progs_are P_t P_s -∗
    sim_expr Ω Φ e_t e_s -∗
    gsim_expr Ω Φ e_t e_s.
  Proof.
    rewrite /local_rel; iIntros "#Hloc #Hprog Hsim".
    iApply (gsim_expr_coind Ω (sim_expr Ω) with "[] Hsim"); clear Φ e_t e_s.
    iModIntro. iIntros (Φ e_t e_s).
    rewrite {1}sim_expr_eq greatest_def_unfold.
    iIntros "H". iApply (least_def_ind _ (global_least_def Ω (sim_expr Ω)) with "[] H"); clear Φ e_t e_s.
    iModIntro. iIntros (Φ e_t e_s) "Hsim".
    rewrite global_least_def_unfold.
    iIntros (P_t' σ_t P_s' σ_s) "[Hstate %Hsafe]".
    rewrite /progs_are; iDestruct ("Hprog" with "Hstate") as "[% %]"; subst P_t' P_s'.
    iMod ("Hsim" with "[$Hstate //]") as "[Hsim|[Hsim|Hsim]]"; iModIntro; [ eauto | rewrite sim_expr_eq; eauto | ].
    iDestruct "Hsim" as (f K_t v_t K_s v_s σ_s') "(% & %Hnfs & Hval & Hstate & Hcont)".
    subst e_t. iRight.
    (* the function is in the source table *)
    edestruct (@safe_call_in_prg Λ) as [K_f_s Hdef_s]; [by eauto..|].

    (* we prove reducibility and the step case *)
    iSplit.
    - iAssert (∃ K_f_t, ⌜P_t !! f = Some K_f_t⌝)%I as (K_f_t) "%".
      { iDestruct ("Hloc" $! _ _ Hdef_s) as (K_f_t) "[% _]"; by eauto. }
      iPureIntro. eexists _, _, _.
      by apply fill_prim_step, head_prim_step, call_head_step_intro.
    - iIntros (e_t' efs_t σ_t' Hstep).
      apply prim_step_call_inv in Hstep as (K_f_t & Hdef & -> & -> & ->).
      iModIntro. iRight. iExists (fill K_s (of_call f v_s)), (fill K_s (fill K_f_s (of_val v_s))), σ_s', σ_s', [].
      iFrame. iSplit; first done. iSplit.
      { iPureIntro. by apply fill_prim_step, head_prim_step, call_head_step_intro. }
      iSplit; first done. simpl; iSplit; last done.
      iApply sim_expr_bind. iDestruct ("Hloc" $! _ _ Hdef_s) as (K_f_t') "[% Hectx]".
      replace K_f_t' with K_f_t by naive_solver. rewrite /sim_ectx.
      iApply (sim_expr_mono with "[-Hval] [Hval]"); last by iApply "Hectx".
      iIntros (e_t' e_s'). iDestruct 1 as (v_t' v_s' -> ->) "Hval".
      rewrite sim_expr_eq. by iApply "Hcont".
  Qed.


  Lemma local_to_global_call Ω P_t P_s f v_t v_s:
    is_Some (P_s !! f) →
    local_rel Ω P_t P_s -∗
    progs_are P_t P_s -∗
    Ω v_t v_s -∗
    gsim_expr Ω (lift_post Ω) (of_call f v_t) (of_call f v_s).
  Proof.
    iIntros ([K_s Hlook]) "#Hloc #Hprogs Hval".
    iApply (local_to_global with "Hloc Hprogs").
    rewrite /local_rel.
    iDestruct "Hloc" as "#Hloc".
    iDestruct ("Hloc" $! _ _ Hlook) as (K_t) "[% Hsim]".
    iApply sim_call_inline; last (iFrame; iSplit; first done); eauto.
  Qed.
End fix_lang.
