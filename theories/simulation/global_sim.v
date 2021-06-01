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
  Context {s : simulirisG PROP Λ}.

  Set Default Proof Using "Type*".

  Implicit Types
    (e_s e_t e: expr Λ)
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ).

  Notation expr_rel := (@exprO Λ -d> @exprO Λ -d> PROP).

  Global Instance expr_rel_func_ne (F: expr_rel → thread_idO -d> expr_rel) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ π π' ->%discrete_iff%leibniz_equiv e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv; [|apply _..].
    eapply Hne, HΦ.
  Qed.


  (** Global simulation relation with stuttering *)

  Section sim_def.
  Context (val_rel : thread_id → val Λ → val Λ → PROP).
  Definition gsim_expr_inner (greatest_rec : expr_rel -d> thread_id -d> expr_rel) (least_rec : expr_rel -d> thread_id -d> expr_rel) : expr_rel -d> thread_id -d> expr_rel :=
    λ Φ π e_t e_s,
    (∀ P_t σ_t P_s σ_s T_s K_s,
        state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ -∗ |==>
      (* base case *)
      (∃ e_s' σ_s', ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗
        state_interp P_t σ_t P_s σ_s' (<[π := fill K_s e_s']> T_s) ∗ Φ e_t e_s')

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ -∗ |==>
        (* stuttering *)
        (⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s T_s ∗ least_rec Φ π e_t' e_s) ∨
        (* take a step *)
        (∃ e_s' e_s'' σ_s' σ_s'' efs_s,
          ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗
          ⌜prim_step P_s e_s' σ_s' e_s'' σ_s'' efs_s⌝ ∗
          ⌜length efs_t = length efs_s⌝ ∗
          state_interp P_t σ_t' P_s σ_s'' (<[π := fill K_s e_s'']> T_s ++ efs_s) ∗ greatest_rec Φ π e_t' e_s'' ∗
          [∗ list] π'↦e_t; e_s ∈ efs_t; efs_s, greatest_rec (lift_post (val_rel (length T_s + π'))) (length T_s + π') e_t e_s))
    )%I.

  Lemma gsim_expr_inner_mono l1 l2 g1 g2:
    ⊢ □ (∀ Φ π e_t e_s, l1 Φ π e_t e_s -∗ l2 Φ π e_t e_s)
    → □ (∀ Φ π e_t e_s, g1 Φ π e_t e_s -∗ g2 Φ π e_t e_s)
    → ∀ Φ π e_t e_s, gsim_expr_inner g1 l1 Φ π e_t e_s -∗ gsim_expr_inner g2 l2 Φ π e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ π e_t e_s) "Hsim".
    rewrite /gsim_expr_inner. iIntros (P_t σ_t P_s σ_s T_s K_s) "Ha".
    iMod ("Hsim" with "Ha") as "[Hval | Hstep]"; iModIntro.
    + iLeft. iApply "Hval".
    + iRight. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". by iApply "Hleast". }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & %Hlen & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame. iSplit; first done.
      iSplitL "H5"; first by iApply "Hgreatest".
      iApply (big_sepL2_impl with "H6 []"); simpl.
      iIntros "!>" (?????). by iApply "Hgreatest".
  Qed.

  (* the strongest monotonicity lemma we can prove, allows for changing the post condition and recursive occurrences *)
  Lemma gsim_expr_inner_strong_mono l1 l2 g1 g2:
    ⊢ □ (∀ Φ π Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, l1 Φ π e_t e_s -∗ l2 Ψ π e_t e_s)
    → □ (∀ Φ π Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, g1 Φ π e_t e_s -∗ g2 Ψ π e_t e_s)
    → ∀ Φ π Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, gsim_expr_inner g1 l1 Φ π e_t e_s -∗ gsim_expr_inner g2 l2 Ψ π e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ π Ψ) "HΦΨ". iIntros (e_t e_s) "Hsim".
    rewrite /gsim_expr_inner. iIntros (P_t σ_t P_s σ_s T_s K_s) "Ha".
    iMod ("Hsim" with "Ha") as "[Hval | Hstep]"; iModIntro.
    + iLeft. iDestruct "Hval" as (e_s' σ_s') "(Hnf & SI & HΦ)".
      iExists e_s', σ_s'. iFrame. by iApply "HΦΨ".
    + iRight. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". by iApply ("Hleast" with "HΦΨ H1"). }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & %Hlen & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame. iSplit; first done.
      iSplitL "H5 HΦΨ"; first by iApply ("Hgreatest" with "HΦΨ H5").
      iApply (big_sepL2_impl with "H6 []"); simpl.
      iIntros "!>" (?????) "Hg". iApply ("Hgreatest" with "[] Hg").
      by iIntros (??) "?".
  Qed.

  Instance gsim_expr_inner_ne:
    ∀n, Proper ((dist n ==> dist n ==> dist n) ==> (dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n ==> dist n) gsim_expr_inner.
  Proof.
    intros n G1 G2 HG L1 L2 HL Φ Ψ HΦΨ π π' Hπ%discrete_iff%leibniz_equiv e_t e_t' Ht%discrete_iff%leibniz_equiv e_s e_s' Hs%discrete_iff%leibniz_equiv; [|apply _..].
    subst; rewrite /gsim_expr_inner.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
  Qed.

  Instance gsim_expr_inner_proper:
    Proper ((equiv ==> equiv ==> equiv) ==> (equiv ==> equiv ==> equiv) ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv) gsim_expr_inner.
  Proof.
    intros G1 G2 HG L1 L2 HL Φ Ψ HΦΨ π π' Hπ%leibniz_equiv e_t e_t' Ht%leibniz_equiv e_s e_s' Hs%leibniz_equiv.
    subst; rewrite /gsim_expr_inner.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
  Qed.

  Local Instance global_least_def_body_mono greatest_rec :
    NonExpansive (greatest_rec) →
    BiMonoPred (λ (least_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO -d> PROP), curry4 (gsim_expr_inner greatest_rec (uncurry4 least_rec))).
  Proof.
    intros Hg; constructor.
    - intros L1 L2 HL1 HL2. iIntros "#H" (x).
      destruct x as (((Φ & π) & e_t) & e_s); simpl.
      iApply (gsim_expr_inner_mono with "[] []"); iModIntro; clear.
      { iIntros (G π e_t e_s); unfold uncurry4; iApply "H". }
      iIntros (G π e_t e_s) "$".
    - intros l Hne n x y Heq.
      destruct x as (((Φ & π) & e_t) & e_s); simpl.
      destruct y as (((Ψ & π') & e_t') & e_s'); simpl.
      destruct Heq as [[[Heq1 Heq2] Heq3] Heq4]; simpl in Heq1, Heq2, Heq3, Heq4.
      eapply gsim_expr_inner_ne; eauto.
      + intros ?????->%leibniz_equiv. by eapply Hg.
      + intros ????????; rewrite /uncurry4. eapply Hne.
        repeat split; simpl; done.
  Qed.

  Definition global_least_def (greatest_rec : expr_rel -d> thread_id -d> expr_rel) : expr_rel -d> thread_id -d> expr_rel :=
    uncurry4 (bi_least_fixpoint (λ (least_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO → PROP), curry4 (gsim_expr_inner greatest_rec (uncurry4 least_rec)))).


  Global Instance global_least_def_ne :
    NonExpansive2 global_least_def.
  Proof.
    rewrite /global_least_def; intros n x y Heq ??????.
    rewrite {1 3}/uncurry4. apply least_fixpoint_ne; last by repeat split.
    intros ? [[[??]?] ?]; simpl.
    rewrite /gsim_expr_inner. repeat f_equiv; apply Heq.
  Qed.

  Lemma global_least_def_mono R R' π Φ e_t e_s:
    NonExpansive (R': expr_rel -d> thread_id -d> expr_rel) →
    <pers> (∀ Φ π e_t e_s, R Φ π e_t e_s -∗ R' Φ π e_t e_s) -∗
    global_least_def R Φ π e_t e_s -∗ global_least_def R' Φ π e_t e_s.
  Proof.
    iIntros (Hne) "#Hmon". rewrite /global_least_def {1 3}/uncurry4.
    iIntros "Hleast". iApply (least_fixpoint_ind with "[] Hleast"); clear Φ π e_t e_s.
    iModIntro. iIntros ([[[Φ π] e_t] e_s]).
    erewrite least_fixpoint_unfold; last first.
    { eapply global_least_def_body_mono, _. }
    rewrite {1 3}/curry4.
    iApply (gsim_expr_inner_mono with "[] []").
    { iModIntro. iIntros (Φ' π' e_t' e_s') "$". }
      iModIntro; iIntros (Φ' π' e_t' e_s'); by iApply "Hmon".
  Qed.

  Lemma global_least_def_unfold G Φ π e_t e_s:
    NonExpansive G →
    global_least_def G Φ π e_t e_s ≡ gsim_expr_inner G (global_least_def G) Φ π e_t e_s.
  Proof.
    intros ?; rewrite {1}/global_least_def {1}/uncurry4 least_fixpoint_unfold {1}/curry4 //=.
  Qed.

  Instance global_greatest_def_body_mono :
    BiMonoPred (λ (greatest_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO → PROP), curry4 (global_least_def (uncurry4 greatest_rec))).
  Proof.
    constructor.
    - intros G1 G2 HG1 HG2. iIntros "#H" (x).
      destruct x as [[[Φ π] e_t] e_s]; rewrite /curry4.
      iApply global_least_def_mono. iModIntro.
      iIntros (Φ' π' e_t' e_s'); iApply "H".
    - intros G Hne n x y Heq. rewrite /least_def -!curry4_uncurry4.
      eapply least_fixpoint_ne'; last done.
      intros L HL m [[[Φ π] e_t] e_s] [[[Ψ π'] e_t'] e_s'] Heq'; simpl.
      eapply gsim_expr_inner_ne; [| |eapply Heq'..].
      + intros ??? ??->%leibniz_equiv. eapply uncurry4_ne; [apply Hne | done].
      + intros ??? ??->%leibniz_equiv. eapply uncurry4_ne; [apply HL | done].
  Qed.

  Definition global_greatest_def : expr_rel -d> thread_id -d> expr_rel :=
    uncurry4 (bi_greatest_fixpoint (λ (greatest_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO → PROP), curry4 (global_least_def (uncurry4 greatest_rec)))).

  Lemma global_greatest_def_unfold Φ π e_t e_s:
    global_greatest_def Φ π e_t e_s ≡ global_least_def global_greatest_def Φ π e_t e_s.
  Proof.
    rewrite {1}/global_greatest_def {1}/uncurry4 greatest_fixpoint_unfold {1}/curry4 //=.
  Qed.

  Global Instance global_greatest_def_ne: NonExpansive global_greatest_def.
  Proof. eapply @uncurry4_ne. solve_proper. Qed.

  Global Instance global_greatest_def_proper: Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) global_greatest_def.
  Proof.
    intros Φ Ψ Heq π π' <-%leibniz_equiv e_t e_t' <-%leibniz_equiv e_s e_s' <-%leibniz_equiv.
    revert π e_t e_s. change (global_greatest_def Φ ≡ global_greatest_def Ψ).
    eapply ne_proper; first apply _. done.
  Qed.

  Lemma global_greatest_def_fixpoint Φ π e_t e_s:
    global_greatest_def Φ π e_t e_s ≡ gsim_expr_inner global_greatest_def global_greatest_def Φ π e_t e_s.
  Proof.
    rewrite global_greatest_def_unfold global_least_def_unfold.
    eapply gsim_expr_inner_proper; eauto.
    - solve_proper.
    - intros Φ' Ψ' Heq. intros ??? ??. rewrite -global_greatest_def_unfold.
      f_equiv; done.
  Qed.

  End sim_def.

  Implicit Types (Ω : thread_id → val Λ → val Λ → PROP).

  Definition gsim_expr_aux : seal (λ Ω, global_greatest_def Ω).
  Proof. by eexists. Qed.
  Definition gsim_expr := (gsim_expr_aux).(unseal).
  Lemma gsim_expr_eq : gsim_expr = λ Ω Φ π e_t e_s, @global_greatest_def Ω Φ π e_t e_s.
  Proof. rewrite -gsim_expr_aux.(seal_eq) //. Qed.

  Lemma gsim_expr_fixpoint Ω Φ π e_t e_s:
    gsim_expr Ω Φ π e_t e_s ⊣⊢ gsim_expr_inner Ω (gsim_expr Ω) (gsim_expr Ω) Φ π e_t e_s.
  Proof.
    rewrite gsim_expr_eq global_greatest_def_fixpoint //.
  Qed.

  Lemma gsim_expr_unfold Ω Φ π e_t e_s:
    gsim_expr Ω Φ π e_t e_s ⊣⊢
    (∀ P_t σ_t P_s σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ -∗ |==>
      (* base case *)
      (∃ e_s' σ_s', ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗
        state_interp P_t σ_t P_s σ_s' (<[π := fill K_s e_s']> T_s) ∗ Φ e_t e_s')

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ -∗ |==>
        (* stuttering *)
        (⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s T_s ∗ gsim_expr Ω Φ π e_t' e_s) ∨
        (* take a step *)
        (∃ e_s' e_s'' σ_s' σ_s'' efs_s,
          ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗
          ⌜prim_step P_s e_s' σ_s' e_s'' σ_s'' efs_s⌝ ∗
          (* TODO: This length constraint is unnecessary as it is implied by the big_sepL2. *)
          ⌜length efs_t = length efs_s⌝ ∗
          state_interp P_t σ_t' P_s σ_s'' (<[π := fill K_s e_s'']> T_s ++ efs_s) ∗
          gsim_expr Ω Φ π e_t' e_s'' ∗
          [∗ list] π'↦e_t; e_s ∈ efs_t; efs_s, gsim_expr Ω (lift_post (Ω (length T_s + π'))) (length T_s + π') e_t e_s))
    )%I.
  Proof.
    rewrite gsim_expr_fixpoint /gsim_expr_inner //.
  Qed.

  Global Instance gsim_expr_ne Ω:
    NonExpansive4 (gsim_expr Ω: expr_rel → thread_id → expr_rel).
  Proof. rewrite gsim_expr_eq. apply _. Qed.

  Global Instance gsim_expr_proper Ω:
    Proper ((pointwise_relation (expr Λ) (pointwise_relation (expr Λ) (≡))) ==> eq ==> eq ==> eq ==> (≡)) (gsim_expr Ω).
  Proof.
    intros p1 p2 Heq2 π π' -> e e' -> e1 e1' ->.
    rewrite !gsim_expr_eq. eapply global_greatest_def_proper; done.
  Qed.


  Existing Instances global_least_def_body_mono global_greatest_def_body_mono.
  (* any post-fixed point is included in the gfp *)
  Lemma gsim_expr_strong_coind Ω (F : expr_rel → thread_id -d> expr_rel) :
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ global_least_def Ω (λ Φ π e_t e_s, F Φ π e_t e_s ∨ gsim_expr Ω Φ π e_t e_s) Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ gsim_expr Ω Φ π e_t e_s.
  Proof.
    iIntros (Hprop) "#HPre". iIntros (Φ π e_t e_s) "HF".
    rewrite gsim_expr_eq /global_greatest_def {3}/uncurry4.
    set (F_curry := curry4 F).
    assert (NonExpansive F_curry) as Hne; first by eapply @curry4_ne, _.
    change (F Φ π e_t e_s) with (F_curry (Φ, π, e_t, e_s)).
    remember (Φ, π, e_t, e_s) as p. rewrite -Heqp; clear Φ π e_t e_s Heqp.
    iApply (greatest_fixpoint_strong_coind _ F_curry with "[] HF").
    iModIntro. iIntros ([[[Φ π] e_t] e_s]); simpl.
    rewrite /F_curry.
    iApply ("HPre" $! Φ π e_t e_s).
  Qed.

  Lemma gsim_expr_coind Ω (F : expr_rel → thread_id -d> expr_rel) :
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ global_least_def Ω F Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ gsim_expr Ω Φ π e_t e_s.
  Proof.
    iIntros (Hprop) "#HPre". iIntros (Φ π e_t e_s) "HF".
    iApply (gsim_expr_strong_coind with "[] HF"); clear Φ π e_t e_s.
    iModIntro; iIntros (Φ π e_t e_s) "HF".
    iDestruct ("HPre" with "HF") as "HF".
    iApply (global_least_def_mono with "[] HF"); first by solve_proper.
    iModIntro. clear Φ π e_t e_s. iIntros (Φ π e_t e_s) "HF". by iLeft.
  Qed.

  Lemma global_least_def_strong_ind Ω (F R: expr_rel → thread_id -d> expr_rel):
    NonExpansive R →
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, gsim_expr_inner Ω R (λ Ψ π e_t e_s, F Ψ π e_t e_s ∧ global_least_def Ω R Ψ π e_t e_s) Φ π e_t e_s -∗ F Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, global_least_def Ω R Φ π e_t e_s -∗ F Φ π e_t e_s.
  Proof.
    iIntros (Hne1 Hne2) "#HPre". iIntros (Φ π e_t e_s) "HF".
    rewrite {2}/global_least_def {1}/uncurry4.
    set (F_curry := curry4 F).
    assert (NonExpansive F_curry); first by eapply @curry4_ne, _.
    change (F Φ π e_t e_s) with (F_curry (Φ, π, e_t, e_s)).
    remember (Φ, π, e_t, e_s) as p. rewrite -Heqp; clear Φ π e_t e_s Heqp.
    iApply (least_fixpoint_strong_ind _ F_curry with "[] HF").
    iModIntro. iIntros ([[[Φ π] e_t] e_s]); simpl.
    rewrite /F_curry {1}/uncurry4 {1}/curry4.
    iIntros "H". iApply "HPre". iExact "H".
  Qed.

  Lemma global_least_def_ind Ω (F R: expr_rel → thread_id -d> expr_rel):
    NonExpansive R →
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, gsim_expr_inner Ω R F Φ π e_t e_s -∗ F Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, global_least_def Ω R Φ π e_t e_s -∗ F Φ π e_t e_s.
  Proof.
    iIntros (Hne1 Hne2) "#HPre". iApply global_least_def_strong_ind.
    iModIntro. iIntros (Φ π e_t e_s) "Hsim".
    iApply "HPre". iApply (gsim_expr_inner_mono with "[] [] Hsim"); last by auto.
    iModIntro. iIntros (Φ' π' e_t' e_s') "H". iApply bi.and_elim_l. iApply "H".
  Qed.

  (* we change the predicate beause at every recursive ocurrence,
     we give back ownership of the monotonicity assumption *)
  Lemma global_least_def_strong_mono Ω (rec : expr_rel → thread_idO -d> expr_rel) Φ Φ' π e_t e_s:
    NonExpansive rec →
     (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗
     global_least_def Ω rec Φ π e_t e_s -∗
     global_least_def Ω (λ Ψ π e_t e_s, rec Φ π e_t e_s ∗ (∀ e_t e_s, Φ e_t e_s ==∗ Ψ e_t e_s) ∨ rec Ψ π e_t e_s) Φ' π e_t e_s.
  Proof.
    iIntros (Hne) "Hmon Hleast". iRevert (Φ') "Hmon".
    pose (rec' := (λ Φ Ψ π e_t e_s, rec Φ π e_t e_s ∗ (∀ e_t e_s, Φ e_t e_s ==∗ Ψ e_t e_s) ∨ rec Ψ π e_t e_s)%I).
    pose (F_ind := (λ Φ π e_t e_s, ∀ Φ', (∀ e_t e_s : expr Λ, Φ e_t e_s ==∗ Φ' e_t e_s) -∗ global_least_def Ω (rec' Φ) Φ' π e_t e_s)%I).
    assert (NonExpansive2 (rec': expr_rel -d> expr_rel -d> thread_idO -d> expr_rel)) as Rne.
    { intros m Φ' Φ'' Heq1 Ψ Ψ' Heq2 ???; rewrite /rec'.
      solve_proper_core ltac:(fun x => f_equiv || apply Heq1 || apply Heq2). }
    assert (NonExpansive (F_ind: expr_rel -d> thread_idO -d> expr_rel)).
    { clear Φ π e_t e_s. intros n Φ Ψ Heq π e_t e_s.
      rewrite /F_ind; do 3 f_equiv; first (repeat f_equiv; by apply Heq).
      eapply global_least_def_ne; [ |done..]. intros ?. eapply (Rne n Φ Ψ Heq). done. }
    iApply (global_least_def_ind Ω F_ind rec with "[] Hleast"); clear Φ π e_t e_s.
    iModIntro. iIntros (Φ π e_t e_s) "Hrec". iIntros (Φ') "Hmon".
    rewrite global_least_def_unfold /gsim_expr_inner.

    iIntros (P_t σ_t P_s σ_s T_s K_s) "Ha".
    iMod ("Hrec" with "Ha") as "[Hval | Hstep]".
    + iLeft. iDestruct "Hval" as (e_s' σ_s') "(Hnf & SI & HΦ)".
      iExists e_s', σ_s'. iFrame. by iApply "Hmon".
    + iModIntro; iRight. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". rewrite /F_ind. iApply ("H1" with "Hmon"). }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & %Hlen & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame. iSplit; first done.
      iSplitL "H5 Hmon"; first by rewrite /rec'; iLeft; iFrame.
      iApply (big_sepL2_impl with "H6").
      iIntros "!>" (?????) "?"; by iRight.
  Qed.

  Lemma gsim_expr_bupd_mono Ω Φ Φ' π e_t e_s:
    (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗ gsim_expr Ω Φ π e_t e_s -∗ gsim_expr Ω Φ' π e_t e_s.
  Proof.
    iIntros "Ha Hmon".
    iApply (gsim_expr_strong_coind Ω (λ Ψ π e_t e_s, gsim_expr Ω Φ π e_t e_s ∗ (∀ e_t e_s : expr Λ, Φ e_t e_s ==∗ Ψ e_t e_s))%I); last by iFrame.
    { intros n Ψ Ψ' Heq π' e_t' e_s'. repeat f_equiv. by eapply Heq. }
    iModIntro. clear Φ' π e_t e_s. iIntros (Φ' π e_t e_s) "[Ha Hmon]".
    rewrite gsim_expr_eq global_greatest_def_unfold.
    iApply (global_least_def_strong_mono with "Hmon Ha").
  Qed.

  Lemma gsim_expr_mono Ω Φ Φ' π e_t e_s:
    (∀ e_t e_s, Φ e_t e_s -∗ Φ' e_t e_s) -∗ gsim_expr Ω Φ π e_t e_s -∗ gsim_expr Ω Φ' π e_t e_s.
  Proof.
    iIntros "Hmon Ha". iApply (gsim_expr_bupd_mono with "[Hmon] Ha").
    iIntros (??) "?". iModIntro. by iApply "Hmon".
  Qed.


  Lemma gsim_expr_inner_base Ω G L Φ π e_t e_s :
    ⊢ (Φ e_t e_s) -∗ gsim_expr_inner Ω G L Φ π e_t e_s.
  Proof.
    iIntros "He". rewrite /gsim_expr. iIntros (??????) "[Hstate [% %]]".
    iModIntro. iLeft. iExists e_s, σ_s. rewrite list_insert_id //. iFrame. iPureIntro. constructor.
  Qed.

  Lemma gsim_expr_base Ω Φ π e_t e_s :
    ⊢ (Φ e_t e_s) -∗ gsim_expr Ω Φ π e_t e_s.
  Proof.
    iIntros "He". iApply gsim_expr_fixpoint. by iApply gsim_expr_inner_base.
  Qed.

  Lemma gsim_expr_bupd Ω Φ π e_t e_s:
    (gsim_expr Ω (λ e_t' e_s', |==> Φ e_t' e_s') π e_t e_s) -∗ gsim_expr Ω Φ π e_t e_s.
  Proof.
    iIntros "H". iApply (gsim_expr_bupd_mono with "[] H").
    iIntros (??) "$".
  Qed.


  (* Bind Lemma *)
  Local Definition bind_coind_pred Ω :=
    (λ Φ π e_t e_s, (∃ e_t' e_s' (K_t K_s : ectx Λ),
     ⌜e_t = fill K_t e_t'⌝ ∗ ⌜e_s = fill K_s e_s'⌝ ∗
     gsim_expr Ω (λ e_t'' e_s'', gsim_expr Ω Φ π (fill K_t e_t'') (fill K_s e_s'')) π e_t' e_s'))%I.

  Local Definition bind_coind_rec Ω :=
    (λ Φ π e_t e_s, (∃ e_t' e_s' (K_t K_s : ectx Λ),
      ⌜e_t = fill K_t e_t'⌝ ∗ ⌜e_s = fill K_s e_s'⌝ ∗
      gsim_expr Ω (λ e_t'' e_s'', gsim_expr Ω Φ π (fill K_t e_t'') (fill K_s e_s'')) π e_t' e_s') ∨ gsim_expr Ω Φ π e_t e_s)%I.

  Local Instance bind_coind_pred_ne Ω: NonExpansive (bind_coind_pred Ω: expr_rel → thread_idO -d> expr_rel).
  Proof.
    rewrite /bind_coind_pred. solve_proper_prepare; repeat f_equiv.
    intros ??; by f_equiv.
  Qed.

  Local Instance bind_coind_rec_ne Ω: NonExpansive (bind_coind_rec Ω: expr_rel → thread_idO -d> expr_rel).
  Proof.
    rewrite /bind_coind_pred. solve_proper_prepare; repeat f_equiv; last done.
    intros ??; by f_equiv.
  Qed.


  Lemma gsim_expr_bind Ω K_t K_s e_t e_s Φ π :
    gsim_expr Ω (λ e_t' e_s', gsim_expr Ω Φ π (fill K_t e_t') (fill K_s e_s')) π e_t e_s -∗
    gsim_expr Ω Φ π (fill K_t e_t) (fill K_s e_s).
  Proof.
    iIntros "H".
    iApply (gsim_expr_strong_coind Ω (bind_coind_pred Ω)%I); last first.
    { iExists e_t, e_s, K_t, K_s; iFrame; iSplit; by iPureIntro. }
    iModIntro. clear Φ π e_t e_s K_t K_s.
    iIntros (Φ π e_t' e_s') "IH". change (global_least_def Ω _ Φ π e_t' e_s') with (global_least_def Ω (bind_coind_rec Ω) Φ π e_t' e_s').
    iDestruct "IH" as (e_t e_s K_t K_s) "[-> [-> H]]".
    rewrite {1}gsim_expr_eq global_greatest_def_unfold.
    pose (F := (λ Ψ π e_t e_s, ∀ Φ, (∀ e_t e_s, Ψ e_t e_s -∗ gsim_expr Ω Φ π (fill K_t e_t) (fill K_s e_s)) -∗ global_least_def Ω (bind_coind_rec Ω) Φ π (fill K_t e_t) (fill K_s e_s))%I).
    assert (NonExpansive (F: expr_rel → thread_idO -d> expr_rel)).
    { rewrite /F. intros n x y Heq ???. repeat f_equiv. apply Heq. }
    iAssert (∀ Ψ π e_t e_s, global_least_def Ω (global_greatest_def Ω) Ψ π e_t e_s -∗ F Ψ π e_t e_s)%I as "Hgen"; last first.
    { iApply ("Hgen" with "H"). iIntros (??) "$". }
    clear Φ π e_t e_s. iIntros (Ψ π e_t e_s) "HL".
    iApply (global_least_def_ind with "[] HL"); clear Ψ π e_t e_s.
    iModIntro. iIntros (Ψ π e_t e_s) "Hinner".
    iIntros (Φ) "Hcont".
    rewrite global_least_def_unfold. rewrite /gsim_expr_inner.
    iIntros (P_t σ_t P_s σ_s T_s K_s') "[Hs [%HT %Hnreach]]". iMod ("Hinner" with "[Hs]") as "H".
    { iFrame. iPureIntro. split; [|done]. by rewrite fill_comp in HT. }
    iDestruct "H" as "[Hval | Hstep]".
    - iDestruct "Hval" as (e_s' σ_s') "(%Hstutter & Hstate & Hpost)".
      (* we prove that we can stutter the source and still end up at the right place *)
      iSpecialize ("Hcont" with "Hpost"). rewrite gsim_expr_unfold.
      iMod ("Hcont" with "[$Hstate]") as "[Val|Step]".
      + iPureIntro. rewrite -fill_comp list_lookup_insert; [ | by apply: lookup_lt_Some].
        split; [done|]. apply: pool_safe_no_forks; [done..|].
        apply fill_no_forks. by apply fill_no_forks.
      + iModIntro. iLeft. iDestruct "Val" as (e_s'' σ_s'' Hnf') "[SI HΦ]".
        iExists e_s'', σ_s''. rewrite list_insert_insert. iFrame. iPureIntro. eapply no_forks_trans, Hnf'.
        by eapply fill_no_forks.
      + iModIntro. iRight.
        iDestruct "Step" as "($ & Step)".
        iIntros (e_t' efs_t σ_t' Hprim_t).
        iMod ("Step" with "[//]") as "[(-> & SI & Sim)|Step]".
        * destruct (no_forks_inv_r _ _ _ _ _ Hstutter) as [(-> & ->)|(e_s'' & σ_s'' & Hsteps & Hstep)].
          -- iModIntro. iLeft. rewrite -fill_comp list_insert_id //.
             iFrame. iSplit; first done.
             rewrite gsim_expr_eq global_greatest_def_unfold.
             iApply (global_least_def_mono with "[] Sim").
             clear; iModIntro. iIntros (Φ π e_t e_s) "Hrec". iRight.
             by rewrite gsim_expr_eq.
          -- iModIntro. iRight. rewrite -fill_comp.
             iExists (fill K_s e_s''), (fill K_s e_s'), σ_s'', σ_s', []. rewrite app_nil_r.
             iSplit; first by iPureIntro; eapply fill_no_forks.
             iSplit; first by iPureIntro; eapply fill_prim_step, Hstep.
             iSplit; first done. by iFrame.
        * iDestruct "Step" as (e_s'' e_s''' σ_s'' σ_s''' efs_s Hforks) "(Hprim & Hlen & SI & Hsim & Hforks)".
          iModIntro. iRight. iExists e_s'', e_s''', σ_s'', σ_s''', efs_s.
          rewrite list_insert_insert. iFrame.
          iSplit; first by iPureIntro; eauto using no_forks_trans, fill_no_forks.
          iApply (big_sepL2_impl with "Hforks"). clear.
          iIntros "!>" (π' e_t e_s ??) "H". rewrite insert_length. by iRight.
    - iModIntro. iRight;  iDestruct "Hstep" as "[%Hred Hstep]".
      iSplitR. { iPureIntro. by apply fill_reducible. }
      iIntros (e_t' efs σ_t') "%Hstep".
      destruct (fill_reducible_prim_step _ _ _ _ _ _ _ Hred Hstep) as (e_t'' & -> & Hstep').
      iMod ("Hstep" with "[]") as "Hstep". { iPureIntro. apply Hstep'. }
      iModIntro. iDestruct "Hstep" as "[(Hnf & Hstate & Hstutter) | Hstep]".
      + iLeft. iFrame. by iApply "Hstutter".
      + iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs') "(%Hnf & %Hstep'' & %Hlen & Hstate & Hrec & Hfrk)".
        iExists (fill K_s e_s'), (fill K_s e_s''), σ_s', σ_s'', efs'.
        rewrite -fill_comp. iFrame.
        iSplitR. { iPureIntro. by apply fill_no_forks. }
        iSplitR. { iPureIntro. by apply fill_prim_step. }
        iSplitR. { done. }
        iSplitL "Hcont Hrec".
        { iLeft. iExists e_t'', e_s'', K_t, K_s.
          do 2 (iSplitR; first done).
          iApply (gsim_expr_mono with "Hcont"); by rewrite gsim_expr_eq. }
        { iApply (big_sepL2_impl with "Hfrk").
          iIntros "!>" (?????) "?". iRight. by rewrite gsim_expr_eq. }
  Qed.

  Lemma gsim_expr_decompose Ω e_t e_s π Φ Ψ:
    gsim_expr Ω Ψ π e_t e_s -∗
    (∀ e_t e_s, Ψ e_t e_s -∗ gsim_expr Ω Φ π e_t e_s) -∗
    gsim_expr Ω Φ π e_t e_s.
  Proof.
    iIntros "H1 H2".
    rewrite -{2}(fill_empty e_t) -{2}(fill_empty e_s).
    iApply (gsim_expr_bind _ empty_ectx empty_ectx).
    iApply (gsim_expr_mono with "[H2] H1").
    clear. iIntros (e_t e_s). by rewrite !fill_empty.
  Qed.


  Definition gjoin_expr Ω (F: expr_rel -d> thread_idO -d> expr_rel) : expr_rel -d> thread_idO -d> expr_rel :=
    λ Φ π, gsim_expr Ω (λ e_t e_s, F Φ π e_t e_s ∨ Φ e_t e_s)%I π.

  Global Instance gjoin_expr_ne Ω F:
    NonExpansive F →
    NonExpansive (gjoin_expr Ω F).
  Proof.
    intros ???? Heq ???. rewrite /gjoin_expr. f_equiv.
    intros ??. repeat f_equiv; by apply Heq.
  Qed.
  Lemma gsim_expr_paco Ω F Φ π e_t e_s:
    NonExpansive (F: expr_rel → thread_idO -d> expr_rel) →
    □ (∀ Φ π e_t e_s, F Φ π e_t e_s -∗ lock_step (gjoin_expr Ω F Φ π) π e_t e_s) -∗
    F Φ π e_t e_s -∗ gsim_expr Ω Φ π e_t e_s.
  Proof.
    iIntros (Hne) "#Hlock_step HF".
    iApply (gsim_expr_strong_coind _ (gjoin_expr Ω F)%I); last first.
    { rewrite /gjoin_expr. iApply gsim_expr_base. by iLeft. }
    iModIntro. clear Φ π e_t e_s. iIntros (Φ π e_t e_s) "Hs".
    rewrite {2}/gjoin_expr gsim_expr_eq global_greatest_def_unfold.
    pose (rec := (λ Φ π e_t e_s, gjoin_expr Ω F Φ π e_t e_s ∨ global_greatest_def Ω Φ π e_t e_s)%I).
    assert (NonExpansive (rec: expr_rel → thread_idO -d> expr_rel)).
    { intros ??? Heq ???. solve_proper. }
    pose (Rec := (λ Ψ π e_t e_s, ∀ Φ, (∀ e_t e_s, Ψ e_t e_s -∗ F Φ π e_t e_s ∨ Φ e_t e_s) -∗ global_least_def Ω rec Φ π e_t e_s)%I).
    assert (NonExpansive (Rec: expr_rel → thread_idO -d> expr_rel)).
    { intros ??? Heq ???. rewrite /Rec. repeat f_equiv. by eapply Heq. }
    iApply (global_least_def_ind _ Rec with "[] Hs []"); last auto.
    iModIntro. clear Φ π e_t e_s. iIntros (Ψ π e_t e_s) "Hinner".
    iIntros (Φ) "Hmon". rewrite global_least_def_unfold.
    rewrite /gsim_expr_inner.
    iIntros (P_t σ_t P_s σ_s T_s K_s) "[Hs [%HT %Hsafe]]". iMod ("Hinner" with "[$Hs //]") as "H".
    iDestruct "H" as "[Hval | Hstep]".
    - iDestruct "Hval" as (e_s' σ_s') "(%Hstutter & Hstate & Hpost)".
      (* we prove that we can stutter the source and still end up at the right place *)
      iDestruct ("Hmon" with "Hpost") as "[HF|Hpost]"; last first.
      { iModIntro. iLeft. iExists _, _. iFrame. by iPureIntro. }
      iMod ("Hlock_step" with "HF [$Hstate ]") as "[Hred Hstep]".
      { iPureIntro. rewrite list_lookup_insert; [ | by apply: lookup_lt_Some]. split; [done|].
        apply: pool_safe_no_forks; [done..|]. by apply fill_no_forks. }
      iModIntro. iRight. iFrame.
      iIntros (e_t' efs_t σ_t' Hprim_t). iMod ("Hstep" with "[//]") as (e_s'' σ_s'' -> Hnfs) "[SI Hjoin]".
      iModIntro. iRight. rewrite list_insert_insert. iExists e_s', e_s'', σ_s', σ_s'', []; simpl.
      rewrite app_nil_r. iFrame.
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
        iApply (big_sepL2_impl with "Hfrk").
        iIntros "!>" (?????) "?". by iRight.
  Qed.

  Lemma bupd_gsim_expr Ω Φ π e_t e_s:
    ⊢ (|==> gsim_expr Ω Φ π e_t e_s) -∗ gsim_expr Ω Φ π e_t e_s.
  Proof.
    iIntros "Hv". rewrite gsim_expr_unfold. iIntros (??????) "H". iMod "Hv". iApply ("Hv" with "H").
  Qed.


  Lemma gsim_step_source Ω e_t e_s Φ π :
    (∀ P_s σ_s P_t σ_t T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ∃ e_s' σ_s', ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗ state_interp P_t σ_t P_s σ_s' (<[π:=fill K_s e_s']>T_s) ∗ gsim_expr Ω Φ π e_t e_s') -∗
      gsim_expr Ω Φ π e_t e_s.
  Proof.
    rewrite gsim_expr_unfold. iIntros "Hsource" (P_t σ_t P_s σ_s T_s K_s) "[Hstate [%HT %Hsafe]]".
    iMod ("Hsource" with "[$Hstate //]") as (e_s' σ_s') "(%Hexec & Hstate & Hsim)".
    rewrite {1}gsim_expr_unfold.
    iMod ("Hsim" with "[Hstate]") as "Hsim".
    { iFrame. iPureIntro. rewrite list_lookup_insert; [ | by apply: lookup_lt_Some]. split; [done|].
        apply: pool_safe_no_forks; [done..|]. by apply fill_no_forks. }
    iModIntro. iDestruct "Hsim" as "[Hval | Hstep]".
    - iLeft. iDestruct "Hval" as (e_s'' σ_s'') "(% & Hstate & Hphi)". rewrite list_insert_insert.
      iExists e_s'', σ_s''. iFrame. iPureIntro. by eapply no_forks_trans.
    - iDestruct "Hstep" as "(%&Hstep)". iRight.
      iSplitR; first by iPureIntro.
      iIntros (e_t' efs_t σ_t') "Hprim". iMod ("Hstep" with "Hprim") as "[Hstutter | Hred]"; iModIntro.
      + (* which path we want to take depends on the rtc we have *)
        eapply no_forks_inv_r in Hexec as [(-> & ->)|(e_s'' & σ_s'' & Hnfs & Hnf)].
        { (* no step, just mirror the stuttering *) iLeft. rewrite list_insert_id //. }
        (* we have actually taken a source step *)
        iRight. iExists e_s'', e_s', σ_s'', σ_s', []. rewrite app_nil_r.
        iDestruct "Hstutter" as "(-> & SI & Hsim)"; simpl; iFrame.
        by iPureIntro.
      + iRight. iDestruct "Hred" as (e_s'' e_s''' σ_s'' σ_s''' efs_s) "(%Hnfs & Hstep & Hlen & Hstate & Hsim & Hfrks)".
        rewrite list_insert_insert insert_length.
        iExists e_s'', e_s''', σ_s'', σ_s''', efs_s. iFrame. iPureIntro.
        by eapply no_forks_trans.
  Qed.

  (* the step case of the simulation relation, but the two cases are combined into an rtc in the source *)
  Lemma gsim_step_target Ω e_t e_s Φ π:
    (∀ P_t P_s σ_t σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
      ∃ e_s' σ_s', ⌜efs_t = []⌝ ∗ ⌜no_forks P_s e_s σ_s e_s' σ_s'⌝ ∗ state_interp P_t σ_t' P_s σ_s' (<[π:=fill K_s e_s']>T_s) ∗ gsim_expr Ω Φ π e_t' e_s') -∗
    gsim_expr Ω Φ π e_t e_s.
  Proof.
    iIntros "Hsim". rewrite gsim_expr_unfold. iIntros (??????) "[Hstate [% %]]".
    iMod ("Hsim" with "[$Hstate ]") as "[Hred Hsim]"; first done. iModIntro. iRight.
    iFrame. iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hsim" with "Hstep") as (e_s' σ_s') "(-> & %Hs & ? & ?)".
    apply no_forks_inv_r in Hs as [ [-> ->] | (e_s'' & σ_s'' & Hstep & Hsteps)].
    - iLeft. rewrite list_insert_id //. by iFrame.
    - iRight; iExists e_s'', e_s', σ_s'', σ_s', []. rewrite app_nil_r. iModIntro; simpl; iFrame.
      by iPureIntro.
  Qed.


  (* we show that the local simulation for all functions in the program implies the global simulation *)
  Definition local_rel Ω P_t P_s : PROP :=
    (□ ∀ f K_s π, ⌜P_s !! f = Some K_s⌝ → ∃ K_t, ⌜P_t !! f = Some K_t⌝ ∗ sim_ectx Ω π K_t K_s (Ω π))%I.
  Typeclasses Opaque local_rel.

  Global Instance local_rel_persistent Ω P_s P_t : Persistent (local_rel Ω P_s P_t).
  Proof. rewrite /local_rel; apply _. Qed.

  Lemma local_to_global Ω P_t P_s Φ e_t e_s π:
    local_rel Ω P_t P_s -∗
    progs_are P_t P_s -∗
    sim_expr Ω Φ π e_t e_s -∗
    gsim_expr Ω Φ π e_t e_s.
  Proof.
    rewrite /local_rel; iIntros "#Hloc #Hprog Hsim".
    assert (NonExpansive (sim_expr Ω : expr_rel → thread_id -d> expr_rel)).
    { solve_proper. }
    iApply (gsim_expr_coind Ω (sim_expr Ω) with "[] Hsim"); clear Φ π e_t e_s.
    iModIntro. iIntros (Φ π e_t e_s).
    rewrite {1}sim_expr_eq greatest_def_unfold.
    iIntros "H". iApply (least_def_ind _ (global_least_def Ω (sim_expr Ω)) with "[] H"); clear Φ π e_t e_s.
    iModIntro. iIntros (Φ π e_t e_s) "Hsim".
    rewrite global_least_def_unfold.
    iIntros (P_t' σ_t P_s' σ_s T_s K_s) "[Hstate [% %]]".
    rewrite /progs_are; iDestruct ("Hprog" with "Hstate") as "[% %]"; subst P_t' P_s'.
    iMod ("Hsim" with "[$Hstate //]") as "[Hsim|[Hsim|Hsim]]"; iModIntro; [ eauto | rewrite sim_expr_eq; eauto | ].
    iDestruct "Hsim" as (f K_t v_t K_s' v_s σ_s') "(% & %Hnfs & Hval & Hstate & Hcont)".
    subst e_t. iRight.
    (* the function is in the source table *)
    edestruct (@safe_call_in_prg Λ) as [K_f_s Hdef_s]; [ |done|].
    { eapply fill_safe. by eapply pool_safe_threads_safe. }

    (* we prove reducibility and the step case *)
    iSplit.
    - iAssert (∃ K_f_t, ⌜P_t !! f = Some K_f_t⌝)%I as (K_f_t) "%".
      { iDestruct ("Hloc" $! _ _ π Hdef_s) as (K_f_t) "[% _]"; by eauto. }
      iPureIntro. eexists _, _, _.
      by apply fill_prim_step, head_prim_step, call_head_step_intro.
    - iIntros (e_t' efs_t σ_t' Hstep).
      apply prim_step_call_inv in Hstep as (K_f_t & Hdef & -> & -> & ->).
      iModIntro. iRight. iExists (fill K_s' (of_call f v_s)), (fill K_s' (fill K_f_s (of_val v_s))), σ_s', σ_s', [].
      iFrame. iSplit; first done. iSplit.
      { iPureIntro. by apply fill_prim_step, head_prim_step, call_head_step_intro. }
      iSplit; first done.
      iSplitL "Hstate".
      { rewrite app_nil_r. iPoseProof (state_interp_pure_prim_step with "Hstate") as "Hstate".
        { apply list_lookup_insert. by eapply lookup_lt_Some. }
        2: { rewrite list_insert_insert. iFrame. }
        intros σ_s''. eapply fill_prim_step, fill_prim_step. by eapply head_prim_step, call_head_step_intro.
      }
      simpl; iSplit; last done.
      iApply sim_expr_bind. iDestruct ("Hloc" $! _ _ _ Hdef_s) as (K_f_t') "[% Hectx]".
      replace K_f_t' with K_f_t by naive_solver. rewrite /sim_ectx.
      iApply (sim_expr_mono with "[-Hval] [Hval]"); last by iApply "Hectx".
      iIntros (e_t' e_s'). iDestruct 1 as (v_t' v_s' -> ->) "Hval".
      rewrite sim_expr_eq. by iApply "Hcont".
  Qed.


  Lemma local_to_global_call Ω P_t P_s f v_t v_s π:
    is_Some (P_s !! f) →
    local_rel Ω P_t P_s -∗
    progs_are P_t P_s -∗
    Ω π v_t v_s -∗
    gsim_expr Ω (lift_post (Ω π)) π (of_call f v_t) (of_call f v_s).
  Proof.
    iIntros ([K_s Hlook]) "#Hloc #Hprogs Hval".
    iApply (local_to_global with "Hloc Hprogs").
    rewrite /local_rel.
    iDestruct "Hloc" as "#Hloc".
    iDestruct ("Hloc" $! _ _ _ Hlook) as (K_t) "[% Hsim]".
    iApply sim_call_inline; last (iFrame; iSplit; first done); eauto.
  Qed.
End fix_lang.
