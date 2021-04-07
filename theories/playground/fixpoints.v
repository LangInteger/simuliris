From iris.prelude Require Import options prelude.

Class Lattice (L: Type) (le: relation L) `{!PreOrder le} `{!Equiv L} := {
  sup: (L → Prop) → L;
  inf: (L → Prop) → L;
  sup_is_upper_bound l (A: L → Prop): A l → le l (sup A);
  sup_is_least_upper_bound l (A: L → Prop):
    (∀ l', A l' → le l' l) → le (sup A) l;
  inf_is_lower_bound l (A: L → Prop): A l → le (inf A) l;
  inf_is_greatest_lower_bound l (A: L → Prop):
    (∀ l', A l' → le l l') → le l (inf A);
  anti_symm l l': le l l' → le l' l → l ≡ l'
}.

Class Mono `{Lattice L leq} (f: L → L) := {
  mono l1 l2: leq l1 l2 → leq (f l1) (f l2)
}.

Global Hint Mode Mono - - - - - + : typeclass_instances.

Section lattice_properties.
  Context `{Lattice L leq}.

  Infix "⪯" := leq (at level 60).

  Definition top := sup (λ _, True).
  Definition bot := inf (λ _, True).

  Lemma top_upper_bound l: l ⪯ top.
  Proof.
    by eapply sup_is_upper_bound.
  Qed.

  Lemma bot_lower_bound l: bot ⪯ l.
  Proof.
    by eapply inf_is_lower_bound.
  Qed.

  Definition gfp f := sup (λ x, x ⪯ f x).
  Definition lfp f := inf (λ x, f x ⪯ x).

  Lemma gfp_greatest_post_fixpoint f l:
    l ⪯ f l → l ⪯ gfp f.
  Proof.
    intros Hle. by eapply sup_is_upper_bound.
  Qed.

  Lemma gfp_post_fixpoint f `{!Mono f}:
    (gfp f) ⪯ f (gfp f).
  Proof.
    eapply sup_is_least_upper_bound.
    intros l Hle. etrans; first apply Hle.
    eapply gfp_greatest_post_fixpoint in Hle.
    by eapply mono.
  Qed.

  Lemma gfp_pre_fixpoint f `{!Mono f}:
    f (gfp f) ⪯ (gfp f).
  Proof.
    eapply gfp_greatest_post_fixpoint.
    eapply mono. eapply gfp_post_fixpoint; first done.
  Qed.

  Lemma gfp_fixpoint f `{!Mono f}:
    gfp f ≡ f (gfp f).
  Proof.
    eapply anti_symm; eauto using gfp_post_fixpoint, gfp_pre_fixpoint.
  Qed.

  Lemma lfp_least_pre_fixpoint f l:
    f l ⪯ l → lfp f ⪯ l.
  Proof.
    intros Hle. by eapply inf_is_lower_bound.
  Qed.

  Lemma lfp_pre_fixpoint f `{!Mono f}:
    f (lfp f) ⪯ (lfp f).
  Proof.
    eapply inf_is_greatest_lower_bound.
    intros l Hle. etrans; last apply Hle.
    eapply lfp_least_pre_fixpoint in Hle.
    by eapply mono.
  Qed.

  Lemma lfp_post_fixpoint f `{!Mono f}:
     (lfp f) ⪯ f (lfp f).
  Proof.
    eapply lfp_least_pre_fixpoint.
    eapply mono. eapply lfp_pre_fixpoint; first done.
  Qed.

  Lemma lfp_fixpoint f `{!Mono f}:
    lfp f ≡ f (lfp f).
  Proof.
    eapply anti_symm; eauto using lfp_post_fixpoint, lfp_pre_fixpoint.
  Qed.

End lattice_properties.

Global Instance Prop_Preorder: PreOrder impl.
Proof. split; unfold impl; eauto 10. Qed.

Global Instance Prop_equiv: Equiv Prop := iff.

Global Instance Prop_equivalence: Equivalence (@equiv Prop equiv).
Proof. split; intuition. intros ??? [][]. split; eauto. Qed.

Global Program Instance Prop_Lattice: Lattice Prop impl :=
  {| sup F := ∃ P, F P ∧ P; inf F := ∀ P, F P → P |}.
Next Obligation.
  intros P F; unfold impl; eauto.
Qed.
Next Obligation.
  intros P F; unfold impl.
  intros H [? []]. eapply H; done.
Qed.
Next Obligation.
  intros P F H H'; unfold impl; eapply H', H.
Qed.
Next Obligation.
  intros P F; unfold impl.
  intros H HP Q FQ. eapply H; done.
Qed.
Next Obligation.
  rewrite /impl. by split.
Qed.


Global Instance pointwise_Preorder A B (R: relation B) `{!PreOrder R}: PreOrder (pointwise_relation A R).
Proof. split; unfold impl.
  - intros ??. done.
  - intros ??? H1 H2 a. etrans; eauto.
Qed.

Global Instance pointwise_equiv A `{Equiv B}: Equiv (A → B) := pointwise_relation A equiv.

Global Instance pointwise_equivalence A `{eq: Equiv B} `{!Equivalence eq}: Equivalence (@equiv (A → B) _).
Proof. split; intuition. intros ????? a. etrans; eauto. Qed.


Global Program Instance  pointwise_Lattice A `{@Lattice B leq Pre equ}: @Lattice (A → B) (pointwise_relation A leq) (@pointwise_Preorder _ _ _ Pre) (@pointwise_equiv _ _ equ):=
  {| sup F := λ a, sup (λ b, ∃ f, F f ∧ f a = b); inf F := λ a, inf (λ b, ∃ f, F f ∧ f a = b) |}.
Next Obligation.
  intros A B leq Pre equ Lat f F Ff a. eapply sup_is_upper_bound.
  exists f. split; done.
Qed.
Next Obligation.
  intros A B leq Pre equ Lat f F upper a. eapply sup_is_least_upper_bound.
  intros b [g [Fg Hab]]. subst b. by eapply upper.
Qed.
Next Obligation.
  intros A B leq Pre equ Lat f F Ff a. eapply inf_is_lower_bound.
  exists f. split; done.
Qed.
Next Obligation.
  intros A B leq Pre equ Lat f F lower a. eapply inf_is_greatest_lower_bound.
  intros b [g [Fg Hab]]. subst b. by eapply lower.
Qed.
Next Obligation.
  intros A B leq Pre equ Lat f g Hfg Hgf. intros a; eapply anti_symm.
  - eapply Hfg.
  - eapply Hgf.
Qed.


Definition lattice_leq `{Lattice L leq} := leq.
Infix "⪯" := lattice_leq (at level 60).


Lemma lfp_mono `{Lattice L leq} (f g: L → L) `{!Mono g}:
  f ⪯ g → lfp f ⪯ lfp g.
Proof.
  intros Hle. eapply lfp_least_pre_fixpoint.
  etrans; last eapply lfp_pre_fixpoint, _.
  eapply Hle.
Qed.

Lemma gfp_mono `{Lattice L leq} (f g: L → L) `{!Mono f}:
  f ⪯ g → gfp f ⪯ gfp g.
Proof.
  intros Hle. eapply gfp_greatest_post_fixpoint.
  etrans; first eapply gfp_post_fixpoint, _.
  eapply Hle.
Qed.





(* small lockstep simulation example *)
(* Section simulation.
  Context (expr: Type) (step: expr → expr → Prop) (val: expr → Prop).

  Definition sim :=
    gfp (λ sim e_t e_s,
      ((val e_t) ∧ (val e_s)) ∨
      (∀ e_t', step e_t e_t' → ∃ e_s', step e_s e_s' ∧ sim e_t' e_s')).

  Global Instance sim_func_mono :
    Mono (λ sim e_t e_s,
    ((val e_t) ∧ (val e_s)) ∨
    (∀ e_t', step e_t e_t' → ∃ e_s', step e_s e_s' ∧ sim e_t' e_s')).
  Proof.
    split. intros sim sim' Himpl e_t e_s.
    intros [|Hsim]; [eauto|right].
    intros e_t' Hstep; destruct (Hsim e_t' Hstep) as [e_s' [Hstep' Hsim2]].
    exists e_s'. split; first done. by eapply Himpl.
  Qed.

  Lemma sim_fixpoint e_t e_s:
    sim e_t e_s ≡
    (((val e_t) ∧ (val e_s)) ∨
    (∀ e_t', step e_t e_t' → ∃ e_s', step e_s e_s' ∧ sim e_t' e_s')).
  Proof.
    rewrite {1}/sim. by rewrite {1}gfp_fixpoint.
  Qed.

  Lemma sim_coinduction (P : expr → expr → Prop):
    (∀ e_t e_s, P e_t e_s →
      val e_t ∧ val e_s
      ∨ (∀ e_t' : expr,
         step e_t e_t' → ∃ e_s' : expr, step e_s e_s' ∧ P e_t' e_s')) →
    ∀ e_t e_s, P e_t e_s → sim e_t e_s.
  Proof.
    rewrite /sim. intros IH. change (lattice_leq P sim).
    eapply gfp_greatest_post_fixpoint.
    exact IH.
  Qed.
End simulation. *)



(*
(* coindutive inductive fairness *)
Section fairness.
  Context (expr: Type) (step: gmap nat expr → nat → gmap nat expr → Prop) (val: expr → Prop) (is_val: ∀ e, Decision (val e)).
  Implicit Types (e: expr) (T: gmap nat expr) (O: gset nat).


  Definition active_exprs T :=
    dom (gset nat) (filter (λ '(i, e), ¬ val e) T).

  Lemma active_expr_spec T i:
    i ∈ active_exprs T ↔ ∃ e, T !! i = Some e ∧ ¬ val e.
  Proof.
    rewrite /active_exprs elem_of_dom. split.
    - intros [e Hlook]. exists e. by eapply map_filter_lookup_Some in Hlook.
    - intros [e H]. exists e. by eapply map_filter_lookup_Some.
  Qed.

  Definition fair_div :=
    gfp (λ fair_div T,
      lfp (λ steps T O,
        (O ≡ ∅ ∧ fair_div T) ∨
        (∃ T' i, step T i T' ∧ steps T' (O ∖ {[i]}))
      ) T (active_exprs T)).


End fairness. *)
