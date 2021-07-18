(** This file has been adapted from the Iris development, available at 
  https://gitlab.mpi-sws.org/iris/iris
*)

From iris.bi Require Export bi.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
Import bi.

(** Least and greatest fixpoint of a monotone function, defined entirely inside
    the logic.  *)
Class BiMonoPred {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) := {
  bi_mono_pred (Φ Ψ : A → PROP): NonExpansive Φ → NonExpansive Ψ → ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x;
  bi_mono_pred_ne Φ : NonExpansive Φ → NonExpansive (F Φ)
}.
Global Arguments bi_mono_pred {_ _ _ _} _ _ _ _.
Local Existing Instance bi_mono_pred_ne.

Definition bi_least_fixpoint {PROP : bi} {A : ofe}
    (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  tc_opaque (∀ Φ : A -n> PROP, □ (∀ x, F Φ x -∗ Φ x) -∗ Φ x)%I.
Global Arguments bi_least_fixpoint : simpl never.

Definition bi_greatest_fixpoint {PROP : bi} {A : ofe}
    (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  tc_opaque (∃ Φ : A -n> PROP, □ (∀ x, Φ x -∗ F Φ x) ∗ Φ x)%I.
Global Arguments bi_greatest_fixpoint : simpl never.


Global Instance least_fixpoint_ne' {PROP : bi} {A : ofe} (F: (A → PROP) → (A → PROP)):
  (∀ Φ, NonExpansive Φ → NonExpansive (F Φ)) → NonExpansive (bi_least_fixpoint F).
Proof. solve_proper. Qed.
Global Instance least_fixpoint_ne {PROP : bi} {A : ofe} n :
  Proper (pointwise_relation (A → PROP) (pointwise_relation A (dist n)) ==>
          dist n ==> dist n) bi_least_fixpoint.
Proof. solve_proper. Qed.
Global Instance least_fixpoint_proper {PROP : bi} {A : ofe} :
  Proper (pointwise_relation (A → PROP) (pointwise_relation A (≡)) ==>
          (≡) ==> (≡)) bi_least_fixpoint.
Proof. solve_proper. Qed.

Section least.
  Context {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}.

  Lemma least_fixpoint_unfold_2 x : F (bi_least_fixpoint F) x ⊢ bi_least_fixpoint F x.
  Proof using Type*.
    rewrite {2}/bi_least_fixpoint /=. iIntros "HF" (Φ) "#Hincl".
    iApply "Hincl". iApply (bi_mono_pred (bi_least_fixpoint F) Φ with "[#]"); last iApply "HF".
    iIntros "!>" (y) "Hy". iApply ("Hy" with "[# //]").
  Qed.

  Lemma least_fixpoint_unfold_1 x :
    bi_least_fixpoint F x ⊢ F (bi_least_fixpoint F) x.
  Proof using Type*.
    iIntros "HF". iApply ("HF" $! (OfeMor (F (bi_least_fixpoint F))) with "[#]").
    iIntros "!>" (y) "Hy /=". iApply (bi_mono_pred (F (bi_least_fixpoint F)) _ with "[#]"); last iApply "Hy".
    iIntros "!>" (z) "?". by iApply least_fixpoint_unfold_2.
  Qed.

  Corollary least_fixpoint_unfold x :
    bi_least_fixpoint F x ≡ F (bi_least_fixpoint F) x.
  Proof using Type*.
    apply (anti_symm _); auto using least_fixpoint_unfold_1, least_fixpoint_unfold_2.
  Qed.

  Lemma least_fixpoint_ind (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, F Φ y -∗ Φ y) -∗ ∀ x, bi_least_fixpoint F x -∗ Φ x.
  Proof.
    iIntros "#HΦ" (x) "HF". by iApply ("HF" $! (OfeMor Φ) with "[#]").
  Qed.

  Lemma least_fixpoint_strong_ind (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, F (λ x, Φ x ∧ bi_least_fixpoint F x) y -∗ Φ y) -∗
    ∀ x, bi_least_fixpoint F x -∗ Φ x.
  Proof using Type*.
    trans (∀ x, bi_least_fixpoint F x -∗ Φ x ∧ bi_least_fixpoint F x)%I; last first.
    { by setoid_rewrite and_elim_l. }
    iIntros "#HΦ". iApply (least_fixpoint_ind with "[]"); first solve_proper.
    iIntros "!>" (y) "H". iSplit; first by iApply "HΦ".
    iApply least_fixpoint_unfold_2. iApply (bi_mono_pred with "[#] H").
    - solve_proper.
    - by iIntros "!> * [_ ?]".
  Qed.
End least.

Lemma greatest_fixpoint_ne_outer {PROP : bi} {A : ofe}
    (F1 : (A → PROP) → (A → PROP)) (F2 : (A → PROP) → (A → PROP)):
  (∀ Φ x n, F1 Φ x ≡{n}≡ F2 Φ x) → ∀ x1 x2 n,
  x1 ≡{n}≡ x2 → bi_greatest_fixpoint F1 x1 ≡{n}≡ bi_greatest_fixpoint F2 x2.
Proof.
  intros HF x1 x2 n Hx. rewrite /bi_greatest_fixpoint /=.
  do 3 f_equiv; last solve_proper. repeat f_equiv. apply HF.
Qed.

Global Instance greatest_fixpoint_ne' {PROP : bi} {A : ofe} (F: (A → PROP) → (A → PROP)):
  (∀ Φ, NonExpansive Φ → NonExpansive (F Φ)) → NonExpansive (bi_least_fixpoint F).
Proof. solve_proper. Qed.
Global Instance greatest_fixpoint_ne {PROP : bi} {A : ofe} n :
  Proper (pointwise_relation (A → PROP) (pointwise_relation A (dist n)) ==>
          dist n ==> dist n) bi_greatest_fixpoint.
Proof. solve_proper. Qed.
Global Instance greatest_fixpoint_proper {PROP : bi} {A : ofe} :
  Proper (pointwise_relation (A → PROP) (pointwise_relation A (≡)) ==>
          (≡) ==> (≡)) bi_greatest_fixpoint.
Proof. solve_proper. Qed.

Section greatest.
  Context {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}.

  Lemma greatest_fixpoint_unfold_1 x :
    bi_greatest_fixpoint F x ⊢ F (bi_greatest_fixpoint F) x.
  Proof using Type*.
    iDestruct 1 as (Φ) "[#Hincl HΦ]".
    iApply (bi_mono_pred Φ (bi_greatest_fixpoint F) with "[#]").
    - iIntros "!>" (y) "Hy". iExists Φ. auto.
    - by iApply "Hincl".
  Qed.

  Lemma greatest_fixpoint_unfold_2 x :
    F (bi_greatest_fixpoint F) x ⊢ bi_greatest_fixpoint F x.
  Proof using Type*.
    iIntros "HF". iExists (OfeMor (F (bi_greatest_fixpoint F))).
    iSplit; last done. iIntros "!>" (y) "Hy /=". iApply (bi_mono_pred with "[#] Hy").
    iIntros "!>" (z) "?". by iApply greatest_fixpoint_unfold_1.
  Qed.

  Corollary greatest_fixpoint_unfold x :
    bi_greatest_fixpoint F x ≡ F (bi_greatest_fixpoint F) x.
  Proof using Type*.
    apply (anti_symm _); auto using greatest_fixpoint_unfold_1, greatest_fixpoint_unfold_2.
  Qed.

  Lemma greatest_fixpoint_coind (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, Φ y -∗ F Φ y) -∗ ∀ x, Φ x -∗ bi_greatest_fixpoint F x.
  Proof. iIntros "#HΦ" (x) "Hx". iExists (OfeMor Φ). auto. Qed.

  Lemma greatest_fixpoint_strong_coind (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, Φ y -∗ F (λ x, Φ x ∨ bi_greatest_fixpoint F x) y) -∗
    ∀ x, Φ x -∗ bi_greatest_fixpoint F x.
  Proof using Type*.
    trans (∀ x, Φ x ∨ bi_greatest_fixpoint F x -∗ bi_greatest_fixpoint F x)%I; last first.
    { iIntros "H" (x) "Φ". iApply "H". by iLeft. }
    iIntros "#HΦ". iApply (greatest_fixpoint_coind  with "[]"); first solve_proper.
    iIntros "!>" (y) "[H|H]"; first by iApply "HΦ".
    iApply (bi_mono_pred (bi_greatest_fixpoint F) with "[#] [H]"); first solve_proper.
      - iModIntro. iIntros (x) "H". iRight. iApply "H".
      - by iApply greatest_fixpoint_unfold_1.
  Qed.

End greatest.



Instance paco_mono {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F} Φ:
  NonExpansive Φ →
  BiMonoPred (λ (Ψ : A → PROP) (a : A), Φ a ∨ F Ψ a)%I.
Proof.
  split.
  - intros Ψ Ψ' Hne Hne'. iIntros "#Mon" (x) "[H1|H2]"; first by iLeft.
    iRight. iApply (bi_mono_pred with "[] H2"). by iModIntro.
  - iIntros (Ψ Hne). solve_proper.
Qed.

Lemma greatest_fixpoint_paco {PROP : bi} {A : ofe}
    (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F} (Φ : A → PROP) `{!NonExpansive Φ} :
  □ (∀ y, Φ y -∗ F (bi_greatest_fixpoint (λ Ψ a, Φ a ∨ F Ψ a)) y) -∗
  ∀ x, Φ x -∗ bi_greatest_fixpoint F x.
Proof using Type*.
  iIntros "#Hmon" (x) "HΦ". iDestruct ("Hmon" with "HΦ") as "HF".
  rewrite greatest_fixpoint_unfold. iApply (bi_mono_pred with "[] HF").
  iModIntro. iIntros (y) "HG". iApply (greatest_fixpoint_coind with "[] HG").
  iModIntro. iIntros (z) "Hf". rewrite greatest_fixpoint_unfold.
  iDestruct "Hf" as "[HΦ|$]". by iApply "Hmon".
Qed.
