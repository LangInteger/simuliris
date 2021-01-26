From stdpp Require Import prelude relations.

(* TODO: upstream *)
(* This file contains various abstract results about
   relations/state transition systems. *)

Lemma rtc_inv_tc {X} (R: relation X) x y:
  rtc R x y → x = y ∨ tc R x y.
Proof.
  destruct 1; eauto using tc_rtc_r, tc_once.
Qed.


Lemma ex_loop_inv {X: Type} (R: relation X) x:
  ex_loop R x →
  ∃ x', R x x' ∧ ex_loop R x'.
Proof.
  inversion 1; eauto.
Qed.

Lemma ex_loop_pair_inv {X Y: Type} (R: relation (X * Y)) x y:
  ex_loop R (x, y) →
  ∃ x' y', R (x, y) (x', y') ∧ ex_loop R (x', y').
Proof.
  intros [[] ?] % ex_loop_inv; eauto.
Qed.

Lemma ex_loop_tc {X: Type} (R: relation X) (x: X):
  ex_loop (tc R) x → ex_loop R x.
Proof.
  revert x; cofix IH.
  intros x (y & Hstep & Hloop') % ex_loop_inv.
  destruct Hstep as [x y Hstep|x y z Hstep Hsteps].
  - econstructor; eauto.
  - econstructor; [by eauto|].
    eapply IH; econstructor; eauto.
Qed.

Lemma rtc_pair_ind {A B: Type} (R : relation (A * B)) (P : A → B → A → B → Prop) x y x' y':
  (∀ x y, P x y x y) →
  (∀ x y x' y' x'' y'', R (x, y) (x', y') → rtc R (x', y') (x'', y'') → P x' y' x'' y'' → P x y x'' y'') →
  rtc R (x, y) (x', y') → P x y x' y'.
Proof.
  intros Base IH Hrtc. remember (x, y) as p. remember (x', y') as p'.
  revert x x' y y' Heqp Heqp'. induction Hrtc as [[]|[] [] []]; naive_solver.
Qed.

Lemma tc_pair_ind {A B: Type} (R : relation (A * B)) (P : A → B → A → B → Prop):
  (∀ x y x' y', R (x, y) (x', y') → P x y x' y') →
  (∀ x y x' y' x'' y'', R (x, y) (x', y') → tc R (x', y') (x'', y'') → P x' y' x'' y'' → P x y x'' y'') →
  ∀ x y x' y', tc R (x, y) (x', y') → P x y x' y'.
Proof.
  intros Base IH x y x' y' Htc. remember (x, y) as p. remember (x', y') as p'.
  revert x x' y y' Heqp Heqp'. induction Htc as [[] []|[] [] []]; naive_solver.
Qed.


