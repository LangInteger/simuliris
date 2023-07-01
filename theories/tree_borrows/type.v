(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From Coq Require Import Program ssreflect.
From stdpp Require Export list countable.
From simuliris.tree_borrows Require Export helpers.
From iris.prelude Require Import options.

Inductive pinedness := Pin | Unpin.
Inductive freeze := Freeze | Interiormut.
Inductive mutability := Mutable | Immutable.
Inductive pointer_kind := BoxPtr | RawPtr | RefPtr (mut:mutability) (frz:freeze) (pin:pinedness).
Inductive pointer := Ptr (ptrk:pointer_kind) (sz:nat).

Definition sizeof '(Ptr _ sz) := sz.
Definition kindof '(Ptr pk _) := pk.

(** Decidability *)

Global Instance mutability_eq_dec : EqDecision mutability.
Proof. solve_decision. Defined.
Global Instance mutability_countable : Countable mutability.
Proof.
  refine (inj_countable'
    (λ m, match m with Mutable => 0 | Immutable => 1 end)
    (λ x, match x with 0 => Mutable | _ => Immutable end) _); by intros [].
Qed.

Global Instance freeze_eq_dec : EqDecision freeze.
Proof. solve_decision. Defined.
Global Instance freeze_countable : Countable freeze.
Proof.
  refine (inj_countable'
    (λ f, match f with Freeze => 0 | Interiormut => 1 end)
    (λ x, match x with 0 => Freeze | _ => Interiormut end) _); by intros [].
Qed.

Global Instance pinedness_eq_dec : EqDecision pinedness.
Proof. solve_decision. Defined.
Global Instance pinedness_countable : Countable pinedness.
Proof.
  refine (inj_countable'
    (λ p, match p with Pin => 0 | Unpin => 1 end)
    (λ x, match x with 0 => Pin | _ => Unpin end) _); by intros [].
Qed.

Global Instance pointer_kind_eq_dec : EqDecision pointer_kind.
Proof. solve_decision. Defined.
Global Instance pointer_kind_countable : Countable pointer_kind.
Proof.
  refine (inj_countable
          (λ k, match k with
              | RefPtr mut frz pin => inl (mut, frz, pin)
              | RawPtr => inr true
              | BoxPtr => inr false
              end)
          (λ s, match s with
              | inl (mut, frz, pin) => Some $ RefPtr mut frz pin
              | inr true => Some RawPtr
              | inr false => Some BoxPtr
              end) _); by intros [].
Qed.

Global Instance pointer_eq_dec : EqDecision pointer.
Proof. solve_decision. Defined.
Global Instance pointer_countable : Countable pointer.
Proof.
  refine (inj_countable
    (λ '(Ptr pk sz), (pk, sz))
    (λ '(pk, sz), Some $ Ptr pk sz) _); by intros [].
Qed.
