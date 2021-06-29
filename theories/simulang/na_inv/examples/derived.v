From iris Require Import bi.bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import lang notation tactics
  proofmode log_rel_structural wf behavior.
From simuliris.simulang.na_inv Require Export inv.
From simuliris.simulang.na_inv Require Import readonly_refl adequacy.
From iris.prelude Require Import options.

(** * Derived stuff we show in the paper *)

Section derived.
  Context `{naGS Σ}.


  Lemma safe_reach_if e1 e2 v : safe_reach (∃ b, v = LitV $ LitBool b) (If (Val v) e1 e2).
  Proof. apply safe_reach_irred. apply _. Qed.
  Lemma safe_reach_div v1 v2 : safe_reach ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n ∧ n ≠ 0%Z))%V (BinOp QuotOp (Val v1) (Val v2)).
  Proof. apply safe_reach_irred. apply _. Qed.
  Lemma safe_reach_load o v_l : safe_reach (∃ l, v_l = LitV $ LitLoc l) (Load o $ Val v_l).
  Proof. apply safe_reach_irred. apply _. Qed.
End derived.
