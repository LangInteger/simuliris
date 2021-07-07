From iris Require Import bi.bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import lang notation tactics
  proofmode log_rel_structural wf behavior.
From simuliris.simulang.simple_inv Require Export inv.
From iris.prelude Require Import options.

(** Define (very basic) Hoare triple notations *)

Section fix_bi.
 Context `{!sheapGS Σ} `{!sheapInv Σ}.
  Definition hoareSim P e_t e_s π Φ : iProp Σ := □ (P -∗ sim_expr Φ π e_t e_s).
  Definition hoareTgt P e_t Ψ : iProp Σ := □ (P -∗ target_red e_t Ψ).
  Definition hoareSrc P e_s π Ψ : iProp Σ := □ (P -∗ source_red e_s π Ψ).
End fix_bi.

Notation "'{{{'  P  '}}}'  e_t  ⪯[  π  ] e_s   '{{{'  Φ  '}}}'" := (hoareSim P e_t e_s π Φ) (at level 10) : bi_scope.
Notation "'[{{'  P  '}}]'  e_t  '[{{'  Ψ  '}}]t'" := (hoareTgt P e_t Ψ) (at level 20) : bi_scope.
Notation "'[{{'  P  '}}]'  e_s  @  π  '[{{'  Ψ  '}}]s'" := (hoareSrc P e_s π Ψ) (at level 20) : bi_scope.
