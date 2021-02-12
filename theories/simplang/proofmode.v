From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From simuliris.simplang Require Import tactics class_instances notation.
From simuliris.simulation Require Import slsls. 
From iris.prelude Require Import options.

(*|
This is a heavily stripped-down version of HeapLang's proofmode support. To make any program proofs reasonable we do need to implement `wp_pure` and `wp_bind`, and as a demo of the implementation we also implement `wp_load` in the reflective style typical in the IPM. `wp_pure` is the basis for a number of tactics like `wp_rec` and `wp_let` and such, while `wp_bind` is what powers `wp_apply`.
|*)

Section sim.
Context {PROP : bi} {PROP_bupd : BiBUpd PROP} {PROP_affine : BiAffine PROP}. 
Context {Λ : language} {s : simul_lang PROP Λ}.
Instance: Sim s := (sim_stutter (s := s)).

Lemma tac_sim_expr_eval Δ Φ e_t e_t' e_s e_s' :
  (∀ (e_t'':=e_t'), e_t = e_t'') →
  (∀ (e_s'':=e_s'), e_s = e_s'') →
  envs_entails Δ (e_t' ⪯ e_s' {{ Φ }}) → envs_entails Δ (e_t ⪯ e_s {{ Φ }}).
Proof. by intros -> ->. Qed.

End sim. 

Tactic Notation "sim_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim ?e_t ?e_s ?Φ) =>
    notypeclasses refine (tac_sim_expr_eval _ _ e_t _ e_s _ _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl | ]
  | _ => fail "sim_expr_eval: not a 'sim"
  end.
Ltac sim_expr_simpl := sim_expr_eval simpl.

(* TODO *)
