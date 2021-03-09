From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From simuliris.simulation Require Import slsls lifting language.
From simuliris.simplang Require Import tactics class_instances notation.
From iris.prelude Require Import options.

(*|
This is a heavily stripped-down version of HeapLang's proofmode support. To make any program proofs reasonable we do need to implement `wp_pure` and `wp_bind`, and as a demo of the implementation we also implement `wp_load` in the reflective style typical in the IPM. `wp_pure` is the basis for a number of tactics like `wp_rec` and `wp_let` and such, while `wp_bind` is what powers `wp_apply`.
|*)

Section sim.
Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
Context {s : SimulLang PROP simp_lang}.
Instance: Sim s := (sim_stutter (s := s)).
Context (Ω : val → val → PROP).
Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{Ω} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope. 

Lemma tac_sim_expr_eval Δ Φ e_t e_t' e_s e_s' :
  (∀ (e_t'':=e_t'), e_t = e_t'') →
  (∀ (e_s'':=e_s'), e_s = e_s'') →
  envs_entails Δ (e_t' ⪯ e_s' {{ Φ }}) → envs_entails Δ (e_t ⪯ e_s {{ Φ }}).
Proof. by intros -> ->. Qed.

Lemma tac_sim_pure_target Δ n e_t e_t' e_s K_t Φ (ϕ : Prop):
  PureExec ϕ n (e_t) (e_t') →
  ϕ →
  envs_entails Δ ((fill K_t e_t') ⪯ e_s {{Φ}}) →
  envs_entails Δ ((fill K_t e_t) ⪯ e_s {{Φ}}).
Proof.
  intros ? ?. rewrite envs_entails_eq.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_ctx.
  rewrite sim_pure_step_target //.
Qed.

Lemma tac_sim_pure_source Δ n e_s e_s' e_t K_s Φ (ϕ : Prop):
  PureExec ϕ n e_s e_s' →
  ϕ →
  envs_entails Δ (e_t ⪯ (fill K_s e_s') {{Φ}}) →
  envs_entails Δ (e_t ⪯ (fill K_s e_s) {{Φ}}).
Proof. 
  intros ? ?. rewrite envs_entails_eq.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_ctx.
  rewrite sim_pure_step_source //.
Qed.

Lemma tac_sim_value v_t v_s Φ Δ:
  envs_entails Δ (|==> Φ v_t v_s) → envs_entails Δ (Val v_t ⪯ Val v_s {{ Φ }}).
Proof.
  rewrite envs_entails_eq => ->. iIntros "H". iApply sim_bupd. by iApply sim_value.
Qed.

Lemma tac_sim_value_no_bupd v_t v_s Φ Δ:
  envs_entails Δ (Φ v_t v_s) → envs_entails Δ (Val v_t ⪯ Val v_s {{ Φ }}).
Proof. rewrite envs_entails_eq => ->. by iApply sim_value. Qed.

Lemma tac_sim_bind K_t K_s Δ Φ e_t f_t e_s f_s:
  f_t = (λ e_t, fill K_t e_t) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  f_s = (λ e_s, fill K_s e_s) →
  envs_entails Δ (e_t ⪯ e_s {{ λ v_t v_s, f_t (Val v_t) ⪯ f_s (Val v_s) {{ Φ }} }})%I →
  envs_entails Δ (fill K_t e_t ⪯ fill K_s e_s {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> -> ->. intros H.
  iIntros "H". iApply (sim_bind Ω e_t e_s K_t K_s Φ). by iApply H.
Qed.
End sim.

Tactic Notation "sim_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim ?Ω ?e_t ?e_s ?Φ) =>
    notypeclasses refine (tac_sim_expr_eval Ω _ _ e_t _ e_s _ _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl | ]
  | _ => fail "sim_expr_eval: not a 'sim"
  end.
Ltac sim_expr_simpl := sim_expr_eval simpl.

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).


(** Simplify the goal if it is [sim] of a value.
  If the postcondition already allows a bupd, do not add a second one.
  But otherwise, *do* add a bupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac sim_value_head :=
  lazymatch goal with
  | |- envs_entails _ (sim _ (Val _) (Val _) (λ _ _, bupd _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim _ (Val _) (Val _) (λ _ _, sim _ _ _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim _ (Val _) (Val _) _) =>
      eapply tac_sim_value
  end.

Ltac sim_finish :=
  sim_expr_simpl;      (* simplify occurences of subst/fill *)
  try sim_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify λs caused by wp_value *)

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "sim_pure_target" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim ?Ω ?e_t ?e_s ?Q) =>
    let e_t := eval simpl in e_t in
    reshape_expr e_t ltac:(fun K_t e_t' =>
      unify e_t' efoc;
      eapply (tac_sim_pure_target Ω _ _ e_t' _ _ K_t _ _);
      [ iSolveTC                       (* PureExec *)
      | try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      | sim_finish                      (* new goal *)
      ])
    || fail "sim_pure_target: cannot find" efoc "in" e_t "or" efoc "is not a redex"
  | _ => fail "sim_pure_target: not a 'sim'"
  end.

Tactic Notation "sim_pure_source" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim ?Ω ?e_t ?e_s ?Q) =>
    let e_s := eval simpl in e_s in
    reshape_expr e_s ltac:(fun K_s e_s' =>
      unify e_s' efoc;
      eapply (tac_sim_pure_source Ω _ _ e_s' _ _ K_s _ _);
      [ iSolveTC                       (* PureExec *)
      | try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      | sim_finish                      (* new goal *)
      ])
    || fail "sim_pure_source: cannot find" efoc "in" e_s "or" efoc "is not a redex"
  | _ => fail "sim_pure_source: not a 'sim'"
  end.

Ltac sim_pures_target :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (sim_pure_target _; [])
        | sim_finish (* In case sim_pure_target never ran, make sure we do the usual cleanup. *)
        ].

Ltac sim_pures_source :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (sim_pure_source _; [])
        | sim_finish (* In case sim_pure_target never ran, make sure we do the usual cleanup. *)
        ].

Ltac sim_pures := (try sim_pures_target); (try sim_pures_source).


Ltac sim_bind_core K_t K_s :=
  lazymatch eval hnf in K_t with
  | [] => lazymatch eval hnf in K_s with
          | [] => idtac
          | _ => eapply (tac_sim_bind _ K_t K_s); [simpl; reflexivity| simpl; reflexivity | ]
          end
  | _ => eapply (tac_sim_bind _ K_t K_s); [simpl; reflexivity| simpl; reflexivity | ]
  end.

Tactic Notation "sim_bind" open_constr(efoc_t) open_constr(efoc_s) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim ?Ω ?e_t ?e_s ?Q) =>
    first [ reshape_expr e_t ltac:(fun K_t e_t' => unify e_t' efoc_t;
                                    first [ reshape_expr e_s ltac:(fun K_s e_s' => unify e_s' efoc_s; sim_bind_core K_t K_s)
                                           (* TODO: fix error handling *)
                                           | fail 1 "sim_bind: cannot find" efoc_s "in" e_s]
                                  )
          | fail 1 "sim_bind: cannot find" efoc_t "in" e_t ]
  | _ => fail "sim_bind: not a 'sim"
  end.



(** ** Automation related to stuckness *)

(* FIXME: currently quote tailored to the sideconditions generated by the instances we already have.
  Maybe we can make this more general? *)
Ltac source_stuck_sidecond :=
  intros;
  match goal with
  | |- ¬ _ => intros ?
  end;
  repeat match goal with
         | H : _ ∨ _ |- _ => destruct H
         | H : ∃ _, _ |- _ => destruct H
         | H : is_Some _ |- _ => destruct H
         end;
  unfold bin_op_eval, un_op_eval in *;
  simpl in *;
  congruence.

Ltac source_stuck_prim :=
  iApply source_stuck_prim; [ source_stuck_sidecond | reflexivity].

