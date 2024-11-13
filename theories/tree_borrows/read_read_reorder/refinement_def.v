From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Import defs lang_base lang notation bor_semantics tree tactics class_instances.
From simuliris.tree_borrows.read_read_reorder Require Import low_level.
From iris.prelude Require Import options.

Fixpoint nsteps P (e : expr) σ e'' σ'' n : Prop := match n with
  0 => e = e'' ∧ σ = σ''
| S n => ∃ e' σ', prim_step P e σ e' σ' nil ∧ nsteps P e' σ' e'' σ'' n end.

(* An extremely simple simulation relation: After n steps, all actions on one side are reproducible in the other *)
Definition identical_states_after P e1 e2 σ n := 
  ∀ e' σ', nsteps P e1 σ e' σ' n → nsteps P e2 σ e' σ' n.

Definition refines_after_nsteps P e1 e2 n :=
  ∀ σ, state_wf σ →
    identical_states_after P e1 e2 σ n ∧
    identical_states_after P e2 e1 σ n.
