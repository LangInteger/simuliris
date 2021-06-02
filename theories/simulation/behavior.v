From stdpp Require Import strings.
From simuliris.simulation Require Import fairness language.

Section beh.
  Context {Λ : language}.

  (** Initial states and program entry point *)
  Variable (I: state Λ → state Λ → Prop).
  Variable (main: string) (u: val Λ).
  (** Observations on final values (of the main thread) *)
  Variable (O: val Λ → val Λ → Prop).

  (** "Behavioral refinement", stated in a constructive way. *)
  Definition beh_rel (p_t p_s: prog Λ) :=
    ∀ σ_t σ_s, I σ_t σ_s ∧ safe p_s (of_call main u) σ_s →
    (* divergent case *)
    (fair_div p_t [of_call main u] σ_t → fair_div p_s [of_call main u] σ_s) ∧
    (* convergent case *)
    (∀ T_t σ_t' I, pool_steps p_t [of_call main u] σ_t I T_t σ_t' →
     ∃ T_s σ_s' J, pool_steps p_s [of_call main u] σ_s J T_s σ_s' ∧
    (∀ i v_t, T_t !! i = Some (of_val v_t) → ∃ v_s, T_s !! i = Some (of_val v_s) ∧ O v_t v_s)) ∧
    (* safety *)
    (safe p_t (of_call main u) σ_t).

  (* TODO: also state the more classical version, and prove them
     equivalent under classical assumptions. *)
End beh.
