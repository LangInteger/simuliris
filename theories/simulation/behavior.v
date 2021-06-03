From stdpp Require Import strings.
From simuliris.simulation Require Import fairness language.

Section beh.
  Context {Λ : language}.

  (** Initial states and program entry point *)
  Variable (I: state Λ → state Λ → Prop).
  Variable (main: string) (u: val Λ).
  (** Observations on final values (of the main thread) *)
  Variable (O: val Λ → val Λ → Prop).

  (** * "Behavioral refinement", stated in a constructive way. *)
  Definition beh_rel (p_t p_s : prog Λ) :=
    ∀ σ_t σ_s, I σ_t σ_s → safe p_s (of_call main u) σ_s →
    (* divergent case *)
    (fair_div p_t [of_call main u] σ_t → fair_div p_s [of_call main u] σ_s) ∧
    (* convergent case *)
    (∀ T_t σ_t' I, pool_steps p_t [of_call main u] σ_t I T_t σ_t' →
      ∃ T_s σ_s' J, pool_steps p_s [of_call main u] σ_s J T_s σ_s' ∧
      (∀ i v_t, T_t !! i = Some (of_val v_t) → ∃ v_s, T_s !! i = Some (of_val v_s) ∧ O v_t v_s)) ∧
    (* safety *)
    (safe p_t (of_call main u) σ_t).

  (** * A more classical definition of 'behavioral refinement', equivalent to the
      above. *)

  (** First we define the possible "behaviors" of a program, and which behaviors
      we consider observably related (lifting O to behaviors). *)
  Inductive beh := BehReturn (v : val Λ) | BehDiverge | BehUndefined.
  Inductive obs_beh : beh → beh → Prop :=
  | ObsBehVal (v_t v_s : val Λ) :
    O v_t v_s → obs_beh (BehReturn v_t) (BehReturn v_s)
  | ObsBehDiv :
    obs_beh BehDiverge BehDiverge
  | ObsBehUndefined b :
    obs_beh b BehUndefined.

  (** Next we define when a threadpool has a certain behavior. *)
  Inductive has_beh (p : prog Λ) : tpool Λ → state Λ → beh → Prop :=
  | HasBehStuck T σ :
    stuck_pool p T σ → has_beh p T σ BehUndefined
  | HasBehDiv T σ :
    fair_div p T σ → has_beh p T σ BehDiverge
  | HasBehRet v T σ :
      has_beh p (of_val v :: T) σ (BehReturn v)
  | HasBehStep T σ i T' σ' b :
      has_beh p T' σ' b →
      pool_step p T σ i T' σ' →
      has_beh p T σ b.
  (* FIXME: The first definition talks about all threads that happen to converge,
     the second definition only about the main thread. *)

  (** Finally, we can apply that to the relevant initial states. *)
  Definition beh_rel_alt (p_t p_s : prog Λ) :=
    ∀ σ_t σ_s b_t,
      I σ_t σ_s →
      has_beh p_t [of_call main u] σ_t b_t →
      ∃ b_s, has_beh p_s [of_call main u] σ_s b_s ∧ obs_beh b_t b_s.

  (* TODO: prove them equivalent under classical assumptions. *)
End beh.
