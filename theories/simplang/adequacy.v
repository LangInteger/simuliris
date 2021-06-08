(** Adequacy of our logical relation: it implies contextual refinement. *)

From simuliris.simulation Require Import slsls lifting behavior.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst heap_bij log_rel heapbij_refl ctx.

Section ctx_rel.

  (* TODO: generalize *)
  Let empty_state : state := {| heap := ∅; used_blocks := ∅ |}.
  Let init_state (σ_t σ_s : state) : Prop := σ_t = empty_state ∧ σ_s = empty_state.

  Fixpoint obs_val (v_t v_s : val) {struct v_s} : Prop :=
    match v_t, v_s with
    | LitV (LitLoc l_t), LitV (LitLoc l_s) =>
      True (* the details of locations are not observable *)
    | LitV l_t, LitV l_s =>
      l_t = l_s
    | PairV v1_t v2_t, PairV v1_s v2_s =>
      obs_val v1_t v1_s ∧ obs_val v2_t v2_s
    | InjLV v_t, InjLV v_s =>
      obs_val v_t v_s
    | InjRV v_t, InjRV v_s =>
      obs_val v_t v_s
    | _,_ => False
    end.

  Let B := beh_rel init_state "main" #() obs_val.

  (** The two [e] can be put into an arbitrary context in an arbitrary function.
      [λ: x, e] denotes an evaluation context [let x = <hole> in e]; then the
      <hole> will be the function argument. *)
  Definition ctx_rel (e_t e_s : expr) :=
    ∀ (C : ctx) (fname x : string) (p : prog),
      ctx_wf C →
      map_Forall (const ectx_wf) p →
      free_vars (fill_ctx C e_t) ∪ free_vars (fill_ctx C e_s) ⊆ {[x]} →
      B (<[fname := (λ: x, fill_ctx C e_t)%E]> p) (<[fname := (λ: x, fill_ctx C e_s)%E]> p).
End ctx_rel.
