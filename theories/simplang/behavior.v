From iris.proofmode Require Import tactics.
From iris.base_logic Require Import iprop.

From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import behavior.
From simuliris.simplang Require Import lang notation parallel_subst wf gen_val_rel.

(** Define "observable behavior" and a generic notion of contextual refinement.
*)
Section ctx_rel.
  Context (expr_head_wf : expr_head → Prop).

  (* TODO: generalize *)
  Let init_state (σ_t σ_s : state) : Prop := σ_t = state_empty ∧ σ_s = state_empty.

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

  (** The simplang instance of [beh_rel]. *)
  Definition beh_rel := beh_rel init_state "main" #() obs_val.

  (** Contextual refinement:
      The two [e] can be put into an arbitrary context in an arbitrary function.
      [λ: x, e] denotes an evaluation context [let x = <hole> in e]; then the
      <hole> will be the function argument. *)
  Definition gen_ctx_rel (e_t e_s : expr) :=
    ∀ (C : ctx) (fname x : string) (p : prog),
      map_Forall (λ _ K, gen_ectx_wf expr_head_wf K ∧ free_vars_ectx K = ∅) p →
      gen_ctx_wf expr_head_wf C →
      free_vars (fill_ctx C e_t) ∪ free_vars (fill_ctx C e_s) ⊆ {[x]} →
      beh_rel (<[fname := (λ: x, fill_ctx C e_t)%E]> p) (<[fname := (λ: x, fill_ctx C e_s)%E]> p).

  Lemma gen_val_rel_obs {Σ} loc_rel v_t v_s :
    gen_val_rel loc_rel v_t v_s ⊢@{iPropI Σ} ⌜obs_val v_t v_s⌝.
  Proof.
    iInduction v_t as [[| | | | |]| | |] "IH" forall (v_s);
      destruct v_s as [[| | | | |]| | |]; try by eauto.
    - simpl. iIntros "[Hv1 Hv2]". iSplit.
      + by iApply "IH".
      + by iApply "IH1".
  Qed.
End ctx_rel.
