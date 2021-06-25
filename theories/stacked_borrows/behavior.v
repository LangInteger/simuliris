From iris.proofmode Require Import tactics.
From iris.base_logic Require Import iprop.
From iris.prelude Require Import options.

From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import behavior.
From simuliris.stacked_borrows Require Import lang notation parallel_subst wf logical_state.

(* TODO move to std++ *)
Lemma Forall2_cons_iff {A B} (P : A → B → Prop)
  (x : A) (l : list A) (y : B) (k : list B) :
  Forall2 P (x :: l) (y :: k) ↔ P x y ∧ Forall2 P l k.
Proof.
  split.
  - apply Forall2_cons_inv.
  - intros []. by apply Forall2_cons.
Qed.

(** Define "observable behavior" and a generic notion of contextual refinement.
*)
Section ctx_rel.
  Context (expr_head_wf : expr_head → Prop).

  Definition init_state (σ_t σ_s : state) : Prop :=
    σ_t = init_state ∧ σ_s = init_state.

  Definition obs_scalar (sc_t sc_s : scalar) :=
    match sc_t, sc_s with
    | ScPtr l1 t1, ScPtr l2 t2 => True (* the details of locations are not observable *)
    | ScInt z1, ScInt z2 => z1 = z2
    | ScFnPtr f1, ScFnPtr f2 => f1 =f2
    | ScCallId c1, ScCallId c2 => c1 = c2
    | _, ScPoison => True
    | _, _ => False
    end
    .
  Definition obs_value (v_t v_s : value) : Prop := Forall2 obs_scalar v_t v_s.
  Definition obs_result (r_t r_s : val bor_lang) : Prop :=
    match r_t, r_s with
    | PlaceR _ _ _, PlaceR _ _ _ =>
      True (* the details of locations are not observable *)
    | ValR v_t, ValR v_s => obs_value v_t v_s
    | _, _ => False
    end.

  (** The simplang instance of [beh_rel]. *)
  Definition beh_rel := beh_rel init_state "main" (ValR [ScPoison]) obs_result.

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

  Lemma sc_rel_obs `{!sborGS Σ} sc_t sc_s :
    sc_rel sc_t sc_s ⊢@{iPropI Σ} ⌜ obs_scalar sc_t sc_s ⌝.
  Proof.
    destruct sc_t, sc_s; try by eauto.
    rewrite sc_rel_cid_source. iIntros "[<- _]". eauto.
  Qed.

  Lemma rrel_obs `{!sborGS Σ} r_t r_s :
    rrel r_t r_s ⊢@{iPropI Σ} ⌜ obs_result r_t r_s ⌝.
  Proof.
    destruct r_t as [v_t|], r_s as [v_s|]; try by eauto.
    iInduction v_t as [|sc_t scs_t] "IH" forall (v_s);
      destruct v_s as [|sc_s scs_s]; simpl; try eauto.
    { iIntros "_ !%". constructor. }
    rewrite {2}/value_rel big_sepL2_cons.
    iIntros "[Hs Hss]". rewrite /obs_value Forall2_cons_iff. iSplit.
    - iApply (sc_rel_obs with "Hs").
    - iApply ("IH" with "Hss").
  Qed.
End ctx_rel.
