From simuliris.simplang Require Import lang notation tactics class_instances proofmode.
From iris Require Import bi.bi.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting. 



Section fix_bi.
Context (PROP : bi).
Context {PROP_bupd : BiBUpd PROP}.
Context {PROP_affine : BiAffine PROP}.

(* Sums are encoded as inj1 x -> (1, (1, x)); inj2 x -> (1, (2, x));
  the first tag encodes that this is a sum, the second tag the constructor.
  Pairs are now also tagged to force interpretation as a pair (instead of sum).
  (x, y) becomes (0, (x, y)).
 *)

Definition inj1_enc : val := (LamV "x" (#1, (#1, "x"))).
Definition inj2_enc : val := (LamV "x" (#1, (#2, "x"))).

Definition diverge : val := (rec: "f" "x" := "f" "x")%V.

(* on invalid inputs, we diverge: in the source we get stuck, so any target behaviour is okay *)
Definition case_enc : val :=
  (λ: "x" "f" "g", if: Fst "x" = #1 then
    if: Fst "x" = #1 then "f" (Snd "x")
      else if: Fst "x" = #2
        then "g" (Snd "x")
        else diverge #()
    else diverge #()
  ).

Definition case_prim : val :=
  (λ: "x" "f" "g",
    match: "x" with
      InjL "x" => "f" "x"
    | InjR "x" => "g" "x"
    end).

(** the value relation determining which values can be passed to a function *)
Inductive val_rel_pure : val → val → Prop :=
  (* functions are never related *)
  | val_rel_lit l : val_rel_pure (LitV l) (LitV l)
  | val_rel_injL v1 v2 : val_rel_pure v1 v2 → val_rel_pure ((#1, (#1, v1))%V) (InjLV v2)
  | val_rel_injR v1 v2 : val_rel_pure v1 v2 → val_rel_pure ((#1, (#2, v1))%V) (InjRV v2)
  | val_rel_pair v1 v2 v1' v2' :
      val_rel_pure v1 v1' →
      val_rel_pure v2 v2' →
      val_rel_pure ((#0, (v1, v2))%V) ((v1', v2')%V).
Definition val_rel_simp v1 v2 : PROP := (⌜val_rel_pure v1 v2⌝)%I.

Instance sim_sum_lang : simul_lang PROP simp_lang :=
  {|
    (* TODO *)
    state_interp Pt σt Ps σs := ⌜ True ⌝%I;
    val_rel := val_rel_simp
  |}.
Instance: Sim sim_sum_lang := sim_stutter.


Definition mul2_source :=
  (λ: "x", case_prim "x" (λ: "x", "x" * #2) (λ: "x", "x" + #2))%V.
Definition mul2_target :=
  (λ: "x", case_enc "x" (λ: "x", "x" * #2) (λ: "x", "x" + #2))%V.

Definition fun_to_ectx (v : val) := [AppRCtx v].

Definition source_prog : gmap string ectx := {[ "mul2" := fun_to_ectx mul2_source]}.
Definition target_prog : gmap string ectx := {[ "mul2" := fun_to_ectx mul2_target]}.

(** We want to prove: *)

Lemma mul2_sim:
  ⊢ ∀ v_t v_s, val_rel v_t v_s -∗
    mul2_target (of_val v_t) ⪯ mul2_source (of_val v_s) {{λ v_t' v_s', val_rel v_t' v_s' }}.
Proof.
Admitted.


(* TODO move *)
Lemma step_Call e_t e_s (v_t v_s : val) f :
  to_val e_t = Some v_t → to_val e_s = Some v_s → 
  ⊢ val_rel v_t v_s -∗ Call f e_t ⪯ Call f e_s {{val_rel}}.
Proof.
  intros <-%of_to_val <-%of_to_val. 
  iIntros "H". rewrite sim_unfold. iIntros (????) "[H1 H2]". iModIntro.
  iRight; iRight. iExists f, empty_ectx, v_t, empty_ectx, v_s, σ_s. cbn. iFrame.
  iSplitL ""; first done. iSplitL "". { iPureIntro. constructor. }
  iIntros (v_t' v_s' ) "H". iApply sim_value. iApply "H".
Qed.

Definition source_client := (λ: "x", Call "mul2" (InjL "x"))%V.
Definition target_client := (λ: "x", Call "mul2" (inj1_enc "x"))%V.

Lemma client_sim (n : Z) :
  ⊢ target_client #n ⪯ source_client #n {{λ v_t v_s, val_rel v_t v_s }}.
Proof.
  iStartProof. rewrite /target_client /source_client.
  iApply sim_pure_steps; eauto. cbn. 
  sim_expr_simpl. 
  (* TODO: bind and further reduce target *)
  (* TODO: fix handling of values. to_val (InjL ..) should go to InjLV .. ? *)
  iApply step_Call. cbn. 

Admitted.

