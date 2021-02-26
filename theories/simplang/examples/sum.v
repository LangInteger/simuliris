From simuliris.simplang Require Import lang notation tactics class_instances proofmode.
From iris Require Import bi.bi.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.



Section fix_bi.
Context (PROP : bi).
Context {PROP_bupd : BiBUpd PROP}.
Context {PROP_forall : BiPureForall PROP}.
Context {PROP_affine : BiAffine PROP}.

(* Sums are encoded as injL x -> (1, x); injR x -> (2, x); the tag encodes the constructor.  *)

Definition inj1_enc : val := (λ: "x", (#1, "x"))%V.
Definition inj2_enc : val := (λ: "x", (#2, "x"))%V.

Definition diverge : val := (rec: "f" "x" := "f" "x")%V.

(* on invalid inputs, we diverge: in the source we get stuck, so any target behaviour is okay *)
Definition case_enc : val :=
  (λ: "x" "f" "g",
      if: Fst "x" = #1 then "f" (Snd "x")
      else if: Fst "x" = #2
        then "g" (Snd "x")
        else diverge #()
  ).

Definition case_prim : val :=
  (λ: "x" "f" "g",
    match: "x" with
      InjL "x" => "f" "x"
    | InjR "x" => "g" "x"
    end)%V.

(** the value relation determining which values can be passed to a function *)
Inductive val_rel_pure : val → val → Prop :=
  (* functions are never related *)
  | val_rel_lit l : val_rel_pure (LitV l) (LitV l)
  | val_rel_injL v1 v2 : val_rel_pure v1 v2 → val_rel_pure ((#1, v1)%V) (InjLV v2)
  | val_rel_injR v1 v2 : val_rel_pure v1 v2 → val_rel_pure ((#2, v1)%V) (InjRV v2)
  | val_rel_pair v1 v2 v1' v2' :
      val_rel_pure v1 v1' →
      val_rel_pure v2 v2' →
      val_rel_pure ((v1, v2)%V) ((v1', v2')%V).
Local Hint Constructors val_rel_pure : core.
Definition val_rel_simp v1 v2 : PROP := (⌜val_rel_pure v1 v2⌝)%I.

(* TODO: make a Record ? *)
Instance sim_sum_lang : SimulLang PROP simp_lang :=
  {|
    (* TODO *)
    state_interp Pt σt Ps σs := True%I;
    val_rel := val_rel_simp (* TODO: remove *)
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

Lemma sim_source_case e_t e_s1 e_s2 Φ v_s :
  ⊢ (∀ v_s', ⌜v_s = InjLV v_s'⌝ -∗ e_t ⪯ Case (Val v_s) e_s1 e_s2 {{ Φ }}) -∗
    (∀ v_s', ⌜v_s = InjRV v_s'⌝ -∗ e_t ⪯ Case (Val v_s) e_s1 e_s2 {{ Φ }}) -∗
    e_t ⪯ Case (Val v_s) e_s1 e_s2 {{ Φ }}.
Proof.
  iIntros "Hvl Hvr".
  destruct v_s as [ l | | v1 v2 | v1 | v2 ].
  - iApply source_stuck_sim. source_stuck_prim.
  - iApply source_stuck_sim. source_stuck_prim.
  - iApply source_stuck_sim. source_stuck_prim.
  - by iApply "Hvl".
  - by iApply "Hvr".
Qed.

Lemma mul2_sim:
  ⊢ ∀ v_t v_s, val_rel v_t v_s -∗
    mul2_target (of_val v_t) ⪯ mul2_source (of_val v_s) {{ λ v_t' v_s', val_rel v_t' v_s' }}.
Proof.
  iIntros (?? Hval). rewrite /mul2_target /mul2_source.
  sim_pures.
  rewrite /case_enc /case_prim.
  sim_pures.
  iApply sim_source_case.
  - iIntros (v_s') "->". inversion Hval; subst.
    sim_pures. destruct H1.
    { destruct l. { sim_pures. sim_pures_target. iModIntro. iPureIntro. constructor. }
      all: iApply source_stuck_sim; source_stuck_prim.
    }
    all: iApply source_stuck_sim; source_stuck_prim.
  - iIntros (v_t') "->". inversion Hval; subst.
    sim_pures. sim_pures_target. destruct H1.
    { destruct l. { sim_pures. iModIntro. iPureIntro. constructor. }
      all: iApply source_stuck_sim; source_stuck_prim.
    }
    all: iApply source_stuck_sim; source_stuck_prim.
Qed.


(* TODO move *)
Lemma step_call e_t e_s (v_t v_s : val) f :
  to_val e_t = Some v_t → to_val e_s = Some v_s →
  ⊢ val_rel v_t v_s -∗ Call (of_fname f) e_t ⪯ Call (of_fname f) e_s {{ val_rel }}.
Proof.
  intros <-%of_to_val <-%of_to_val.
  iIntros "H". rewrite sim_unfold. iIntros (????) "[H1 H2]". iModIntro.
  iRight; iRight. iExists f, empty_ectx, v_t, empty_ectx, v_s, σ_s. cbn. iFrame.
  iSplitR; first done. iSplitR. { iPureIntro. constructor. }
  iIntros (v_t' v_s' ) "H". iApply sim_value. iApply "H".
Qed.

Definition source_client := (λ: "x", Call (of_fname "mul2") (InjL "x"))%V.
Definition target_client := (λ: "x", Call (of_fname "mul2") (inj1_enc "x"))%V.

Lemma client_sim (n : Z) :
  ⊢ target_client #n ⪯ source_client #n {{ λ v_t v_s, val_rel v_t v_s }}.
Proof.
  iStartProof. rewrite /target_client /source_client.
  sim_pures. sim_bind (inj1_enc #n) (InjL #n).
  rewrite /inj1_enc.
  sim_pures. sim_pures_target.
  iApply step_call; eauto.
Qed.
