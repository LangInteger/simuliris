From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From simuliris.simulation Require Import slsls lifting language.
From simuliris.simplang Require Import tactics class_instances.
From simuliris.simplang Require Export notation primitive_laws derived.
From iris.bi Require Import bi.
Import bi.
From iris.bi Require Import derived_laws.
Import bi.
From iris.prelude Require Import options.


Section sim.
Context `{!sheapG Σ} `{sheapInv Σ}.
Context (Ω : val → val → iProp Σ).
Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{Ω} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.
Local Notation "et '⪯' es [{ Φ }]" := (et ⪯{Ω} es [{Φ}])%I (at level 40, Φ at level 200) : bi_scope.

Lemma tac_sim_expr_eval Δ Φ e_t e_t' e_s e_s' :
  (∀ (e_t'':=e_t'), e_t = e_t'') →
  (∀ (e_s'':=e_s'), e_s = e_s'') →
  envs_entails Δ (e_t' ⪯ e_s' [{ Φ }]) → envs_entails Δ (e_t ⪯ e_s [{ Φ }]).
Proof. by intros -> ->. Qed.

Lemma tac_target_red_expr_eval Δ Ψ e_t e_t' :
  (∀ (e_t'':=e_t'), e_t = e_t'') →
  envs_entails Δ (target_red e_t' Ψ : iProp Σ) →
  envs_entails Δ (target_red e_t Ψ).
Proof. by intros ->. Qed.

Lemma tac_source_red_expr_eval Δ Ψ e_s e_s' :
  (∀ (e_s'':=e_s'), e_s = e_s'') →
  envs_entails Δ (source_red e_s' Ψ : iProp Σ) →
  envs_entails Δ (source_red e_s Ψ).
Proof. by intros ->. Qed.

Lemma tac_target_red_pure Δ n e_t e_t' K_t Ψ (ϕ : Prop):
  PureExec ϕ n (e_t) (e_t') →
  ϕ →
  envs_entails Δ (target_red (fill K_t e_t') Ψ : iProp Σ) →
  envs_entails Δ (target_red (fill K_t e_t) Ψ).
Proof.
  intros ? ?. rewrite envs_entails_eq.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_ctx.
  rewrite target_red_lift_pure //.
Qed.

Lemma tac_source_red_pure Δ n e_s e_s' K_s Ψ (ϕ : Prop):
  PureExec ϕ n e_s e_s' →
  ϕ →
  envs_entails Δ (source_red (fill K_s e_s') Ψ : iProp Σ) →
  envs_entails Δ (source_red (fill K_s e_s) Ψ).
Proof.
  intros ? ?. rewrite envs_entails_eq.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_ctx.
  rewrite source_red_lift_pure //.
Qed.

Lemma tac_target_red_base e_t Ψ Δ :
  envs_entails Δ (|==> Ψ e_t : iProp Σ) → envs_entails Δ (target_red e_t Ψ).
Proof.
  rewrite envs_entails_eq => ->. iIntros "H". by iApply target_red_base.
Qed.
Lemma tac_target_red_base_no_bupd e_t Ψ Δ :
  envs_entails Δ (Ψ e_t : iProp Σ) → envs_entails Δ (target_red e_t Ψ).
Proof.
  rewrite envs_entails_eq => ->. iIntros "H". by iApply target_red_base.
Qed.

Lemma tac_source_red_base e_s Ψ Δ :
  envs_entails Δ (|==> Ψ e_s : iProp Σ) → envs_entails Δ (source_red e_s Ψ).
Proof.
  rewrite envs_entails_eq => ->. by iApply source_red_base.
Qed.
Lemma tac_source_red_base_no_bupd e_s Ψ Δ :
  envs_entails Δ (Ψ e_s : iProp Σ) → envs_entails Δ (source_red e_s Ψ).
Proof.
  rewrite envs_entails_eq => ->. iIntros "H". by iApply source_red_base.
Qed.

Lemma tac_sim_value v_t v_s Φ Δ :
  envs_entails Δ (|==> Φ v_t v_s) → envs_entails Δ (Val v_t ⪯ Val v_s {{ Φ }}).
Proof.
  rewrite envs_entails_eq => ->. iIntros "H". iApply sim_bupd. by iApply sim_value.
Qed.

Lemma tac_sim_value_no_bupd v_t v_s Φ Δ :
  envs_entails Δ (Φ v_t v_s) → envs_entails Δ (Val v_t ⪯ Val v_s {{ Φ }}).
Proof. rewrite envs_entails_eq => ->. by iApply sim_value. Qed.

Lemma tac_sim_bind K_t K_s Δ Φ e_t f_t e_s f_s :
  f_t = (λ e_t, fill K_t e_t) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  f_s = (λ e_s, fill K_s e_s) →
  envs_entails Δ (e_t ⪯ e_s {{ λ e_t' e_s', f_t e_t' ⪯ f_s e_s' [{ Φ }] }})%I →
  envs_entails Δ (fill K_t e_t ⪯ fill K_s e_s [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> -> ->. intros Hs.
  iIntros "H". iApply (sim_bind Ω e_t e_s K_t K_s Φ). by iApply Hs.
Qed.

Lemma tac_target_red_bind K_t e_t f_t Ψ Δ :
  f_t = (λ e_t, fill K_t e_t) →
  envs_entails Δ (target_red e_t (λ e_t', target_red (f_t e_t') Ψ) : iProp Σ) →
  envs_entails Δ (target_red (fill K_t e_t) Ψ).
Proof.
  rewrite envs_entails_eq=> ->. intros Hs.
  iIntros "H". iApply target_red_bind. by iApply Hs.
Qed.

Lemma tac_source_red_bind K_s e_s f_s Ψ Δ :
  f_s = (λ e_s, fill K_s e_s) →
  envs_entails Δ (source_red e_s (λ e_s', source_red (f_s e_s') Ψ) : iProp Σ) →
  envs_entails Δ (source_red (fill K_s e_s) Ψ).
Proof.
  rewrite envs_entails_eq=> ->. intros Hs.
  iIntros "H". iApply source_red_bind. by iApply Hs.
Qed.

Lemma tac_target_red_allocN n v j K Ψ Δ :
  (0 < n)%Z →
  (∀ l,
    match envs_app false (Esnoc Enil j (array (hG:=gen_heap_inG_target) l (DfracOwn 1) (replicate (Z.to_nat n) v))) Δ with
    | Some Δ' =>
       envs_entails Δ' (target_red (fill K (Val $ LitV $ LitLoc l)) Ψ)
    | None => False
    end) →
  envs_entails Δ (target_red (fill K (AllocN (Val $ LitV $ LitInt n) (Val v))) Ψ).
Proof.
  rewrite envs_entails_eq=> ? HΔ. iIntros "He".
  iApply target_red_bind. iApply (target_red_allocN); [done..| ].
  iIntros (l) "Hl". specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  iApply target_red_base. iModIntro. iApply HΔ.
  rewrite envs_app_sound //; simpl. iApply "He"; eauto.
Qed.

Lemma tac_source_red_allocN n v j K Ψ Δ :
  (0 < n)%Z →
  (∀ l,
    match envs_app false (Esnoc Enil j (array (hG:=gen_heap_inG_source) l (DfracOwn 1) (replicate (Z.to_nat n) v))) Δ with
    | Some Δ' =>
       envs_entails Δ' (source_red (fill K (Val $ LitV $ LitLoc l)) Ψ)
    | None => False
    end) →
  envs_entails Δ (source_red (fill K (AllocN (Val $ LitV $ LitInt n) (Val v))) Ψ).
Proof.
  rewrite envs_entails_eq=> ? HΔ. iIntros "He".
  iApply source_red_bind. iApply source_red_allocN; [done..| ].
  iIntros (l) "Hl". specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  iApply source_red_base. iModIntro.
  iApply HΔ. rewrite envs_app_sound //; simpl. iApply "He"; eauto.
Qed.

Lemma tac_target_red_alloc v j K Ψ Δ :
  (∀ l,
    match envs_app false (Esnoc Enil j (l ↦t v)) Δ with
    | Some Δ' =>
       envs_entails Δ' (target_red (fill K (Val $ LitV $ LitLoc l)) Ψ)
    | None => False
    end) →
  envs_entails Δ (target_red (fill K (Alloc (Val v))) Ψ).
Proof.
  rewrite envs_entails_eq=> HΔ. iIntros "He".
  iApply target_red_bind. iApply target_red_alloc.
  iIntros (l) "Hl". specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  iApply target_red_base. iModIntro.
  iApply HΔ. rewrite envs_app_sound //; simpl. iApply "He"; eauto.
Qed.

Lemma tac_source_red_alloc v j K Ψ Δ :
  (∀ l,
    match envs_app false (Esnoc Enil j (l ↦s v)) Δ with
    | Some Δ' =>
       envs_entails Δ' (source_red (fill K (Val $ LitV $ LitLoc l)) Ψ)
    | None => False
    end) →
  envs_entails Δ (source_red (fill K (Alloc (Val v))) Ψ).
Proof.
  rewrite envs_entails_eq=> HΔ. iIntros "He".
  iApply source_red_bind. iApply source_red_alloc.
  iIntros (l) "Hl". specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  iApply source_red_base. iModIntro.
  iApply HΔ. rewrite envs_app_sound //; simpl. iApply "He"; eauto.
Qed.

Lemma tac_target_red_free l v i K Ψ Δ :
  envs_lookup i Δ = Some (false, l ↦t v)%I →
  (let Δ' := envs_delete false i false Δ in
    envs_entails Δ' (target_red (fill K (Val $ LitV LitUnit)) Ψ)) →
  envs_entails Δ (target_red (fill K (Free (LitV l))) Ψ).
Proof.
  rewrite envs_entails_eq=> Hlk Hfin.
  rewrite -target_red_bind. eapply wand_apply; first exact: target_red_free.
  rewrite envs_lookup_split //; simpl.
  iIntros "H". iApply sep_mono_r.
  { iIntros "H". iApply target_red_base. iModIntro. iApply "H". }
  rewrite -Hfin.
  rewrite (envs_lookup_sound' _ _ _ _ _ Hlk).
  by rewrite wand_elim_r.
Qed.

Lemma tac_source_red_free l v i K Ψ Δ :
  envs_lookup i Δ = Some (false, l ↦s v)%I →
  (let Δ' := envs_delete false i false Δ in
    envs_entails Δ' (source_red (fill K (Val $ LitV LitUnit)) Ψ)) →
  envs_entails Δ (source_red (fill K (Free (LitV l))) Ψ).
Proof.
  rewrite envs_entails_eq=> Hlk Hfin.
  rewrite -source_red_bind. eapply wand_apply; first exact: source_red_free.
  rewrite envs_lookup_split //; simpl.
  iIntros "H". iApply sep_mono_r.
  { iIntros "H". iApply source_red_base. iModIntro. iApply "H". }
  rewrite -Hfin.
  rewrite (envs_lookup_sound' _ _ _ _ _ Hlk).
  by rewrite wand_elim_r.
Qed.

Lemma tac_target_red_load Δ i K b l q v Ψ :
  envs_lookup i Δ = Some (b, l ↦t{q} v)%I →
  envs_entails Δ (target_red (fill K (Val v)) Ψ) →
  envs_entails Δ (target_red (fill K (Load (LitV l))) Ψ).
Proof.
  rewrite envs_entails_eq=> ? Hi.
  rewrite -target_red_bind. eapply wand_apply; first exact: target_red_load.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply target_red_base. iModIntro.
    iApply Hi. iApply "He". iFrame "#".
  * apply sep_mono_r, wand_mono; first done. rewrite Hi. iIntros "Ht".
    iApply target_red_base; eauto.
Qed.

Lemma tac_source_red_load Δ i K b l q v Ψ :
  envs_lookup i Δ = Some (b, l ↦s{q} v)%I →
  envs_entails Δ (source_red (fill K (Val v)) Ψ) →
  envs_entails Δ (source_red (fill K (Load (LitV l))) Ψ).
Proof.
  rewrite envs_entails_eq=> ? Hi.
  rewrite -source_red_bind. eapply wand_apply; first exact: source_red_load.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply source_red_base. iModIntro.
    iApply Hi. iApply "He". iFrame "#".
  * apply sep_mono_r, wand_mono; first done. rewrite Hi. iIntros "Hs".
    iApply source_red_base; eauto.
Qed.

Lemma tac_target_red_store Δ i K l v v' Ψ :
  envs_lookup i Δ = Some (false, l ↦t v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦t v')) Δ with
  | Some Δ' => envs_entails Δ' (target_red (fill K (Val $ LitV LitUnit)) Ψ)
  | None => False
  end →
  envs_entails Δ (target_red (fill K (Store (LitV l) (Val v'))) Ψ).
Proof.
  rewrite envs_entails_eq=> ? Hi.
  destruct (envs_simple_replace _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  rewrite -target_red_bind. eapply wand_apply; first by eapply target_red_store.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. apply sep_mono_r, wand_mono; first done.
  rewrite Hi. iIntros "Ht". iApply target_red_base; eauto.
Qed.

Lemma tac_source_red_store Δ i K l v v' Ψ :
  envs_lookup i Δ = Some (false, l ↦s v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦s v')) Δ with
  | Some Δ' => envs_entails Δ' (source_red (fill K (Val $ LitV LitUnit)) Ψ)
  | None => False
  end →
  envs_entails Δ (source_red (fill K (Store (LitV l) (Val v'))) Ψ).
Proof.
  rewrite envs_entails_eq=> ? Hi.
  destruct (envs_simple_replace _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  rewrite -source_red_bind. eapply wand_apply; first by eapply source_red_store.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. apply sep_mono_r, wand_mono; first done.
  rewrite Hi. iIntros "Hs". iApply source_red_base; eauto.
Qed.

Lemma tac_target_red_call Δ i K b f v K_t Ψ :
  envs_lookup i Δ = Some (b, f @t K_t)%I →
  envs_entails Δ (target_red (fill K (fill K_t (Val v))) Ψ) →
  envs_entails Δ (target_red (fill K (Call (Val $ LitV $ LitFn f) (Val v))) Ψ).
Proof.
  rewrite envs_entails_eq=> ? Hi.
  rewrite -target_red_bind. eapply wand_apply; first exact: target_red_call.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  * iIntros "[#$ He]". iApply target_red_base. iModIntro.
    iApply Hi. iApply "He". iFrame "#".
  * rewrite Hi. iIntros "[#Hf Hs]". iSplitR; first done.
    iApply target_red_base. iSpecialize ("Hs" with "Hf"); eauto.
Qed.

Lemma tac_source_red_call Δ i K b f v K_s Ψ :
  envs_lookup i Δ = Some (b, f @s K_s)%I →
  envs_entails Δ (source_red (fill K (fill K_s (Val v))) Ψ) →
  envs_entails Δ (source_red (fill K (Call (Val $ LitV $ LitFn f) (Val v))) Ψ).
Proof.
  rewrite envs_entails_eq=> ? Hi.
  rewrite -source_red_bind. eapply wand_apply; first exact: source_red_call.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  * iIntros "[#$ He]". iApply source_red_base. iModIntro.
    iApply Hi. iApply "He". iFrame "#".
  * rewrite Hi. iIntros "[#Hf Hs]". iSplitR; first done.
    iApply source_red_base. iSpecialize ("Hs" with "Hf"); eauto.
Qed.


Lemma tac_to_target Δ e_t e_s Φ :
  envs_entails Δ (target_red e_t (λ e_t', e_t' ⪯ e_s [{ Φ }]))%I →
  envs_entails Δ (e_t ⪯ e_s [{ Φ }]).
Proof. rewrite envs_entails_eq=> Hi. by rewrite -target_red_sim_expr. Qed.

Lemma tac_to_source Δ e_t e_s Φ :
  envs_entails Δ (source_red e_s (λ e_s', e_t ⪯ e_s' [{ Φ }]))%I →
  envs_entails Δ (e_t ⪯ e_s [{ Φ }]).
Proof. rewrite envs_entails_eq=> Hi. by rewrite -source_red_sim_expr. Qed.

Lemma tac_target_to_sim Δ e_t e_s Φ :
  envs_entails Δ (e_t ⪯ e_s [{ Φ }]) →
  envs_entails Δ (target_red e_t (λ e_t', e_t' ⪯ e_s [{ Φ }]))%I.
Proof.
  rewrite envs_entails_eq=> Hi. rewrite -target_red_base.
  iIntros "He". iModIntro. by iApply Hi.
Qed.

Lemma tac_source_to_sim Δ e_t e_s Φ :
  envs_entails Δ (e_t ⪯ e_s [{ Φ }]) →
  envs_entails Δ (source_red e_s (λ e_s', e_t ⪯ e_s' [{ Φ }]))%I.
Proof.
  rewrite envs_entails_eq=> Hi. rewrite -source_red_base.
  iIntros "He". iModIntro. by iApply Hi.
Qed.

Lemma tac_sim_expr_to_sim Δ e_t e_s Φ :
  envs_entails Δ (e_t ⪯ e_s {{ Φ }}) →
  envs_entails Δ (e_t ⪯ e_s [{ lift_post Φ }])%I.
Proof. done. Qed.

Lemma tac_sim_to_sim_expr Δ e_t e_s Φ :
  envs_entails Δ (e_t ⪯ e_s [{ lift_post Φ }]) →
  envs_entails Δ (e_t ⪯ e_s {{ Φ }})%I.
Proof. done. Qed.
End sim.

(** ** automation for source_red and target_red *)
(* the proofmode works with sim_expr, not sim *)
Ltac to_sim :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim_expr _ _ _ _) => idtac
  | |- envs_entails _ (sim _ _ ?e_t ?e_s) =>
      notypeclasses refine (tac_sim_to_sim_expr _ _ e_t e_s _ _)
  | |- envs_entails _ (target_red ?e_t (λ _, sim_expr _ _ _ _ )) =>
      notypeclasses refine (tac_target_to_sim _ _ e_t _ _ _)
  | |- envs_entails _ (source_red ?e_s (λ _, sim_expr _ _ _ _)) =>
      notypeclasses refine (tac_source_to_sim _ _ _ e_s _ _)
  | _ => fail "not a target_red or source_red of suitable shape"
  end.

Ltac to_target :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (target_red _ _) => idtac
  | _ =>
    to_sim;
    lazymatch goal with
    | |- envs_entails _ (sim_expr ?Ω ?Φ ?e_t ?e_s) =>
        notypeclasses refine (tac_to_target  Ω _ e_t e_s Φ _)
    | _ => fail "to_target: not a sim"
    end
  end.

Ltac to_source :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (source_red _ _) => idtac
  | _ =>
    to_sim;
    lazymatch goal with
    | |- envs_entails _ (sim_expr ?Ω ?Φ ?e_t ?e_s) =>
        notypeclasses refine (tac_to_source  Ω _ e_t e_s Φ _)
    | _ => fail "to_source: not a sim"
    end
  end.

(** ** simple automation for evaluation *)
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
  | |- envs_entails _ (sim _ (λ _ _, bupd _) (Val _) (Val _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim _ (λ _ _, sim_expr _ _ _ _) (Val _) (Val _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim _ (λ _ _, sim _ _ _ _) (Val _) (Val _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim _ _ (Val _) (Val _)) =>
      eapply tac_sim_value
  end.

(* TODO: do we even need this? *)
Tactic Notation "sim_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?Ω ?Φ ?e_t ?e_s) =>
    notypeclasses refine (tac_sim_expr_eval Ω _ _ e_t _ e_s _ _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl | ]
  | _ => fail "sim_expr_eval: not a 'sim"
  end.
Ltac sim_expr_simpl := sim_expr_eval simpl.

(* finish and switch back to a sim, if possible *)
Ltac sim_finish :=
  (* TODO: can remove sim_expr_simpl if we do not use sim_finish anywhere explicitly *)
  sim_expr_simpl;      (* simplify occurences of subst/fill *)
  match goal with
  | |- envs_entails _ (sim_expr _ (lift_post _) ?e_t ?e_s) =>
      notypeclasses refine (tac_sim_expr_to_sim _ _ e_t e_s _ _)
  | |- envs_entails _ (sim_expr _ _ _ _) => idtac
  | |- envs_entails _ (sim _ _ _ _) => idtac
  end;
  try sim_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify λs caused by wp_value *)

(** target_red *)
Tactic Notation "target_red_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e_t ?Ψ) =>
    notypeclasses refine (tac_target_red_expr_eval _ _ e_t _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl| ]
  | _ => fail "target_red_expr_eval: not a 'target_red"
  end.
Ltac target_expr_simpl := target_red_expr_eval simpl.

Ltac target_value_head :=
  lazymatch goal with
  | |- envs_entails _ (target_red (Val _) (λ _, bupd _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) (λ _, sim_expr _ _ _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) (λ _, sim _ _ _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) (λ _, target_red _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) _) =>
      eapply tac_target_red_base
  end.

Ltac target_finish :=
  target_expr_simpl;      (* simplify occurences of subst/fill *)
  first [target_value_head; try sim_finish | pm_prettify].

(** source_red *)
Tactic Notation "source_red_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e_s ?Ψ) =>
    notypeclasses refine (tac_source_red_expr_eval _ _ e_s _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl| ]
  | _ => fail "source_red_expr_eval: not a 'target_red"
  end.
Ltac source_expr_simpl := source_red_expr_eval simpl.

Ltac source_value_head :=
  lazymatch goal with
  | |- envs_entails _ (source_red (Val _) (λ _, bupd _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) (λ _, sim_expr _ _ _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) (λ _, sim _ _ _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) (λ _, source_red _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) _) =>
      eapply tac_source_red_base; try iIntros (_ _)
  end.

Ltac source_finish :=
  source_expr_simpl;      (* simplify occurences of subst/fill *)
  first [source_value_head; try sim_finish | pm_prettify].


(** ** Pure reduction *)

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "target_pure" open_constr(efoc) :=
  iStartProof;
  to_target;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e_t _) =>
    let e_t := eval simpl in e_t in
    reshape_expr e_t ltac:(fun K_t e_t' =>
      unify e_t' efoc;
      eapply (tac_target_red_pure _ _ e_t' _ K_t _ _);
      [ iSolveTC                       (* PureExec *)
      | try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      | target_finish                      (* new goal *)
      ])
    || fail "target_red_pure: cannot find" efoc "in" e_t "or" efoc "is not a redex"
  | _ => fail "target_red_pure: not a 'target_red"
  end.

(** We have not declared an instance for the reduction of while:
  usually, we do not want to reduce it arbitrarily, but instead do an induction. *)
Tactic Notation "target_while" :=
  let Hwhile := fresh "H" in
  pose (Hwhile := pure_while);
  target_pure (While _ _);
  clear Hwhile.

Tactic Notation "target_if" := target_pure (If _ _ _).
Tactic Notation "target_if_true" := target_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "target_if_false" := target_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "target_unop" := target_pure (UnOp _ _).
Tactic Notation "target_binop" := target_pure (BinOp _ _ _).
Tactic Notation "target_op" := target_unop || target_binop.
Tactic Notation "target_let" := target_pure (Let (BNamed _) _ _).
Tactic Notation "target_seq" := target_pure (Let BAnon _ _).
Tactic Notation "target_proj" := target_pure (Fst _) || target_pure (Snd _).
Tactic Notation "target_match" := target_pure (Match _ _ _ _ _).
Tactic Notation "target_inj" := target_pure (InjL _) || target_pure (InjR _).
Tactic Notation "target_pair" := target_pure (Pair _ _).

Ltac target_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (target_pure _; [])
        | target_finish (* In case target_pure never ran, make sure we do the usual cleanup.*)
        ].

Tactic Notation "source_pure" open_constr(efoc) :=
  iStartProof;
  to_source;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e_s _) =>
    let e_s := eval simpl in e_s in
    reshape_expr e_s ltac:(fun K_s e_s' =>
      unify e_s' efoc;
      eapply (tac_source_red_pure _ _ e_s' _ K_s _ _);
      [ iSolveTC                       (* PureExec *)
      | try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      | source_finish                      (* new goal *)
      ])
    || fail "source_red_pure: cannot find" efoc "in" e_s "or" efoc "is not a redex"
  | _ => fail "source_red_pure: not a 'sim'"
  end.

Tactic Notation "source_while" :=
  let Hwhile := fresh "H" in
  pose (Hwhile := pure_while);
  source_pure (While _ _);
  clear Hwhile.

Tactic Notation "source_if" := source_pure (If _ _ _).
Tactic Notation "source_if_true" := source_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "source_if_false" := source_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "source_unop" := source_pure (UnOp _ _).
Tactic Notation "source_binop" := source_pure (BinOp _ _ _).
Tactic Notation "source_op" := source_unop || source_binop.
Tactic Notation "source_let" := source_pure (Let (BNamed _) _ _).
Tactic Notation "source_seq" := source_pure (Let BAnon _ _).
Tactic Notation "source_proj" := source_pure (Fst _) || source_pure (Snd _).
Tactic Notation "source_match" := source_pure (Match _ _ _ _ _).
Tactic Notation "source_inj" := source_pure (InjL _) || source_pure (InjR _).
Tactic Notation "source_pair" := source_pure (Pair _ _).

Ltac source_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (source_pure _; [])
        | source_finish (* In case source_red_pure never ran, make sure we do the usual cleanup.*)
        ].

Ltac sim_pures_int := (try target_pures); (try source_pures); try to_sim.
Ltac sim_pures := (try target_pures); (try source_pures); try (to_sim; sim_finish).



(** ** Bind tactics *)

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
  to_sim;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?Ω ?Q ?e_t ?e_s) =>
    first [ reshape_expr e_t ltac:(fun K_t e_t' => unify e_t' efoc_t;
                                    first [ reshape_expr e_s ltac:(fun K_s e_s' => unify e_s' efoc_s; sim_bind_core K_t K_s)
                                           (* TODO: fix error handling *)
                                           | fail 1 "sim_bind: cannot find" efoc_s "in" e_s]
                                  )
          | fail 1 "sim_bind: cannot find" efoc_t "in" e_t ]
  | _ => fail "sim_bind: not a 'sim'"
  end.

Ltac target_bind_core K_t :=
  lazymatch eval hnf in K_t with
  | [] => idtac
  | _ => eapply (tac_target_red_bind K_t); [simpl; reflexivity| reduction.pm_prettify]
  end.

Tactic Notation "target_bind" open_constr(efoc_t) :=
  iStartProof;
  to_target;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e_t ?Ψ) =>
    first [ reshape_expr e_t ltac:(fun K_t e_t' => unify e_t' efoc_t;
                                    target_bind_core K_t
                                  )
          | fail 1 "target_bind: cannot find" efoc_t "in" e_t ]
  | _ => fail "target_bind: not a 'target_red'"
  end.

Ltac source_bind_core K_s :=
  lazymatch eval hnf in K_s with
  | [] => idtac
  | _ => eapply (tac_source_red_bind K_s); [simpl; reflexivity| reduction.pm_prettify]
  end.

Tactic Notation "source_bind" open_constr(efoc_s) :=
  iStartProof;
  to_source;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e_s ?Ψ) =>
    first [ reshape_expr e_s ltac:(fun K_s e_s' => unify e_s' efoc_s;
                                    source_bind_core K_s
                                  )
          | fail 1 "source_bind: cannot find" efoc_s "in" e_s ]
  | _ => fail "source_bind: not a 'source_red'"
  end.

(** ** Call automation *)
Tactic Notation "target_call" :=
  to_target;
  let solve_hasfun _ :=
    let f := match goal with |- _ = Some (_, (?f @t _)%I) => f end in
    iAssumptionCore || fail "target_call: cannot find" f "@t ?" in
  target_pures;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_call _ _ K _ _ _ _ _))
      |fail 1 "target_call: cannot find 'Call' in" e];
    [ solve_hasfun ()
    |target_finish]
  | _ => fail "target_call: not a 'target_red'"
  end.

Tactic Notation "source_call" :=
  to_source;
  let solve_hasfun _ :=
    let f := match goal with |- _ = Some (_, (?f @s _)%I) => f end in
    iAssumptionCore || fail "source_call: cannot find" f "@s ?" in
  source_pures;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_call _ _ K _ _ _ _ _))
      |fail 1 "source_call: cannot find 'Call' in" e];
    [ solve_hasfun ()
    |source_finish]
  | _ => fail "source_call: not a 'source_red'"
  end.

(** ** Heap automation *)
Tactic Notation "target_alloc" ident(l) "as" constr(H) :=
  to_target;
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "target_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "target_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; target_finish
    end in
  target_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_target_red_alloc].
     If that fails, it tries to use the lemma [tac_target_red_allocN]
     for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦t∗ [v] instead of
     l ↦t v for single references. These are logically equivalent assertions
     but are not equal. *)
  lazymatch goal with
  | |- envs_entails _ (target_red ?e ?Ψ) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_alloc _ Htmp K _ _))
          |fail 1 "target_alloc: cannot find 'Alloc' in" e];
        finish ()
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_allocN _ _ Htmp K _ _))
          |fail 1 "target_alloc: cannot find 'AllocN' in" e];
        [idtac|finish ()]
    in (process_single ()) || (process_array ())
  | _ => fail "target_alloc: not a 'target_red'"
  end.

Tactic Notation "target_alloc" ident(l) :=
  target_alloc l as "?".

Tactic Notation "source_alloc" ident(l) "as" constr(H) :=
  to_source;
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "source_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "source_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; source_finish
    end in
  source_pures;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e ?Ψ) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_alloc _ Htmp K _ _))
          |fail 1 "source_alloc: cannot find 'Alloc' in" e];
        finish ()
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_allocN _ _ Htmp K _ _))
          |fail 1 "source_alloc: cannot find 'Alloc' in" e];
        [idtac|finish ()]
    in (process_single ()) || (process_array ())
  | _ => fail "source_alloc: not a 'source_red'"
  end.

Tactic Notation "source_alloc" ident(l) :=
  source_alloc l as "?".

Tactic Notation "target_free" :=
  to_target;
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦t{_} _)%I) => l end in
    iAssumptionCore || fail "target_free: cannot find" l "↦t ?" in
  target_pures;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_free _ _ _ K _ _))
      |fail 1 "target_free: cannot find 'Free' in" e];
    [solve_mapsto ()
    |pm_reduce; target_finish]
  | _ => fail "target_free: not a 'target_red'"
  end.

Tactic Notation "source_free" :=
  to_source;
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦s{_} _)%I) => l end in
    iAssumptionCore || fail "source_free: cannot find" l "↦s ?" in
  source_pures;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_free _ _ _ K _ _))
      |fail 1 "source_free: cannot find 'Free' in" e];
    [solve_mapsto ()
    |pm_reduce; source_finish]
  | _ => fail "source_free: not a 'source_red'"
  end.

Tactic Notation "target_load" :=
  to_target;
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦t{_} _)%I) => l end in
    iAssumptionCore || fail "target_load: cannot find" l "↦t ?" in
  target_pures;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_load _ _ K _ _ _ _ _))
      |fail 1 "target_load: cannot find 'Load' in" e];
    [ solve_mapsto ()
    |target_finish]
  | _ => fail "target_load: not a 'target_red'"
  end.

Tactic Notation "source_load" :=
  to_source;
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦s{_} _)%I) => l end in
    iAssumptionCore || fail "source_load: cannot find" l "↦s ?" in
  source_pures;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_load _ _ K _ _ _ _ _))
      |fail 1 "source_load: cannot find 'Load' in" e];
    [ solve_mapsto ()
    |source_finish]
  | _ => fail "source_load: not a 'source_red'"
  end.


(* FIXME: error messages seem broken (already the eapply seems to fail when the pointsto-assumption is missing)*)
Tactic Notation "target_store" :=
  to_target;
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦t{_} _)%I) => l end in
    iAssumptionCore || fail "target_store: cannot find" l "↦t ?" in
  target_pures;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_store _ _ K _ _ _ Ψ))
      |fail 1 "target_store: cannot find 'Store' in" e];
    [solve_mapsto ()
    |pm_reduce; target_finish]
  | _ => fail "target_store: not a 'target_red'"
  end.

Tactic Notation "source_store" :=
  to_source;
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦s{_} _)%I) => l end in
    iAssumptionCore || fail "source_store: cannot find" l "↦s ?" in
  source_pures;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_store _ _ K _ _ _ Ψ))
      |fail 1 "source_store: cannot find 'Store' in" e];
    [solve_mapsto ()
    |pm_reduce; source_finish]
  | _ => fail "source_store: not a 'source_red'"
  end.


(** ** Automation related to stuckness *)

(* FIXME: currently quite tailored to the sideconditions generated by the instances we already have.
  Maybe we can make this more general? *)
Ltac source_stuck_sidecond :=
  unfold bin_op_eval, un_op_eval, vals_compare_safe,val_is_unboxed,lit_is_unboxed in *;
  repeat match goal with
  | H : _ ∨ _ |- _ => destruct H
  | H : _ ∧ _ |- _ => destruct H
  | H : ∃ _, _ |- _ => destruct H
  | H : is_Some _ |- _ => destruct H
  end;
  simpl in *;
  first [by eauto | congruence].

Ltac source_stuck_sidecond_bt :=
  intros;
  match goal with
  | |- ¬ _ => intros ?; source_stuck_sidecond_bt
  | |- _ ∧ _ => split; source_stuck_sidecond_bt
  | |- _ ∨ _ => left; source_stuck_sidecond_bt
  | |- _ ∨ _ => right; source_stuck_sidecond_bt
  | |- _ => source_stuck_sidecond
  end.

Ltac source_stuck_prim :=
  to_source; iApply source_stuck_prim; [ source_stuck_sidecond_bt | reflexivity].

Ltac discr_source :=
  let discr _ :=
    iIntros "%";
    repeat match goal with
           | H : _ ∧ _ |- _ => destruct H
           | H : _ ∨ _ |- _ => destruct H
           | H : ∃ _, _ |- _ => destruct H
           end; subst in
  match goal with
  | |- envs_entails _ (source_red _ _) => iApply source_red_irred_unless; [try done | discr ()]
  | |- envs_entails _ (sim_expr _ _ _ _) => iApply sim_irred_unless; [try done | discr ()]
  | |- envs_entails _ (sim _ _ _ _) => iApply sim_irred_unless; [try done | discr ()]
  end.
