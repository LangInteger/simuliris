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
Context `{!sheapG Σ}.
Context (Ω : val → val → iProp Σ).
Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{Ω} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

Lemma tac_sim_expr_eval Δ Φ e_t e_t' e_s e_s' :
  (∀ (e_t'':=e_t'), e_t = e_t'') →
  (∀ (e_s'':=e_s'), e_s = e_s'') →
  envs_entails Δ (e_t' ⪯ e_s' {{ Φ }}) → envs_entails Δ (e_t ⪯ e_s {{ Φ }}).
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
  envs_entails Δ (∀ P_s σ_s, |==> Ψ P_s e_s σ_s : iProp Σ) → envs_entails Δ (source_red e_s Ψ).
Proof.
  rewrite envs_entails_eq => ->. iIntros "H". by iApply source_red_base.
Qed.
Lemma tac_source_red_base_no_bupd e_s Ψ Δ :
  envs_entails Δ (∀ P_s σ_s, Ψ P_s e_s σ_s : iProp Σ) → envs_entails Δ (source_red e_s Ψ).
Proof.
  rewrite envs_entails_eq => ->. iIntros "H". iApply source_red_base.
  iIntros (??). iModIntro; eauto.
Qed.

Lemma tac_sim_value v_t v_s Φ Δ :
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
  iApply target_red_bind. iApply target_red_allocN; first done.
  iIntros (l) "Hl". specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  iApply target_red_base. iModIntro. iExists #l; iSplitR; first done.
  iApply HΔ.
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
  iApply source_red_bind. iApply source_red_allocN; first done.
  iIntros (l) "Hl". specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  iApply source_red_base; iIntros (??). iModIntro. iExists #l; iSplitR; first done.
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
  iApply target_red_base. iModIntro. iExists #l; iSplitR; first done.
  iApply HΔ.
  rewrite envs_app_sound //; simpl. iApply "He"; eauto.
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
  iApply source_red_base; iIntros (??). iModIntro. iExists #l; iSplitR; first done.
  iApply HΔ.
  rewrite envs_app_sound //; simpl. iApply "He"; eauto.
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
  { iIntros "H". iApply target_red_base. iModIntro. iExists (#()); iSplitR; first done. iApply "H". }
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
  { iIntros "H". iApply source_red_base; iIntros (??). iModIntro. iExists (#()); iSplitR; first done. iApply "H". }
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
  * iIntros "[#$ He]". iIntros "_". iApply target_red_base. iModIntro. iExists v; iSplit; first done.
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
  * iIntros "[#$ He]". iIntros "_". iApply source_red_base; iIntros (??). iModIntro. iExists v; iSplit; first done.
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

Lemma tac_to_target Δ e_t e_s Φ :
  envs_entails Δ (target_red e_t (λ e_t', e_t' ⪯ e_s {{ Φ }}))%I →
  envs_entails Δ (e_t ⪯ e_s {{ Φ }}).
Proof. rewrite envs_entails_eq=> Hi. by rewrite -target_red_sim. Qed.

Lemma tac_to_source Δ e_t e_s Φ :
  envs_entails Δ (source_red e_s (λ _ e_s' _, e_t ⪯ e_s' {{ Φ }}))%I →
  envs_entails Δ (e_t ⪯ e_s {{ Φ }}).
Proof. rewrite envs_entails_eq=> Hi. by rewrite -source_red_sim. Qed.


Lemma tac_target_to_sim Δ e_t e_s Φ :
  envs_entails Δ (e_t ⪯ e_s {{ Φ }}) →
  envs_entails Δ (target_red e_t (λ e_t', e_t' ⪯ e_s {{ Φ }}))%I.
Proof.
  rewrite envs_entails_eq=> Hi. rewrite -target_red_base.
  iIntros "He". iModIntro. by iApply Hi.
Qed.

Lemma tac_source_to_sim Δ e_t e_s Φ :
  envs_entails Δ (e_t ⪯ e_s {{ Φ }}) →
  envs_entails Δ (source_red e_s (λ _ e_s' _, e_t ⪯ e_s' {{ Φ }}))%I.
Proof.
  rewrite envs_entails_eq=> Hi. rewrite -source_red_base.
  iIntros "He" (??). iModIntro. by iApply Hi.
Qed.

End sim.

(** ** automation for source_red and target_red *)
Ltac to_sim :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim _ _ _ _) => idtac
  | |- envs_entails _ (target_red ?e_t _) =>
      notypeclasses refine (tac_target_to_sim _ _ e_t _ _ _)
  | |- envs_entails _ (source_red ?e_s _) =>
      notypeclasses refine (tac_source_to_sim _ _ _ e_s _ _)
  | _ => fail "not a target_eval or source_eval of suitable shape"
  end.

Ltac to_target :=
  iStartProof;
  to_sim;
  lazymatch goal with
  | |- envs_entails _ (sim ?Ω ?e_t ?e_s ?Φ) =>
      notypeclasses refine (tac_to_target  Ω _ e_t e_s Φ _)
  | _ => fail "to_target: not a sim"
  end.

Ltac to_source :=
  iStartProof;
  to_sim;
  lazymatch goal with
  | |- envs_entails _ (sim ?Ω ?e_t ?e_s ?Φ) =>
      notypeclasses refine (tac_to_source  Ω _ e_t e_s Φ _)
  | _ => fail "to_source: not a sim"
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
  | |- envs_entails _ (sim _ (Val _) (Val _) (λ _ _, bupd _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim _ (Val _) (Val _) (λ _ _, sim _ _ _ _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim _ (Val _) (Val _) _) =>
      eapply tac_sim_value
  end.

(* TODO: do we even need this? *)
Tactic Notation "sim_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim ?Ω ?e_t ?e_s ?Φ) =>
    notypeclasses refine (tac_sim_expr_eval Ω _ _ e_t _ e_s _ _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl | ]
  | _ => fail "sim_expr_eval: not a 'sim"
  end.
Ltac sim_expr_simpl := sim_expr_eval simpl.

Ltac sim_finish :=
  (* TODO: can remove sim_expr_simpl if we do not use sim_finish anywhere explicitly *)
  sim_expr_simpl;      (* simplify occurences of subst/fill *)
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
  | |- envs_entails _ (target_red (Val _) (λ _, sim _ _ _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) _) =>
      eapply tac_target_red_base
  end.

Ltac target_finish :=
  target_expr_simpl;      (* simplify occurences of subst/fill *)
  first [target_value_head; sim_finish | pm_prettify].

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

(* TODO: make more robust by using variant of source_red that takes predicates expr → iProp (instead of iIntros) *)
Ltac source_value_head :=
  lazymatch goal with
  | |- envs_entails _ (source_red (Val _) (λ _ _ _, bupd _)) =>
      eapply tac_source_red_base_no_bupd; try iIntros (_ _)
  | |- envs_entails _ (source_red (Val _) (λ _ _ _, sim _ _ _ _)) =>
      eapply tac_source_red_base_no_bupd; try iIntros (_ _)
  | |- envs_entails _ (source_red (Val _) _) =>
      eapply tac_source_red_base; try iIntros (_ _)
  end.

Ltac source_finish :=
  source_expr_simpl;      (* simplify occurences of subst/fill *)
  first [source_value_head; sim_finish | pm_prettify].

(** ** Pure reduction *)

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "target_red_pure" open_constr(efoc) :=
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

Tactic Notation "source_red_pure" open_constr(efoc) :=
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

Ltac target_red_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (target_red_pure _; [])
        | target_finish (* In case target_red_pure never ran, make sure we do the usual cleanup.*)
        ].

Ltac source_red_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (source_red_pure _; [])
        | source_finish (* In case source_red_pure never ran, make sure we do the usual cleanup.*)
        ].

Ltac sim_pures := (try target_red_pures); (try source_red_pures); try to_sim.


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


(** ** Heap automation *)
(*Tactic Notation "target_store" :=*)
  (*let solve_mapsto _ :=*)
    (*let l := match goal with |- _ = Some (_, (?l ↦t{_} _)%I) => l end in*)
    (*iAssumptionCore || fail "target_store: cannot find" l "↦t ?" in*)
  (*sim_pures;*)
  (*lazymatch goal with*)
  (*| |- envs_entails _ (target_red ?Ψ ?e) =>*)
    (*first*)
      (*[reshape_expr e ltac:(fun K e' => eapply (tac_target_red_store _ _ K _ _ _ Ψ))*)
      (*|fail 1 "wp_store: cannot find 'Store' in" e];*)
    (*[solve_mapsto ()*)
    (*|pm_reduce; first [sim_seq|wp_finish]]*)
  (*| _ => fail "target_store: not a 'target_red"*)
  (*end.*)


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
