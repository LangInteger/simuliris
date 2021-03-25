From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From simuliris.base_logic Require Export gen_sim_heap gen_sim_prog gen_heap_bij.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Export class_instances.
From simuliris.simplang Require Import tactics notation primitive_laws.
From simuliris.simplang Require Export primitive_laws proofmode.

From iris.bi Require Import bi.
Import bi.
From iris.bi Require Import derived_laws.
Import bi.

From iris.prelude Require Import options.

(** * Instance of the SimpLang program logic that provides a means of establishing bijections on the heap. *)

Class sbijG (Σ : gFunctors) := SBijG {
  sbijG_sheapG :> sheapG Σ;
  sbijG_bijG :> gen_heap_bijG (Σ:=Σ) (H1:=sheapG_gen_heapG);
}.

Section fix_heap.
  Context `{sbijG Σ} (val_rel : val → val → iProp Σ).
  Context {val_rel_pers : ∀ v_t v_s, Persistent (val_rel v_t v_s)}.
  Instance heap_bij_rel : sheapRel Σ := {|
    sheap_stateRel _ _ := gen_heap_bij_inv (λ ov_t ov_s,
      (∃ v_t v_s, ⌜ov_t = Some v_t⌝ ∗ ⌜ov_s = Some v_s⌝ ∗ val_rel v_t v_s) ∨
      (⌜ov_t = None⌝ ∗ ⌜ov_s = None⌝))%I;
    sheap_progRel _ _ := True%I;
  |}.

  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

  Lemma stuck_reach_stuck P (e : expr) σ:
    stuck P e σ → reach_stuck P e σ.
  Proof. intros Hs; exists e, σ. done. Qed.

  Lemma sim_bij_load l_t l_s Φ :
    l_t ↔h l_s -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ Val v_t ⪯ Val v_s {{ Φ }}) -∗
    (Load (Val $ LitV $ LitLoc l_t)) ⪯ (Load (Val $ LitV $ LitLoc l_s)) {{ Φ }}.
  Proof using val_rel_pers.
    iIntros "#Hbij Hsim". iApply sim_lift_head_step_both.
    iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hstate & Hprog) %Hnstuck]".
    iPoseProof (gen_heap_bij_access with "Hstate Hbij") as (v_t' v_s') "(Hl_t & Hl_s & He & Hclose)".
    iDestruct (gen_heap_valid with "Hσ_t Hl_t") as %?.
    iDestruct (gen_heap_valid with "Hσ_s Hl_s") as %?.
    iDestruct "He" as "[He | [-> ->]]".
    - iDestruct "He" as (v_t v_s) "(-> & -> & #Hv)".
      iModIntro; iSplit; first by eauto with head_step.
      iIntros (e_t' σ_t') "%"; inv_head_step.
      assert (head_step P_s (Load #l_s) σ_s (Val v_s) σ_s) as Hs.
      { eauto with head_step. }
      iModIntro. iExists (Val v_s), σ_s. iFrame.
      iSplitR. { by iPureIntro. }
      iSplitR "Hsim"; first last. { by iApply "Hsim". }
      iApply ("Hclose" with "Hl_t Hl_s []"). iLeft; eauto.
    - exfalso; contradict Hnstuck.
      apply stuck_reach_stuck. split; first done.
      apply sirreducible. source_stuck_sidecond_bt.
  Qed.

  Lemma sim_bij_store l_t l_s v_t v_s Φ :
    l_t ↔h l_s -∗
    val_rel v_t v_s -∗
    #() ⪯ #() {{ Φ }} -∗
    Store (Val $ LitV (LitLoc l_t)) (Val v_t) ⪯ Store (Val $ LitV (LitLoc l_s)) (Val v_s) {{ Φ }}.
  Proof.
    iIntros "Hbij Hval Hsim". iApply sim_lift_head_step_both.
    iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hstate & Hprog) %Hnstuck] !>".
    iPoseProof (gen_heap_bij_access with "Hstate Hbij") as (v_t'' v_s'') "(Hl_t & Hl_s & He & Hclose)".
    iDestruct (gen_heap_valid with "Hσ_t Hl_t") as %?.
    iDestruct (gen_heap_valid with "Hσ_s Hl_s") as %?.
    iDestruct "He" as "[He | [-> ->]]".
    - iDestruct "He" as (v_t' v_s') "(-> & -> & Hval')".
      iSplitR; first by eauto with head_step.
      iIntros (e_t' σ_t') "%"; inv_head_step.
      assert (head_step P_s (#l_s <- v_s) σ_s #() (state_upd_heap <[l_s:=Some v_s]> σ_s)) as Hs.
      { eauto with head_step. }

      iMod (gen_heap_update with "Hσ_t Hl_t") as "[$ Hl_t]".
      iMod (gen_heap_update with "Hσ_s Hl_s") as "[Ha Hl_s]".
      iModIntro. iExists #(),(state_upd_heap <[l_s:=Some v_s]> σ_s).
      iFrame. iSplitR; first by iPureIntro.
      iApply ("Hclose" with "Hl_t Hl_s [Hval]"). iLeft; eauto.
    - exfalso; contradict Hnstuck.
      apply stuck_reach_stuck. split; first done.
      apply sirreducible. source_stuck_sidecond_bt.
  Qed.

  Lemma sim_bij_free l_t l_s Φ :
    l_t ↔h l_s -∗
    #() ⪯ #() {{ Φ }} -∗
    Free (Val $ LitV $ LitLoc l_t) ⪯ Free (Val $ LitV $ LitLoc l_s) {{ Φ }}.
  Proof.
    iIntros "Hbij Hsim". iApply sim_lift_head_step_both.
    iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hstate & Hprog) %Hnstuck]".
    iPoseProof (gen_heap_bij_access with "Hstate Hbij") as (v_t'' v_s'') "(Hl_t & Hl_s & He & Hclose)".
    iDestruct (gen_heap_valid with "Hσ_t Hl_t") as %?.
    iDestruct (gen_heap_valid with "Hσ_s Hl_s") as %?.
    iDestruct "He" as "[He | [-> ->]]".
    - iDestruct "He" as (v_t' v_s') "(-> & -> & Hval')".
      iSplitR; first by eauto with head_step. iModIntro.
      iIntros (e_t' σ_t') "%"; inv_head_step.
      assert (head_step P_s (Free #l_s) σ_s #() (state_upd_heap <[l_s:=None]> σ_s)) as Hs.
      { eauto with head_step. }

      iMod (gen_heap_update with "Hσ_t Hl_t") as "[$ Hl_t]".
      iMod (gen_heap_update with "Hσ_s Hl_s") as "[Ha Hl_s]".
      iModIntro. iExists #(),(state_upd_heap <[l_s:=None]> σ_s).
      iFrame. iSplitR; first by iPureIntro.
      iApply ("Hclose" with "Hl_t Hl_s"). iRight; eauto.
    - exfalso; contradict Hnstuck.
      apply stuck_reach_stuck. split; first done.
      apply sirreducible. source_stuck_sidecond_bt.
  Qed.

  Lemma sim_bij_insert l_t l_s v_t v_s e_t e_s Φ :
    l_t ↦t v_t -∗
    l_s ↦s v_s -∗
    val_rel v_t v_s -∗
    (l_t ↔h l_s -∗ e_t ⪯ e_s {{ Φ }}) -∗
    e_t ⪯ e_s {{ Φ }}.
  Proof.
    iIntros "Hl_t Hl_s Hval Hsim". iApply sim_update_si.
    iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hstate & Hprog)".
    iMod (gen_heap_bij_insert with "Hstate Hl_t Hl_s [Hval]") as "[Hb #Ha]";
      first by iLeft; eauto.
    iModIntro. iSplitR "Hsim"; last by iApply "Hsim".
    iFrame.
  Qed.
End fix_heap.


(** ** Extension of the proofmode *)
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From simuliris.simplang Require Export proofmode.


(* the bij invariant isn't dependent on the parameters, so this is trivial. *)
Ltac solve_state_sidecond ::= iAssumption.

(** New lemmas for the new tactics *)

Section sim.
  Context `{sbijG Σ} (val_rel : val → val → iProp Σ).
  Context {val_rel_pers : ∀ v_t v_s, Persistent (val_rel v_t v_s)}.
  Instance : sheapRel Σ := heap_bij_rel val_rel.

  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

  Implicit Types
    (K_t K_s : ectx)
    (l_t l_s : loc)
    (v_t v_s : val)
    (e_t e_s : expr).

  Instance maybe_persistent b (P : iProp Σ) : Persistent P → Persistent (□?b P).
  Proof.
    intros Hp. destruct b; simpl; last by eauto.
    rewrite /Persistent. iIntros "#H"; eauto.
  Qed.

  Lemma tac_bij_load Δ i j b K_t K_s l_t l_s Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    (∀ v_t v_s,
      match envs_app true (Esnoc Enil j (val_rel v_t v_s)) Δ with
      | Some Δ' =>
          envs_entails Δ' (sim val_rel (fill K_t (Val v_t)) (fill K_s (Val v_s)) Φ)
      | None => False
      end) →
    envs_entails Δ (sim val_rel (fill K_t (Load (LitV l_t))) (fill K_s (Load (LitV l_s))) Φ)%I.
  Proof using val_rel_pers.
    rewrite envs_entails_eq=> ? Hi.
    rewrite -sim_bind. eapply wand_apply; first exact: sim_bij_load.
    rewrite envs_lookup_split //; simpl.
    iIntros "[#Ha He]". iSpecialize ("He" with "Ha").
    rewrite intuitionistically_if_elim. iSplitR; first done.
    iIntros (v_t' v_s') "#Hv". specialize (Hi v_t' v_s').
    destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction].
    iApply sim_value.
    iApply Hi. rewrite envs_app_sound //; simpl. iApply "He"; eauto.
  Qed.

  Lemma tac_bij_store Δ i K_t K_s b l_t l_s v_t' v_s' Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    envs_entails Δ (val_rel v_t' v_s') →
    envs_entails Δ (sim val_rel (fill K_t (Val $ LitV LitUnit)) (fill K_s (Val $ LitV LitUnit)) Φ) →
    envs_entails Δ (sim val_rel (fill K_t (Store (LitV l_t) (Val v_t'))) (fill K_s (Store (LitV l_s) (Val v_s'))) Φ).
  Proof using val_rel_pers.
    rewrite envs_entails_eq => HΔ.
    rewrite (persistent_persistently_2 (val_rel _ _)).
    intros Hv%persistently_entails_r Hi.
    rewrite -sim_bind.
    iIntros "He". iPoseProof (Hv with "He") as "[He #Hv]".
    rewrite (envs_lookup_split Δ i b _ HΔ). iDestruct "He" as "[#Hbij He]".
    iSpecialize ("He" with "Hbij").
    iApply sim_bij_store; [ | done | ]. { by rewrite intuitionistically_if_elim. }
    iApply sim_value. by iApply Hi.
  Qed.

  (* NOTE: we may want to actually keep the bijection assertion in context for some examples,
    where we need to use source stuckness for some runs of the target that access a deallocated location?
    In that case, change this lemma to not remove the fractional bijection assertion from the context.
    *)
  Lemma tac_bij_free Δ i K_t K_s b l_t l_s Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    envs_entails (envs_delete true i b Δ) (sim val_rel (fill K_t (Val $ LitV LitUnit)) (fill K_s (Val $ LitV LitUnit)) Φ) →
    envs_entails Δ (sim val_rel (fill K_t (Free (LitV l_t))) (fill K_s (Free (LitV l_s))) Φ).
  Proof.
    rewrite envs_entails_eq => Hl HΔ.
    rewrite -sim_bind. rewrite (envs_lookup_sound _ _ _ _ Hl).
    iIntros "[#bij He]". iPoseProof (HΔ with "He") as "He". rewrite intuitionistically_if_elim.
    iApply sim_bij_free; first done.
    iApply sim_value. by iApply "He".
  Qed.
End sim.

Tactic Notation "sim_load" ident(v_t) ident(v_s) "as" constr(H) :=
  to_sim;
  let solve_bij _ :=
    match goal with |- _ = Some (_, (?l_t ↔h ?l_s)%I) =>
      iAssumptionCore || fail "sim_load: cannot find" l_t "↔h" l_s
    end in
  let finish _ :=
    first [intros v_t v_s | fail 1 "sim_load: " v_t " or " v_s " not fresh"];
    pm_reduce; sim_finish in
  sim_pures;
  lazymatch goal with
  | |- envs_entails _ (sim ?vrel ?e_t ?e_s ?Φ) =>
    first
      [reshape_expr e_t ltac:(fun K_t e_t' =>
        reshape_expr e_s ltac:(fun K_s e_s' =>
          eapply (tac_bij_load _ _ _ H _ K_t K_s _ _ _)))
      |fail 1 "sim_load: cannot find 'Load' in" e_t " or " e_s];
    [ solve_bij ()
    | finish () ]
  | _ => fail "sim_load: not a 'sim'"
  end.
Tactic Notation "sim_load" ident(v_t) ident(v_s) :=
  sim_load v_t v_s as "?".

Tactic Notation "sim_store" :=
  to_sim;
  let Htmp := iFresh in
  let solve_bij _ :=
    match goal with |- _ = Some (_, (?l_t ↔h ?l_s)%I) =>
    iAssumptionCore || fail "sim_store: cannot find" l_t "↔h" l_s end in
  sim_pures;
  lazymatch goal with
  | |- envs_entails _ (sim ?vrel ?e_t ?e_s ?Φ) =>
    first
      [reshape_expr e_t ltac:(fun K_t e_t' =>
        reshape_expr e_s ltac:(fun K_s e_s' =>
          eapply (tac_bij_store _ _ _ K_t K_s _ _ _ _ _)))
      |fail 1 "sim_store: cannot find 'Store' in" e_t " or " e_s];
    [solve_bij ()
    | pm_reduce
    |pm_reduce; sim_finish]
  | _ => fail "sim_store: not a 'sim'"
  end.

Tactic Notation "sim_free" :=
  to_sim;
  let solve_bij _ :=
    match goal with |- _ = Some (_, (?l_t ↔h ?l_s)%I) =>
    iAssumptionCore || fail "sim_free: cannot find" l_t "↔h" l_s end in
  sim_pures;
  lazymatch goal with
  | |- envs_entails _ (sim ?vrel ?e_t ?e_s ?Φ) =>
    first
      [reshape_expr e_t ltac:(fun K_t e_t' =>
        reshape_expr e_s ltac:(fun K_s e_s' =>
          eapply (tac_bij_free _ _ _ K_t K_s _ _ _ _)))
      |fail 1 "sim_free: cannot find 'Free' in" e_t " or " e_s];
    [solve_bij ()
    |pm_reduce; sim_finish]
  | _ => fail "sim_free: not a 'sim'"
  end.
