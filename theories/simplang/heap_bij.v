From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From simuliris.base_logic Require Export gen_sim_heap gen_sim_prog.
From simuliris.simulation Require Import slsls lifting.
From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.
From simuliris.simplang Require Export class_instances primitive_laws heapbij.

From iris.prelude Require Import options.

(** * Instance of the SimpLang program logic that provides a means of establishing bijections on the heap. *)

Section fix_heap.
  Context `{heapbijG Σ} (π : thread_id).

  Global Program Instance heap_bij_inv : sheapInv Σ := {|
    sheap_inv _ _ _:= ∃ L, heap_bij_interp L (λ _ _ q, q = Some 1%Qp);
    sheap_ext_rel _ := val_rel;
  |}%I.
  Next Obligation. done. Qed.
  Global Instance : sheapInvSupportsAll.
  Proof. done. Qed.

  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{π} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.
  Local Notation "et '⪯' es [{ Φ }]" := (et ⪯{π} es [{Φ}])%I (at level 40, Φ at level 200) : bi_scope.

  Lemma sim_bij_load_sc l_t l_s Φ :
    l_t ↔h l_s -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ Val v_t ⪯ Val v_s [{ Φ }]) -∗
    (Load ScOrd (Val $ LitV $ LitLoc l_t)) ⪯ (Load ScOrd (Val $ LitV $ LitLoc l_s)) [{ Φ }].
  Proof.
    iIntros "#[Hbij %Hidx] Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & [%L Hinv]) [% %Hsafe]]".
    have [l[v[m[[<-] Hsome]]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(% & Halloc & Hclose)"; first last.
    iDestruct (alloc_rel_read true with "Halloc Hσ_s Hσ_t") as (????) "#?"; [done| naive_solver |].
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id.
    iSplitR "Hsim".
    - iExists L. by iApply "Hclose".
    - by iApply "Hsim".
  Qed.

  Lemma sim_bij_load_na2 l_t l_s Φ :
    l_t ↔h l_s -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ Val v_t ⪯ Val v_s [{ Φ }]) -∗
    (Load Na2Ord (Val $ LitV $ LitLoc l_t)) ⪯ (Load Na2Ord (Val $ LitV $ LitLoc l_s)) [{ Φ }].
  Proof.
    iIntros "#[Hbij %Hidx] Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & [%L Hinv]) [% %Hsafe]]".
    have [l[v[m[[<-] Hsome]]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(% & Halloc & Hclose)".
    iDestruct (alloc_rel_read true with "Halloc Hσ_s Hσ_t") as (????) "#Hv"; [done| naive_solver |]; simplify_eq.
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (alloc_rel_write with "Halloc Hσ_s Hσ_t Hv") as "[Halloc [Hσ_s Hσ_t]]"; [done|naive_solver|].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id.
    iSplitR "Hsim".
    - iExists L. by iApply "Hclose".
    - by iApply "Hsim".
  Qed.

  Lemma sim_bij_load_na1 l_t l_s Φ :
    l_t ↔h l_s -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ Val v_t ⪯ Val v_s [{ Φ }]) -∗
    (Load Na1Ord (Val $ LitV $ LitLoc l_t)) ⪯ (Load Na1Ord (Val $ LitV $ LitLoc l_s)) [{ Φ }].
  Proof.
    iIntros "#[Hbij %Hidx] Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & [%L Hinv]) [% %Hsafe]]".
    have [l[v[m[[<-] Hsome]]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(% & Halloc & Hclose)"; first last.
    iDestruct (alloc_rel_read true with "Halloc Hσ_s Hσ_t") as (????) "#Hv"; [done|naive_solver|].
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (alloc_rel_write with "Halloc Hσ_s Hσ_t Hv") as "[Halloc [Hσ_s Hσ_t]]"; [done|naive_solver|].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id.
    iSplitR "Hsim".
    - iExists _. by iApply "Hclose".
    - iApply sim_bij_load_na2; [|done]. by iSplit.
  Qed.

  Lemma sim_bij_load l_t l_s o Φ :
    l_t ↔h l_s -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ Val v_t ⪯ Val v_s [{ Φ }]) -∗
    (Load o (Val $ LitV $ LitLoc l_t)) ⪯ (Load o (Val $ LitV $ LitLoc l_s)) [{ Φ }].
  Proof. destruct o; [iApply sim_bij_load_sc | iApply sim_bij_load_na1 | iApply sim_bij_load_na2]. Qed.

  Lemma sim_bij_store_sc l_t l_s v_t v_s Φ :
    l_t ↔h l_s -∗
    val_rel v_t v_s -∗
    #() ⪯ #() [{ Φ }] -∗
    Store ScOrd (Val $ LitV (LitLoc l_t)) (Val v_t) ⪯ Store ScOrd (Val $ LitV (LitLoc l_s)) (Val v_s) [{ Φ }].
  Proof.
    iIntros "#[Hbij %Hidx] Hval Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & [%L Hinv]) [% %Hsafe]]".
    have [l[v[[<-] Hsome]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(% & Halloc & Hclose)".
    iDestruct (alloc_rel_read true with "Halloc Hσ_s Hσ_t") as (????) "#Hv"; [done|naive_solver|]; simplify_eq.
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (alloc_rel_write with "Halloc Hσ_s Hσ_t Hval") as "[Halloc [Hσ_s Hσ_t]]"; [done|naive_solver|].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id. iExists _. by iApply "Hclose".
  Qed.

  Lemma sim_bij_store_na2 l_t l_s v_t v_s Φ :
    l_t ↔h l_s -∗
    val_rel v_t v_s -∗
    #() ⪯ #() [{ Φ }] -∗
    Store Na2Ord (Val $ LitV (LitLoc l_t)) (Val v_t) ⪯ Store Na2Ord (Val $ LitV (LitLoc l_s)) (Val v_s) [{ Φ }].
  Proof.
    iIntros "#[Hbij %Hidx] Hval Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & [%L Hinv]) [% %Hsafe]]".
    have [l[v[[<-] Hsome]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(% & Halloc & Hclose)"; first last.
  Admitted.
  (*
    iDestruct (alloc_rel_read true with "Halloc Hσ_s Hσ_t") as (????) "#Hv"; [|naive_solver|].
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (alloc_rel_write with "Halloc Hσ_s Hσ_t Hval") as "[Halloc [Hσ_s Hσ_t]]"; [done|].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id.
    by iApply "Hclose".
  Qed.
*)
  Lemma sim_bij_store_na1 l_t l_s v_t v_s Φ :
    l_t ↔h l_s -∗
    val_rel v_t v_s -∗
    #() ⪯ #() [{ Φ }] -∗
    Store Na1Ord (Val $ LitV (LitLoc l_t)) (Val v_t) ⪯ Store Na1Ord (Val $ LitV (LitLoc l_s)) (Val v_s) [{ Φ }].
  Proof.
    iIntros "#[Hbij %Hidx] Hval Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & [%L Hinv]) [% %Hsafe]]".
    have [l[v[[<-] Hsome]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(% & Halloc & Hclose)"; first last.
    iDestruct (alloc_rel_read true with "Halloc Hσ_s Hσ_t") as (????) "#Hv"; [done|naive_solver|]; simplify_eq.
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (alloc_rel_write with "Halloc Hσ_s Hσ_t Hv") as "[Halloc [Hσ_s Hσ_t]]"; [done|naive_solver|].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id.
    iSplitR "Hsim Hval".
    - iExists _. by iApply "Hclose".
    - iApply (sim_bij_store_na2 with "[] Hval Hsim"). by iSplit.
  Qed.

  Lemma sim_bij_store l_t l_s v_t v_s o Φ :
    l_t ↔h l_s -∗
    val_rel v_t v_s -∗
    #() ⪯ #() [{ Φ }] -∗
    Store o (Val $ LitV (LitLoc l_t)) (Val v_t) ⪯ Store o (Val $ LitV (LitLoc l_s)) (Val v_s) [{ Φ }].
  Proof. destruct o; [iApply sim_bij_store_sc | iApply sim_bij_store_na1 | iApply sim_bij_store_na2]. Qed.

  Lemma sim_bij_free l_t l_s Φ n :
    l_t ↔h l_s -∗
    #() ⪯ #() [{ Φ }] -∗
    FreeN (Val $ LitV $ LitInt n) (Val $ LitV $ LitLoc l_t) ⪯ FreeN (Val $ LitV $ LitInt n) (Val $ LitV $ LitLoc l_s) [{ Φ }].
  Proof.
    iIntros "#[Hbij %Hidx] Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & [%L Hinv]) [% %Hsafe]]".
    have [m[?[[<-][[<-][??]]]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(% & Halloc & Hclose)"; first last.
  Admitted.
(*
    iDestruct "Halloc" as (p sts vs_t vs_s Hlen) "(Hl_t & Hl_s & Ha_t & Ha_s)".
    iDestruct (big_sepL2_length with "Hl_t") as %Hlent.
    iDestruct (big_sepL2_length with "Hl_s") as %Hlens.
    iDestruct (heap_freeable_inj with "Hσ_s Ha_s") as %[? Hl]; [done..|]. move: Hl => [?]. subst.

    iMod (heap_free with "Hσ_t Hl_t [Ha_t]") as (? Hlookup) "[Ha_t Hσ_t]"; [ by rewrite Hlen /= | by rewrite Hlen |].
    rewrite  Z2Nat.id in Hlookup; [| lia].
    iModIntro; iSplit; first by eauto with head_step lia.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (heap_free with "Hσ_s Hl_s [Ha_s]") as (_ _) "[Ha_s Hσ_s]";
      [ done | by rewrite -Hlens Hlent Hlen |].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    rewrite -Hlens Hlent Hlen !Z2Nat.id /=; [|lia]. iFrame.
    iApply "Hclose".
    iExists None, [], [], []. iFrame.
    iSplitR; [done|].
    iSplitR; [by iApply big_sepL2_nil|].
    iSplitR; [by iApply big_sepL2_nil|].
    by iApply big_sepL2_nil.
  Qed.
*)
  Lemma sim_bij_insertN l_t l_s vs_t vs_s e_t e_s n Φ :
    n > 0 →
    length vs_t = n →
    length vs_s = n →
    †l_t …t n -∗
    †l_s …s n -∗
    l_t ↦t∗ vs_t -∗
    l_s ↦s∗ vs_s -∗
    ([∗ list] vt;vs∈vs_t;vs_s, val_rel vt vs) -∗
    (l_t ↔h l_s -∗ e_t ⪯ e_s [{ Φ }]) -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros (Hn Ht Hs) "Hs_t Hs_s Hl_t Hl_s Hval Hsim". iApply sim_update_si.
    iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & [%L Hinv])".
    iMod (heap_bij_insertN with "Hinv Hl_t Hl_s Hval Hs_t Hs_s") as "[Hb #Ha]"; [done .. | ].
    iModIntro. iFrame. iDestruct ("Hsim" with "[//]") as "$". by iExists _.
  Qed.

  Lemma sim_bij_insert l_t l_s v_t v_s e_t e_s Φ :
    †l_t …t 1 -∗
    †l_s …s 1 -∗
    l_t ↦t v_t -∗
    l_s ↦s v_s -∗
    val_rel v_t v_s -∗
    (l_t ↔h l_s -∗ e_t ⪯ e_s [{ Φ }]) -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "Hs_t Hs_s Hl_t Hl_s Hv".
    iApply (sim_bij_insertN _ _ [v_t] [v_s] with "Hs_t Hs_s [Hl_t] [Hl_s] [Hv]"); [lia | done | done | | | ].
    - by rewrite heap_mapsto_vec_singleton.
    - by rewrite heap_mapsto_vec_singleton.
    - by iApply big_sepL2_singleton.
  Qed.
End fix_heap.

(** ** Extension of the proofmode *)
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.bi Require Import bi derived_laws.
From simuliris.simplang Require Export proofmode.


(** New lemmas for the new tactics *)
Section sim.
  Context `{heapbijG Σ} (π : thread_id).

  Import bi.

  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{π} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

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

  Lemma tac_bij_load Δ i j b K_t K_s l_t l_s o Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    (∀ v_t v_s,
      match envs_app true (Esnoc Enil j (val_rel v_t v_s)) Δ with
      | Some Δ' =>
          envs_entails Δ' (sim_expr Φ π (fill K_t (Val v_t)) (fill K_s (Val v_s)))
      | None => False
      end) →
    envs_entails Δ (sim_expr Φ π (fill K_t (Load o (LitV l_t))) (fill K_s (Load o (LitV l_s))))%I.
  Proof.
    rewrite envs_entails_eq=> ? Hi.
    rewrite -sim_expr_bind. eapply wand_apply; first exact: sim_bij_load.
    rewrite envs_lookup_split //; simpl.
    iIntros "[#Ha He]". iSpecialize ("He" with "Ha").
    rewrite intuitionistically_if_elim. iSplitR; first done.
    iIntros (v_t' v_s') "#Hv". specialize (Hi v_t' v_s').
    destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction].
    iApply sim_expr_base.
    iApply Hi. rewrite envs_app_sound //; simpl. iApply "He"; eauto.
  Qed.

  Lemma tac_bij_store Δ i K_t K_s b l_t l_s v_t' v_s' o Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    envs_entails Δ (val_rel v_t' v_s') →
    envs_entails Δ (sim_expr Φ π (fill K_t (Val $ LitV LitUnit)) (fill K_s (Val $ LitV LitUnit))) →
    envs_entails Δ (sim_expr Φ π (fill K_t (Store o (LitV l_t) (Val v_t'))) (fill K_s (Store o (LitV l_s) (Val v_s')))).
  Proof.
    rewrite envs_entails_eq => HΔ.
    rewrite (persistent_persistently_2 (val_rel _ _)).
    intros Hv%persistently_entails_r Hi.
    rewrite -sim_expr_bind.
    iIntros "He". iPoseProof (Hv with "He") as "[He #Hv]".
    rewrite (envs_lookup_split Δ i b _ HΔ). iDestruct "He" as "[#Hbij He]".
    iSpecialize ("He" with "Hbij").
    iApply sim_bij_store; [ | done | ]. { by rewrite intuitionistically_if_elim. }
    iApply sim_expr_base. by iApply Hi.
  Qed.

  (* NOTE: we may want to actually keep the bijection assertion in context for some examples,
    where we need to use source stuckness for some runs of the target that access a deallocated location?
    In that case, change this lemma to not remove the fractional bijection assertion from the context.
    *)
  Lemma tac_bij_freeN Δ i K_t K_s b l_t l_s n Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    envs_entails (envs_delete true i b Δ) (sim_expr Φ π (fill K_t (Val $ LitV LitUnit)) (fill K_s (Val $ LitV LitUnit))) →
    envs_entails Δ (sim_expr Φ π (fill K_t (FreeN (Val $ LitV $ LitInt n) (LitV l_t))) (fill K_s (FreeN (Val $ LitV $ LitInt n) (LitV l_s)))).
  Proof.
    rewrite envs_entails_eq => Hl HΔ.
    rewrite -sim_expr_bind. rewrite (envs_lookup_sound _ _ _ _ Hl).
    iIntros "[#bij He]". iPoseProof (HΔ with "He") as "He". rewrite intuitionistically_if_elim.
    iApply sim_bij_free; first done.
    iApply sim_expr_base. by iApply "He".
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
  sim_pures_int;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?Φ ?π ?e_t ?e_s) =>
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
  sim_pures_int;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?Φ ?π ?e_t ?e_s) =>
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
  sim_pures_int;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?Φ ?π ?e_t ?e_s) =>
    first
      [reshape_expr e_t ltac:(fun K_t e_t' =>
        reshape_expr e_s ltac:(fun K_s e_s' =>
          eapply (tac_bij_freeN _ _ _ K_t K_s _ _ _ _ _)))
      |fail 1 "sim_free: cannot find 'FreeN' in" e_t " or " e_s];
    [solve_bij ()
    |pm_reduce; sim_finish]
  | _ => fail "sim_free: not a 'sim'"
  end.
