From simuliris.simulation Require Import slsls lifting.
From simuliris.stacked_borrows Require Import proofmode tactics.
From simuliris.stacked_borrows Require Import parallel_subst primitive_laws log_rel wf.
From iris.prelude Require Import options.

Section log_rel.
  Context `{!sborGS Σ}.

  Lemma scalar_wf_sound sc : scalar_wf sc → ⊢ sc_rel sc sc.
  Proof. intros Hwf. destruct sc; auto. done. Qed.

  Lemma value_wf_sound v : value_wf v → ⊢ value_rel v v.
  Proof.
    intros Hwf. iInduction v as [|a v] "IH"; first by rewrite /value_rel /=.
    apply Forall_cons_1 in Hwf as [H1 H2]. rewrite /value_rel /=. iSplit.
    - by iApply scalar_wf_sound.
    - by iApply "IH".
  Qed.

  Lemma log_rel_var x : ⊢ log_rel (Var x) (Var x).
  Proof.
    iIntros (? xs) "!# Hs"; simpl.
    iDestruct (subst_map_rel_lookup x with "Hs") as (v_t v_s Hv) "Hrel"; first set_solver.
    rewrite !lookup_fmap Hv /=. sim_val. by iFrame.
  Qed.

  Local Tactic Notation "smart_sim_bind" uconstr(ctx_t) uconstr(ctx_s) uconstr(Hp) :=
    sim_bind_val ctx_t ctx_s;
    iApply (sim_wand with Hp).

  Lemma log_rel_let x e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Let x e1_t e2_t) (Let x e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "#Hv". sim_pures. rewrite !subst'_subst_map.
    rewrite -(binder_insert_fmap fst (v_t, v_s)).
    rewrite -(binder_insert_fmap snd (v_t, v_s)).
    iApply ("IH2" with "[]").
    iApply (subst_map_rel_insert with "[] Hv").
    iApply (subst_map_rel_weaken with "[$]").
    destruct x as [|x]; first set_solver.
    apply elem_of_subseteq=>x'.
    destruct (decide (x = x')) as [<-|Hne]; set_solver.
  Qed.

  Local Lemma call_not_val v1 v2 : language.to_val (Call v1 v2) = None.
  Proof.
    rewrite /language.to_val /language.to_class; cbn.
    destruct to_fname; [destruct to_result | ]; done.
  Qed.

  Lemma log_rel_call e1_t e1_s e2_t e2_s :
    (∀ π v_t v_s, ext_rel π v_t v_s ⊣⊢ rrel v_t v_s) →
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Call e1_t e2_t) (Call e1_s e2_s).
  Proof.
    iIntros (Hext) "#IH1 #IH2". iIntros (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "#Hv1".
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "#Hv2".
  Abort.

  Lemma log_rel_binop e1_t e1_s e2_t e2_s o :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (BinOp o e1_t e2_t) (BinOp o e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "Hv2".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "Hv1".
  Abort.

  Lemma log_rel_result v_t v_s :
    rrel v_t v_s -∗ log_rel (of_result v_t) (of_result v_s).
  Proof.
    iIntros "#Hv" (? xs) "!# #Hs"; simpl. rewrite !subst_map_of_result.
    sim_val ; by iFrame.
  Qed.
End log_rel.
