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
    intros Hwf. iInduction v as [|a v] "IH"; first by iApply value_rel_empty.
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

  Tactic Notation "val_discr_source" constr(H) :=
    let H' := iFresh in
    first [
      iPoseProof (rrel_singleton_source with H) as (? ->) H';
      first [iPoseProof (sc_rel_ptr_source with H') as "[-> ?]" |
            iPoseProof (sc_rel_fnptr_source with H') as "->" |
            iPoseProof (sc_rel_int_source with H') as "->" |
            iPoseProof (sc_rel_cid_source with H') as "->" |
            iPoseProof (sc_rel_poison_target with H') as "->"
            ] |
      iPoseProof (rrel_place_source with H) as (->) H' |
      iPoseProof (rrel_value_source with H) as (? ->) H'
    ];
    try iClear H; try iRename H' into H.

  Lemma log_rel_call e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Call e1_t e2_t) (Call e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2". iIntros (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "#Hv1".
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "#Hv2".
    discr_source; first by apply call_not_val. val_discr_source "Hv2".
    iApply (sim_call with "Hv1"). iIntros (??) "Hr". by iApply lift_post_val.
  Qed.

  Local Ltac solve_rrel_refl :=
    sim_val;
    first [
      iApply rrel_value_rel;
      first [iApply value_rel_poison|
            iApply value_rel_int |
            iApply value_rel_fnptr |
            iApply value_rel_callid |
            iApply value_rel_ptr
           ] |
      iApply rrel_place
    ];
    eauto.

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
    destruct o; sim_pures;
      try (discr_source; val_discr_source "Hv1"; val_discr_source "Hv2";
            sim_pures; solve_rrel_refl).
    (* TODO : irred_unless_eq doesn't work here, because of scoping *)
    admit.
  Admitted.

  Lemma log_rel_proj e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Proj e1_t e2_t) (Proj e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "Hv2".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "Hv1".
    discr_source. val_discr_source "Hv2". val_discr_source "Hv1".
    iDestruct (value_rel_length with "Hv1") as %EqL.
    iDestruct (value_rel_lookup with "Hv1") as (sc_t sc_s Eqt Eqs) "Hsc".
    {  rewrite EqL. eapply Nat2Z.inj_lt, lookup_lt_Some; eauto. }
    sim_pures.
  Admitted.

  Lemma log_rel_conc e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Conc e1_t e2_t) (Conc e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "Hv2".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "Hv1".
    discr_source. val_discr_source "Hv2". val_discr_source "Hv1".
    sim_pures. sim_val.
    rewrite rrel_value_rel. by iApply (value_rel_app with "Hv1 Hv2").
  Qed.

  Lemma log_rel_deref e_t e_s T :
    log_rel e_t e_s -∗ log_rel (Deref e_t T) (Deref e_s T).
  Proof.
    iIntros "#IH" (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "Hv".
    discr_source. val_discr_source "Hv".
    sim_pures. solve_rrel_refl.
  Qed.

  Lemma log_rel_ref e_t e_s :
    log_rel e_t e_s -∗ log_rel (Ref e_t) (Ref e_s).
  Proof.
    iIntros "#IH" (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "Hv".
    discr_source. val_discr_source "Hv".
    sim_pures. solve_rrel_refl.
  Qed.

  Lemma log_rel_copy e_t e_s :
    log_rel e_t e_s -∗ log_rel (Copy e_t) (Copy e_s).
  Proof.
    iIntros "#IH" (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "Hv".
    discr_source. val_discr_source "Hv".
    iApply (sim_copy_public with "[Hv]"). { by iApply rrel_place. }
    iIntros (v_t v_s) "Hv". sim_val. done.
  Qed.

  Lemma log_rel_write e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (Write e1_t e2_t) (Write e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "Hv2".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "Hv1".
  Admitted.

  Lemma log_rel_retag e1_t e1_s e2_t e2_s pk T k :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (Retag e1_t e2_t pk T k) (Retag e1_s e2_s pk T k).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "Hv2".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "Hv1".
    discr_source. val_discr_source "Hv1". val_discr_source "Hv2".
    iApply (sim_retag_public with "[-]"). { by iApply value_rel_ptr. }
    iIntros (t) "Hv". sim_val. done.
  Qed.

  Lemma log_rel_while e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (While e1_t e2_t) (While e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs"; simpl.
    iApply (sim_while_while emp%I with "[//]").
    iModIntro; iIntros "_".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "Hv".
  Admitted.

  Lemma log_rel_case e_t e_s el_t el_s :
    log_rel e_t e_s -∗
    ([∗ list] e_t';e_s' ∈ el_t;el_s, log_rel e_t' e_s') -∗
    log_rel (Case e_t el_t) (Case e_s el_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "#Hv".
    discr_source. val_discr_source "Hv".
  Admitted.

  Lemma log_rel_fork e_t e_s :
    (∀ e_s e_t π Ψ,
     (#[☠] ⪯{π} #[☠] [{ Ψ }]) -∗
     (∀ π', e_t ⪯{π'} e_s {{ λ v_t v_s, rrel v_t v_s }}) -∗
     Fork e_t ⪯{π} Fork e_s [{ Ψ }]) →
    log_rel e_t e_s -∗ log_rel (Fork e_t) (Fork e_s).
  Proof.
    iIntros (Hfork). iIntros "#IH" (? xs) "!# #Hs"; simpl.
    iApply Hfork. { solve_rrel_refl. }
    iIntros (?). iApply (sim_wand with "(IH [])"); eauto.
  Qed.

  Lemma log_rel_alloc T :
    ⊢ log_rel (Alloc T) (Alloc T).
  Proof.
    iIntros (? xs) "!# #Hs"; simpl. iApply sim_alloc_public.
    iIntros (t l) "Hp Hr". sim_val. by iFrame.
  Qed.

  Lemma log_rel_free e_t e_s :
    log_rel e_t e_s ⊢ log_rel (Free e_t) (Free e_s).
  Proof.
    iIntros "#IH" (? xs) "!# #Hs"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH [])".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "Hv".
    discr_source. val_discr_source "Hv".
    iApply (sim_free_public with "[Hv]"). { by iApply rrel_place. }
    solve_rrel_refl.
  Qed.

  Lemma log_rel_result v_t v_s :
    rrel v_t v_s ⊢ log_rel (of_result v_t) (of_result v_s).
  Proof.
    iIntros "#Hv" (? xs) "!# #Hs"; simpl. rewrite !subst_map_of_result.
    sim_val ; by iFrame.
  Qed.
End log_rel.

Definition expr_head_wf (e : expr_head) : Prop :=
  match e with
  | ValHead v => value_wf v
  | InitCallHead => False   (* administrative *)
  | EndCallHead => False    (* administrative *)
  | PlaceHead _ _ _ => False (* no literal pointers *)
  | _ => True
  end.

Notation expr_wf := (gen_expr_wf expr_head_wf).
Notation ectx_wf := (gen_ectx_wf expr_head_wf).
Notation ctx_wf := (gen_ctx_wf expr_head_wf).

Section refl.
  Context `{!sborGS Σ}.

  Theorem sb_log_rel_structural : log_rel_structural expr_head_wf.
  Proof.
    intros e_t e_s ?? Hwf Hs. iIntros "IH".
    destruct e_s, e_t => //; simpl in Hs; simplify_eq.
    all: try iDestruct "IH" as "[IH IH1]".
    all: try iDestruct "IH1" as "[IH1 IH2]".
    all: try iDestruct "IH2" as "[IH2 IH3]".
    - (* Value *)
      iApply (log_rel_result (ValR _) (ValR _)). by iApply value_wf_sound.
    - (* Var *)
      by iApply log_rel_var.
    - (* Call *)
      by iApply (log_rel_call with "IH IH1").
    - (* Proj *)
      by iApply (log_rel_proj with "IH IH1").
    - (* Conc *)
      by iApply (log_rel_conc with "IH IH1").
    - (* BinOp *)
      by iApply (log_rel_binop with "IH IH1").
    - (* Deref *)
      by iApply (log_rel_deref with "IH").
    - (* Ref *)
      by iApply (log_rel_ref with "IH").
    - (* Copy *)
      by iApply (log_rel_copy with "IH").
    - (* Write *)
      by iApply (log_rel_write with "IH IH1").
    - (* Alloc *)
      by iApply log_rel_alloc.
    - (* Free *)
      by iApply log_rel_free.
    - (* Retag *)
      by iApply (log_rel_retag with "IH IH1").
    - (* Let *)
      by iApply (log_rel_let with "IH IH1").
    - (* Case *)
      by iApply (log_rel_case with "IH IH1").
    - (* Fork *)
      iApply (log_rel_fork with "IH").
      iIntros (????) "Hsim Hfork". iApply (sim_fork with "Hsim").
      iIntros (?). iApply (sim_wand with "[Hfork]"). { by iApply "Hfork". }
      iIntros (??) "$".
    - (* While *)
      by iApply (log_rel_while with "IH IH1").
  Qed.

  Corollary log_rel_refl e :
    expr_wf e →
    ⊢ log_rel e e.
  Proof.
    intros ?. iApply log_rel_refl; first by apply sb_log_rel_structural. done.
  Qed.

  Corollary log_rel_ctx C e_t e_s :
    ctx_wf C →
    log_rel e_t e_s -∗ log_rel (fill_ctx C e_t) (fill_ctx C e_s).
  Proof.
    intros ?. iApply log_rel_ctx; first by apply sb_log_rel_structural. done.
  Qed.

  Corollary log_rel_ectx K e_t e_s :
    ectx_wf K →
    log_rel e_t e_s -∗ log_rel (fill K e_t) (fill K e_s).
  Proof.
    intros ?. iApply log_rel_ectx; first by apply sb_log_rel_structural. done.
  Qed.

  Lemma log_rel_closed_1 e_t e_s π :
    free_vars e_t ∪ free_vars e_s = ∅ →
    log_rel e_t e_s ⊢ e_t ⪯{π} e_s {{ λ v_t v_s, rrel v_t v_s }}.
  Proof.
    iIntros (?) "#Hrel".
    iApply sim_mono; last iApply (log_rel_closed_1 with "Hrel"); [|done..].
    iIntros (v_t v_s) "$".
  Qed.

End refl.
