From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst heap_bij.

(** * Reflexivity theorem for the heap bijection value relation *)

(** map_ForallI *)
Definition map_ForallI `{Lookup K A M} `(P : K → A → iProp Σ) : M → iProp Σ :=
    (λ m, ∀ i x, ⌜m !! i = Some x⌝ → P i x)%I.
Section map_Forall.
  Context `{FinMap K M}.
  Context {A} {Σ} (P : K → A → iProp Σ).
  Implicit Types m : M A.

  Lemma map_ForallI_empty : ⊢ map_ForallI P (∅ : M A).
  Proof. iIntros (i x). rewrite lookup_empty. by iIntros "%". Qed.
  Lemma map_ForallI_insert_2 m i x :
    ⊢ P i x -∗ map_ForallI P m -∗ map_ForallI P (<[i:=x]>m).
  Proof.
    iIntros "? Hm" (j y); rewrite lookup_insert_Some.
    iIntros "%Hv". destruct Hv as [[-> ->] | [Hneq Hs]]; first done.
    by iApply "Hm".
  Qed.
End map_Forall.

(** We will only be able to show reflexivity for "well-formed" terms. *)

Section refl.
  Context `{sbijG Σ}.

  Fixpoint val_wf (v : val) : Prop :=
    match v with
    | LitV (LitLoc l) => False (* no literal locations allowed :( *)
    | LitV _ => True
    | PairV v1 v2 => val_wf v1 ∧ val_wf v2
    | InjLV v => val_wf v
    | InjRV v => val_wf v
    end.

  Fixpoint expr_wf (e : expr) : Prop :=
    match e with
    | Val v => val_wf v
    | Var x => True
    | Let b e1 e2 => expr_wf e1 ∧ expr_wf e2
    | Call e1 e2 => expr_wf e1 ∧ expr_wf e2
    | UnOp op e => expr_wf e
    | BinOp op e1 e2 => expr_wf e1 ∧ expr_wf e2
    | If e1 e2 e3 => expr_wf e1 ∧ expr_wf e2 ∧ expr_wf e3
    | While e1 e2 => expr_wf e1 ∧ expr_wf e2
    | Pair e1 e2 => expr_wf e1 ∧ expr_wf e2
    | Fst e => expr_wf e
    | Snd e => expr_wf e
    | InjL e => expr_wf e
    | InjR e => expr_wf e
    | Match e x1 e1 x2 e2 => expr_wf e ∧ expr_wf e1 ∧ expr_wf e2
    | Fork e => expr_wf e
    | AllocN e1 e2 => expr_wf e1 ∧ expr_wf e2
    | FreeN e1 e2 => expr_wf e1 ∧ expr_wf e2
    | Load o e => expr_wf e
    | Store o e1 e2 => expr_wf e1 ∧ expr_wf e2
    | CmpXchg e1 e2 e3 => False   (* currently not supported *)
    | FAA e1 e2 => False          (* currently not supported *)
    end.

  (** Well-formed substitutions in source and target*)

  Definition subst_map_rel (map : gmap string (val * val)) :=
    map_ForallI (λ _ '(v_t, v_s), val_rel v_t v_s) map.

  Instance subst_map_rel_pers map : Persistent (subst_map_rel map).
  Proof.
    rewrite /subst_map_rel /map_ForallI.
    apply bi.forall_persistent => x. apply bi.forall_persistent; intros [a b].
    apply _.
  Qed.

  Lemma subst_map_rel_insert map v_t v_s b :
    val_rel v_t v_s -∗
    subst_map_rel map -∗
    subst_map_rel (binder_insert b (v_t, v_s) map).
  Proof.
    iIntros "Hv Hs". destruct b; first done. by iApply (map_ForallI_insert_2 with "[Hv] Hs").
  Qed.

  Lemma subst_map_rel_empty : ⊢ subst_map_rel ∅.
  Proof. apply map_ForallI_empty. Qed.

  Definition sem_wf e_t e_s : iProp Σ :=
    ∀ π (map : gmap string (val * val)),
      subst_map_rel map -∗ subst_map (fst <$> map) e_t ⪯{π, val_rel} subst_map (snd <$> map) e_s {{ val_rel }}.

  Lemma val_wf_sound v : val_wf v → ⊢ val_rel v v.
  Proof.
    intros Hv.
    iInduction v as [[] | | | ] "IH"; try by (simpl; try iApply "IH").
    simpl. destruct Hv as [H1 H2]. iSplit; [by iApply "IH" | by iApply "IH1"].
  Qed.

  Lemma call_not_val v1 v2 : language.to_val (Call v1 v2) = None.
  Proof.
    rewrite /language.to_val /language.to_class; cbn.
    destruct to_fname; [destruct to_val | ]; done.
  Qed.

  Lemma val_rel_val_is_unboxed v_t v_s : val_rel v_t v_s -∗ ⌜val_is_unboxed v_t ↔ val_is_unboxed v_s⌝.
  Proof.
    iIntros "Hv".
    destruct v_s as [[] | | | ]; val_discr_source "Hv"; [ done .. | |done | | |].
    - by iPoseProof (val_rel_loc_source with "Hv") as (?) "(-> & _)".
    - by iPoseProof (val_rel_pair_source with "Hv") as (??) "(-> & Hv1 & Hv2)".
    - iPoseProof (val_rel_injl_source with "Hv") as (?) "(-> & Hv)".
      destruct v_s as [[] | | | ]; val_discr_source "Hv"; [done.. | | done | | |].
      + by iPoseProof (val_rel_loc_source with "Hv") as (?) "(-> & _)".
      + by iPoseProof (val_rel_pair_source with "Hv") as (??) "(-> & Hv1 & Hv2)".
      + by iPoseProof (val_rel_injl_source with "Hv") as (?) "(-> & Hv)".
      + by iPoseProof (val_rel_injr_source with "Hv") as (?) "(-> & Hv)".
    - iPoseProof (val_rel_injr_source with "Hv") as (?) "(-> & Hv)".
      destruct v_s as [[] | | | ]; val_discr_source "Hv"; [done.. | | done | | |].
      + by iPoseProof (val_rel_loc_source with "Hv") as (?) "(-> & _)".
      + by iPoseProof (val_rel_pair_source with "Hv") as (??) "(-> & Hv1 & Hv2)".
      + by iPoseProof (val_rel_injl_source with "Hv") as (?) "(-> & Hv)".
      + by iPoseProof (val_rel_injr_source with "Hv") as (?) "(-> & Hv)".
  Qed.

  (* pull out compatibility lemmas as Iris entailment *)

  Local Tactic Notation "smart_sim_bind" uconstr(ctx_t) uconstr(ctx_s) uconstr(Hp) :=
    sim_bind ctx_t ctx_s;
    iApply (sim_wand with Hp).

  Lemma sem_wf_var x : ⊢ sem_wf (Var x) (Var x).
  Proof.
    iIntros (? xs) "#Hs"; simpl.
    rewrite !lookup_fmap. destruct (xs !! x) as [[v_t v_s] | ] eqn:Heq; simpl.
    { sim_pures; sim_val; iModIntro. by iApply ("Hs" $! x (v_t, v_s)). }
    source_stuck_prim.
  Qed.

  Lemma sem_wf_let x e1_t e1_s e2_t e2_s :
    sem_wf e1_t e1_s -∗ sem_wf e2_t e2_s -∗ sem_wf (Let x e1_t e2_t) (Let x e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 Hs)".
    iIntros (v_t v_s) "#Hv". sim_pures. rewrite !subst'_subst_map.
    rewrite -(binder_insert_fmap fst (v_t, v_s)).
    rewrite -(binder_insert_fmap snd (v_t, v_s)).
    iApply "IH2". by iApply (subst_map_rel_insert with "Hv").
  Qed.

  Lemma sem_wf_call e1_t e1_s e2_t e2_s :
    sem_wf e1_t e1_s -∗ sem_wf e2_t e2_s -∗ sem_wf (Call e1_t e2_t) (Call e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 Hs)".
    iIntros (v_t1 v_s1) "#Hv1".
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 Hs)".
    iIntros (v_t2 v_s2) "#Hv2".
    discr_source; first by apply call_not_val. val_discr_source "Hv2".
    iApply sim_call; done.
  Qed.

  Lemma sem_wf_unop e_t e_s o :
    sem_wf e_t e_s -∗ sem_wf (UnOp o e_t) (UnOp o e_s).
  Proof.
    iIntros "IH" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH Hs)".
    iIntros (v_t v_s) "#Hv". destruct o; sim_pures; discr_source; val_discr_source "Hv"; by sim_pures; sim_val.
  Qed.

  Lemma sem_wf_binop e1_t e1_s e2_t e2_s o :
    sem_wf e1_t e1_s -∗ sem_wf e2_t e2_s -∗ sem_wf (BinOp o e1_t e2_t) (BinOp o e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 Hs)".
    iIntros (v_t2 v_s2) "Hv2".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 Hs)".
    iIntros (v_t1 v_s1) "Hv1".
    destruct o; sim_pures; discr_source; val_discr_source "Hv1"; val_discr_source "Hv2"; sim_pures; [sim_val; done .. | | ].
    - iAssert (⌜vals_compare_safe v_t1 v_t2⌝)%I as "%".
      { iPoseProof (val_rel_val_is_unboxed with "Hv1") as "%".
        iPoseProof (val_rel_val_is_unboxed with "Hv2") as "%".
        iPureIntro. by rewrite /vals_compare_safe H1 H2.
      }
      case_bool_decide; subst.
      * iPoseProof (val_rel_inj with "Hv1 Hv2") as "->".
        sim_pures; sim_val. case_bool_decide; done.
      * sim_pures; sim_val. case_bool_decide; subst; last done.
        by iPoseProof (val_rel_func with "Hv1 Hv2") as "->".
    - iPoseProof (val_rel_loc_source with "Hv1") as (l_t) "(-> & Hl)".
      sim_pures. sim_val. iModIntro; cbn.
      by iApply heap_bij_loc_shift.
  Qed.

  Lemma sem_wf_if e1_t e1_s e2_t e2_s e3_t e3_s :
    sem_wf e1_t e1_s -∗ sem_wf e2_t e2_s -∗ sem_wf e3_t e3_s -∗ sem_wf (If e1_t e2_t e3_t) (If e1_s e2_s e3_s).
  Proof.
    iIntros "IH1 IH2 IH3" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 Hs)".
    iIntros (v_t v_s) "Hv".
    discr_source. val_discr_source "Hv". destruct x; sim_pures.
    + iApply ("IH2" with "Hs").
    + iApply ("IH3" with "Hs").
  Qed.

  Lemma sem_wf_while e1_t e1_s e2_t e2_s :
    (□ sem_wf e1_t e1_s) -∗ (□ sem_wf e2_t e2_s) -∗ sem_wf (While e1_t e2_t) (While e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "#Hs"; simpl.
    iApply (sim_while_while _ _ _ _ _ _ (True)%I with "[//]").
    iModIntro; iIntros "_".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 Hs)".
    iIntros (v_t v_s) "Hv".
    discr_source. val_discr_source "Hv". destruct x; sim_pures.
    + smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 Hs)".
      iIntros (? ?) "_"; sim_pures. iApply sim_expr_base. iRight. by eauto.
    + iApply sim_expr_base. iLeft. iExists #(), #(); eauto.
  Qed.

  Lemma sem_wf_pair e1_t e1_s e2_t e2_s :
    sem_wf e1_t e1_s -∗ sem_wf e2_t e2_s -∗ sem_wf (Pair e1_t e2_t) (Pair e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 Hs)".
    iIntros (v_t2 v_s2) "Hv2".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 Hs)".
    iIntros (v_t1 v_s1) "Hv1".
    sim_pures; sim_val. iModIntro; iSplit; eauto.
  Qed.

  Lemma sem_wf_fst e_t e_s :
    sem_wf e_t e_s -∗ sem_wf (Fst e_t) (Fst e_s).
  Proof.
    iIntros "IH" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH Hs)".
    iIntros (v_t v_s) "Hv".
    discr_source. iPoseProof (val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; by sim_pures; sim_val.
  Qed.
  Lemma sem_wf_snd e_t e_s :
    sem_wf e_t e_s -∗ sem_wf (Snd e_t) (Snd e_s).
  Proof.
    iIntros "IH" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH Hs)".
    iIntros (v_t v_s) "Hv".
    discr_source. iPoseProof (val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; by sim_pures; sim_val.
  Qed.

  Lemma sem_wf_injl e_t e_s :
    sem_wf e_t e_s -∗ sem_wf (InjL e_t) (InjL e_s).
  Proof.
    iIntros "IH" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH Hs)".
    iIntros (v_t v_s) "Hv"; by sim_pures; sim_val.
  Qed.
  Lemma sem_wf_injr e_t e_s :
    sem_wf e_t e_s -∗ sem_wf (InjR e_t) (InjR e_s).
  Proof.
    iIntros "IH" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH Hs)".
    iIntros (v_t v_s) "Hv"; by sim_pures; sim_val.
  Qed.

  Lemma sem_wf_match e_t e_s e1_t e1_s e2_t e2_s x1 x2 :
    sem_wf e_t e_s -∗ sem_wf e1_t e1_s -∗ sem_wf e2_t e2_s -∗ sem_wf (Match e_t x1 e1_t x2 e2_t) (Match e_s x1 e1_s x2 e2_s).
  Proof.
    iIntros "IH IH1 IH2" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s)  "(IH Hs)".
    iIntros (v_t v_s) "#Hv".
    discr_source.
    + iPoseProof (val_rel_injl_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
      rewrite !subst'_subst_map.
      rewrite -(binder_insert_fmap fst (v_t', x)).
      rewrite -(binder_insert_fmap snd (v_t', x)).
      iApply "IH1". by iApply subst_map_rel_insert.
    + iPoseProof (val_rel_injr_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
      rewrite !subst'_subst_map.
      rewrite -(binder_insert_fmap fst (v_t', x)).
      rewrite -(binder_insert_fmap snd (v_t', x)).
      iApply "IH2". by iApply subst_map_rel_insert.
  Qed.

  Lemma sem_wf_fork e_t e_s :
    sem_wf e_t e_s -∗ sem_wf (Fork e_t) (Fork e_s).
  Proof.
    iIntros "IH" (? xs) "#Hs"; simpl.
    iApply sim_fork; first by sim_pures; sim_val. iIntros (?). sim_pures.
    iApply (sim_wand with "(IH Hs)"). eauto.
  Qed.

  Lemma sem_wf_allocN e1_t e1_s e2_t e2_s :
    sem_wf e1_t e1_s -∗ sem_wf e2_t e2_s -∗ sem_wf (AllocN e1_t e2_t) (AllocN e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 Hs)". iIntros (v_t v_s) "Hv".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 Hs)". iIntros (v_t' v_s') "Hv'".
    discr_source. val_discr_source "Hv'".
    target_alloc l_t as "Hl_t" "Ha_t"; first done.
    source_alloc l_s as "Hl_s" "Ha_s"; first done.
    iApply (sim_bij_insertN with "Ha_t Ha_s Hl_t Hl_s [Hv]"); [lia | by rewrite replicate_length.. | | ].
    { iDestruct "Hv" as "#Hv". rewrite /vrel_list.
      rewrite big_sepL2_replicate_l; last by rewrite replicate_length.
      generalize (Z.to_nat x) => n.
      iInduction n as [] "IHn"; cbn; first done. iFrame "Hv IHn".
    }
    iIntros "Hv". sim_pures. sim_val. done.
  Qed.

  Lemma sem_wf_freeN e1_t e1_s e2_t e2_s :
    sem_wf e1_t e1_s -∗ sem_wf e2_t e2_s -∗ sem_wf (FreeN e1_t e2_t) (FreeN e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 Hs)". iIntros (v_t v_s) "Hv".
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 Hs)". iIntros (v_t' v_s') "Hv'".
    discr_source. iPoseProof (val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
    iPoseProof (val_rel_litint_source with "Hv'") as "->".
    by sim_free; sim_val.
  Qed.

  Lemma sem_wf_load o e_t e_s :
    sem_wf e_t e_s -∗ sem_wf (Load o e_t) (Load o e_s).
  Proof.
    iIntros "IH" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH Hs)".
    iIntros (v_t v_s) "Hv". discr_source. iPoseProof (val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
    by sim_load v_t v_s as "Hv"; sim_val.
  Qed.

  Lemma sem_wf_store o e1_t e1_s e2_t e2_s :
    sem_wf e1_t e1_s -∗ sem_wf e2_t e2_s -∗ sem_wf (Store o e1_t e2_t) (Store o e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs) "#Hs"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 Hs)".
    iIntros (v_t v_s) "Hv". (* FIXME: fix printing *)
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 Hs)".
    iIntros (v_t' v_s') "Hv'".
    discr_source. iPoseProof (val_rel_loc_source with "Hv'") as (l_t) "(-> & Hrel)".
    by sim_store; [done | sim_val].
  Qed.

  Lemma sem_wf_val v_t v_s :
    val_rel v_t v_s -∗ sem_wf (Val v_t) (Val v_s).
  Proof. iIntros "Hv" (? xs) "#Hs"; simpl. by sim_val. Qed.

  Lemma sem_wf_empty e_t e_s π : sem_wf e_t e_s -∗ e_t ⪯{π, val_rel} e_s {{ val_rel }}.
  Proof.
    iIntros "Hwf". iSpecialize ("Hwf" $! π ∅ subst_map_rel_empty).
    by rewrite !fmap_empty !subst_map_empty.
  Qed.

  Lemma expr_wf_sound e : expr_wf e → ⊢ sem_wf e e.
  Proof.
    intros Hwf. iInduction e as [ ] "IH" forall (Hwf); iIntros (? xs) "#Hs"; simpl.
    - (* Val *) iApply sem_wf_val; [by iApply val_wf_sound | done].
    - (* Var *) by iApply sem_wf_var.
    - (* Let *) destruct Hwf as [Hwf1 Hwf2]. by iApply (sem_wf_let with "(IH [//]) (IH1 [//])").
    - (* Call *) destruct Hwf as [Hwf1 Hwf2]. by iApply (sem_wf_call with "(IH [//]) (IH1 [//])").
    - (* UnOp *) by iApply (sem_wf_unop with "(IH [//])").
    - (* BinOp *) destruct Hwf as [Hwf1 Hwf2]. by iApply (sem_wf_binop with "(IH [//]) (IH1 [//])").
    - (* If *) destruct Hwf as (Hwf1 & Hwf2 & Hwf3). by iApply (sem_wf_if with "(IH [//]) (IH1 [//]) (IH2 [//])").
    - (* While *) destruct Hwf as (Hwf1 & Hwf2). by iApply (sem_wf_while with "(IH [//]) (IH1 [//])").
    - (* Pairs *) destruct Hwf as (Hwf1 & Hwf2). by iApply (sem_wf_pair with "(IH [//]) (IH1 [//])").
    - (* Fst *) by iApply (sem_wf_fst with "(IH [//])").
    - (* Snd *) by iApply (sem_wf_snd with "(IH [//])").
    - (* InjL *) by iApply (sem_wf_injl with "(IH [//])").
    - (* InjR *) by iApply (sem_wf_injr with "(IH [//])").
    - (* Match *) destruct Hwf as (Hwf1 & Hwf2 & Hwf3).
      by iApply (sem_wf_match with "(IH [//]) (IH1 [//]) (IH2 [//])").
    - (* Fork *) by iApply (sem_wf_fork with "(IH [//])").
    - (* AllocN *) destruct Hwf as (Hwf1 & Hwf2). by iApply (sem_wf_allocN with "(IH [//]) (IH1 [//])").
    - (* Free *) destruct Hwf as (Hwf1 & Hwf2). by iApply (sem_wf_freeN with "(IH [//]) (IH1 [//])").
    - (* Load *) by iApply (sem_wf_load with "(IH [//])").
    - (* Store *) destruct Hwf as (Hwf1 & Hwf2). by iApply (sem_wf_store with "(IH [//]) (IH1 [//])").
    - done.
    - done.
  Qed.

  Theorem heap_bij_refl e π : expr_wf e → ⊢ e ⪯{π, val_rel} e {{ val_rel }}.
  Proof.
    intros Hwf. iPoseProof (expr_wf_sound _ Hwf) as "Hwf".
    iSpecialize ("Hwf" $! π ∅). setoid_rewrite fmap_empty.
    rewrite !subst_map_empty. iApply "Hwf". rewrite /subst_map_rel.
    by rewrite -map_ForallI_empty.
  Qed.

  Definition ectxi_wf (Ki : ectx_item) : Prop :=
    match Ki with
    | LetCtx _ e => expr_wf e
    | UnOpCtx _ => True
    | BinOpLCtx _ v => val_wf v
    | BinOpRCtx _ e => expr_wf e
    | IfCtx e1 e2 => expr_wf e1 ∧ expr_wf e2
    | PairLCtx v => val_wf v
    | PairRCtx e => expr_wf e
    | FstCtx | SndCtx | InjLCtx | InjRCtx | LoadCtx _ => True
    | MatchCtx _ e1 _ e2 => expr_wf e1 ∧ expr_wf e2
    | AllocNLCtx v => val_wf v
    | AllocNRCtx e => expr_wf e
    | FreeNLCtx v => val_wf v
    | FreeNRCtx e => expr_wf e
    | StoreLCtx _ v => val_wf v
    | StoreRCtx _ e => expr_wf e
    | CmpXchgLCtx _ _ => False  (* unsupported *)
    | CmpXchgMCtx _ _ => False  (* unsupported *)
    | CmpXchgRCtx _ _ => False  (* unsupported *)
    | FaaLCtx _ => False  (* unsupported *)
    | FaaRCtx _ => False (* unsupported *)
    | CallLCtx v => val_wf v
    | CallRCtx e => expr_wf e
    end.
  (* we do not use [Forall] since that does not compute,
    making applications of [heap_bij_ectx_refl] hard. *)
  Fixpoint ectx_wf (K : ectx) : Prop :=
    match K with
    | [] => True
    | Ki :: K => ectxi_wf Ki ∧ ectx_wf K
    end.

  Theorem heap_bij_ectx_refl π K :
    ectx_wf K → ⊢ sim_ectx val_rel π K K val_rel.
  Proof.
    intros Hwf. iInduction (K) as [ | Ki K] "IH".
    { iIntros (v_t v_s) "Hv". sim_pures. by sim_val. }
    destruct Hwf as [Hiwf Kwf].
    iSpecialize ("IH" with "[//]").
    iIntros (v_t v_s) "#Hv". destruct Ki; sim_pures; iApply sim_bind; (iApply sim_wand; [ iApply sem_wf_empty | iApply "IH"]).
    - iApply sem_wf_let; [by iApply sem_wf_val | by iApply expr_wf_sound].
    - iApply sem_wf_unop. by iApply sem_wf_val.
    - iApply sem_wf_binop; [by iApply sem_wf_val | by iApply expr_wf_sound].
    - iApply sem_wf_binop; [ by iApply expr_wf_sound | by iApply sem_wf_val].
    - iApply sem_wf_if; [by iApply sem_wf_val | iApply expr_wf_sound; apply Hiwf..].
    - iApply sem_wf_pair; iApply sem_wf_val; [done | by iApply val_wf_sound].
    - iApply sem_wf_pair; [by iApply expr_wf_sound | by iApply sem_wf_val].
    - iApply sem_wf_fst; by iApply sem_wf_val.
    - iApply sem_wf_snd; by iApply sem_wf_val.
    - iApply sem_wf_injl; by iApply sem_wf_val.
    - iApply sem_wf_injr; by iApply sem_wf_val.
    - iApply sem_wf_match; [by iApply sem_wf_val | iApply expr_wf_sound; apply Hiwf..].
    - iApply sem_wf_allocN; [by iApply sem_wf_val | iApply sem_wf_val; by iApply val_wf_sound].
    - iApply sem_wf_allocN; [iApply expr_wf_sound; apply Hiwf | by iApply sem_wf_val ].
    - iApply sem_wf_freeN; [by iApply sem_wf_val | iApply expr_wf_sound; apply Hiwf].
    - iApply sem_wf_freeN; [iApply expr_wf_sound; apply Hiwf | by iApply sem_wf_val ].
    - iApply sem_wf_load; by iApply sem_wf_val.
    - iApply sem_wf_store; [by iApply sem_wf_val | iApply expr_wf_sound; apply Hiwf].
    - iApply sem_wf_store; [iApply expr_wf_sound; apply Hiwf | by iApply sem_wf_val ].
    - by destruct Hiwf.
    - by destruct Hiwf.
    - by destruct Hiwf.
    - by destruct Hiwf.
    - by destruct Hiwf.
    - iApply sem_wf_call; [by iApply sem_wf_val | iApply expr_wf_sound; apply Hiwf].
    - iApply sem_wf_call; [iApply expr_wf_sound; apply Hiwf | by iApply sem_wf_val ].
  Qed.

  (* TODO: do the same thing for a general notion of contexts *)
End refl.
