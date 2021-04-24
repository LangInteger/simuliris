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

(** We will only be able to show reflexivity for "well-formed" terms.
  Namely, all literal locations should already be in the heap bijection.
*)

Section refl.
  Context `{sbijG Σ}.

  Fixpoint val_wf (v : val) : iProp Σ :=
    match v with
    | LitV (LitLoc l) => l ↔h l
    | LitV _ => True
    | PairV v1 v2 => val_wf v1 ∧ val_wf v2
    | InjLV v => val_wf v
    | InjRV v => val_wf v
    end.

  Fixpoint expr_wf (e : expr) : iProp Σ :=
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
    | Fork e => False             (* currently not supported *)
    | AllocN e1 e2 => expr_wf e1 ∧ expr_wf e2
    | FreeN e1 e2 => expr_wf e1 ∧ expr_wf e2
    | Load o e => expr_wf e
    | Store o e1 e2 => expr_wf e1 ∧ expr_wf e2
    | CmpXchg e1 e2 e3 => False   (* currently not supported *)
    | FAA e1 e2 => False          (* currently not supported *)
    end.

  Instance val_wf_pers v : Persistent (val_wf v).
  Proof. induction v as [[] | | | ]; apply _. Qed.
  Instance expr_wf_pers e : Persistent (expr_wf e).
  Proof. induction e; apply _. Qed.

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

  Definition sem_wf e_t e_s : iProp Σ :=
    ∀ (map : gmap string (val * val)),
      subst_map_rel map -∗ subst_map (fst <$> map) e_t ⪯ subst_map (snd <$> map) e_s {{ val_rel }}.

  Lemma val_wf_sound v : ⊢ val_wf v → val_rel v v.
  Proof.
    iIntros "H".
    iInduction v as [[] | | | ] "IH"; try by (simpl; try iApply "IH").
    simpl. iDestruct "H" as "[H1 H2]". iSplit; [by iApply "IH" | by iApply "IH1"].
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

  Lemma expr_wf_sound e : ⊢ expr_wf e → sem_wf e e.
  Proof.
    iIntros "Hwf". iInduction e as [ ] "IH" forall "Hwf"; iIntros (xs) "#Hs"; simpl.
    - (* Val *)
      sim_pures; sim_val. iModIntro; by iApply val_wf_sound.
    - (* Var *)
      iSpecialize ("Hs" $! x).
      rewrite !lookup_fmap. destruct (xs !! x) as [[v_t v_s] | ] eqn:Heq; simpl.
      { sim_pures; sim_val; iModIntro. by iApply ("Hs" $! (v_t, v_s)). }
      source_stuck_prim.
    - (* Let *)
      iDestruct "Hwf" as "[Hwf1 Hwf2]".
      iSpecialize ("IH" with "Hwf1 Hs").
      sim_bind (subst_map _ e1) (subst_map _ e1). iApply (sim_wand with "IH").
      iIntros (v_t v_s) "#Hv". sim_pures. rewrite !subst'_subst_map.
      rewrite -(binder_insert_fmap fst (v_t, v_s)).
      rewrite -(binder_insert_fmap snd (v_t, v_s)).
      iApply ("IH1" with "Hwf2").
      by iApply (subst_map_rel_insert with "Hv").
    - (* Call *)
      iDestruct "Hwf" as "[Hwf1 Hwf2]".
      iSpecialize ("IH1" with "Hwf2 Hs").
      sim_bind (subst_map _ e2) (subst_map _ e2). iApply (sim_wand with "IH1").
      iIntros (v_t1 v_s1) "#Hv1".
      iSpecialize ("IH" with "Hwf1 Hs").
      sim_bind (subst_map _ e1) (subst_map _ e1). iApply (sim_wand with "IH").
      iIntros (v_t2 v_s2) "#Hv2".
      iApply sim_irred_unless; first by apply call_not_val.
      iIntros ((fn_s & ->)). iPoseProof (val_rel_litfn_source with "Hv2") as "->".
      iApply sim_call; done.
    - (* UnOp *)
      iSpecialize ("IH" with "Hwf Hs").
      sim_bind (subst_map _ e) (subst_map _ e). iApply (sim_wand with "IH").
      iIntros (v_t v_s) "#Hv". destruct op; sim_pures; discr_source; val_discr_source "Hv"; by sim_pures; sim_val.
    - (* BinOp *)
      iDestruct "Hwf" as "[Hwf1 Hwf2]".
      iSpecialize ("IH1" with "Hwf2 Hs").
      sim_bind (subst_map _ e2) (subst_map _ e2). iApply (sim_wand with "IH1").
      iIntros (v_t2 v_s2) "Hv2".
      iSpecialize ("IH" with "Hwf1 Hs").
      sim_bind (subst_map _ e1) (subst_map _ e1). iApply (sim_wand with "IH").
      iIntros (v_t1 v_s1) "Hv1".
      destruct op; sim_pures; discr_source; val_discr_source "Hv1"; val_discr_source "Hv2"; sim_pures; [sim_val; done .. | | ].
      + iAssert (⌜vals_compare_safe v_t1 v_t2⌝)%I as "%".
        { iPoseProof (val_rel_val_is_unboxed with "Hv1") as "%".
          iPoseProof (val_rel_val_is_unboxed with "Hv2") as "%".
          iPureIntro. by rewrite /vals_compare_safe H1 H2.
        }
        case_bool_decide; subst.
        * iPoseProof (val_rel_inj with "Hv1 Hv2") as "->".
          sim_pures; sim_val. case_bool_decide; done.
        * sim_pures; sim_val. case_bool_decide; subst; last done.
          by iPoseProof (val_rel_func with "Hv1 Hv2") as "->".
      + iPoseProof (val_rel_loc_source with "Hv1") as (l_t) "(-> & Hl)".
        sim_pures. sim_val. iModIntro; cbn.
        by iApply heap_bij_loc_shift.
    - (* If *)
      iDestruct "Hwf" as "(Hwf1 & Hwf2 & Hwf3)".
      iSpecialize ("IH" with "Hwf1 Hs").
      sim_bind (subst_map _ e1) (subst_map _ e1). iApply (sim_wand with "IH").
      iIntros (v_t v_s) "Hv".
      discr_source. val_discr_source "Hv". destruct x; sim_pures.
      + iApply ("IH1" with "Hwf2 Hs").
      + iApply ("IH2" with "Hwf3 Hs").
    - (* While *)
      iDestruct "Hwf" as "(#Hwf1 & #Hwf2)".
      iApply (sim_while_while _ _ _ _ _ (True)%I with "[//]").
      iModIntro; iIntros "_".
      iSpecialize ("IH" with "Hwf1 Hs"). iSpecialize ("IH1" with "Hwf2 Hs").
      sim_bind (subst_map _ e1) (subst_map _ e1). iApply (sim_wand with "IH").
      iIntros (v_t v_s) "Hv".
      discr_source. val_discr_source "Hv". destruct x; sim_pures.
      + sim_bind (subst_map _ e2) (subst_map _ e2).
        iApply (sim_wand with "IH1").
        iIntros (? ?) "_"; sim_pures. iApply sim_expr_base. iRight. by eauto.
      + iApply sim_expr_base. iLeft. iExists #(), #(); eauto.
    - (* Pairs *)
      iDestruct "Hwf" as "(Hwf1 & Hwf2)".
      iSpecialize ("IH" with "Hwf1 Hs"). iSpecialize ("IH1" with "Hwf2 Hs").
      sim_bind (subst_map _ e2) (subst_map _ e2).
      iApply (sim_wand with "IH1"). iIntros (v_t2 v_s2) "Hv2".
      sim_bind (subst_map _ e1) (subst_map _ e1).
      iApply (sim_wand with "IH"). iIntros (v_t1 v_s1) "Hv1".
      sim_pures; sim_val. iModIntro; iSplit; eauto.
    - (* Fst *)
      sim_bind (subst_map _ e) (subst_map _ e). iSpecialize ("IH" with "Hwf Hs").
      iApply (sim_wand with "IH"). iIntros (v_t v_s) "Hv".
      discr_source. iPoseProof (val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; by sim_pures; sim_val.
    - (* Snd *)
      sim_bind (subst_map _ e) (subst_map _ e). iSpecialize ("IH" with "Hwf Hs").
      iApply (sim_wand with "IH"). iIntros (v_t v_s) "Hv".
      discr_source. iPoseProof (val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; by sim_pures; sim_val.
    - (* InjL *)
      sim_bind (subst_map _ e) (subst_map _ e). iSpecialize ("IH" with "Hwf Hs").
      iApply (sim_wand with "IH"). iIntros (v_t v_s) "Hv"; by sim_pures; sim_val.
    - (* InjR *)
      sim_bind (subst_map _ e) (subst_map _ e). iSpecialize ("IH" with "Hwf Hs").
      iApply (sim_wand with "IH"). iIntros (v_t v_s) "Hv"; by sim_pures; sim_val.
    - (* Match *)
      iDestruct "Hwf" as "(Hwf1 & Hwf2 & Hwf3)".
      iSpecialize ("IH" with "Hwf1 Hs").

      sim_bind (subst_map _ e1) (subst_map _ e1). iApply (sim_wand with "IH").
      iIntros (v_t v_s) "#Hv".
      discr_source.
      + iPoseProof (val_rel_injl_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
        rewrite !subst'_subst_map.
        rewrite -(binder_insert_fmap fst (v_t', x)).
        rewrite -(binder_insert_fmap snd (v_t', x)).
        iApply ("IH1" with "Hwf2"). by iApply subst_map_rel_insert.
      + iPoseProof (val_rel_injr_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
        rewrite !subst'_subst_map.
        rewrite -(binder_insert_fmap fst (v_t', x)).
        rewrite -(binder_insert_fmap snd (v_t', x)).
        iApply ("IH2" with "Hwf3"). by iApply subst_map_rel_insert.
    - done.
    - (* AllocN *)
      iDestruct "Hwf" as "(Hwf1 & Hwf2)".
      iSpecialize ("IH" with "Hwf1 Hs"). iSpecialize ("IH1" with "Hwf2 Hs").
      sim_bind (subst_map _ e2) (subst_map _ e2).
      iApply (sim_wand with "IH1"). iIntros (v_t v_s) "Hv".
      sim_bind (subst_map _ e1) (subst_map _ e1).
      iApply (sim_wand with "IH"). iIntros (v_t' v_s') "Hv'".
      discr_source. val_discr_source "Hv'".
      target_alloc l_t as "Hl_t" "Ha_t"; first done.
      source_alloc l_s as "Hl_s" "Ha_s"; first done.
      to_sim.
      iApply (sim_bij_insertN with "Ha_t Ha_s Hl_t Hl_s [Hv]"); [lia | by rewrite replicate_length.. | | ].
      { iDestruct "Hv" as "#Hv". rewrite /vrel_list.
        rewrite big_sepL2_replicate_l; last by rewrite replicate_length.
        generalize (Z.to_nat x) => n.
        iInduction n as [] "IH"; cbn; first done. iFrame "Hv IH".
      }
      iIntros "Hv". sim_pures. sim_val. done.
    - (* Free *)
      iDestruct "Hwf" as "(Hwf1 & Hwf2)".
      iSpecialize ("IH" with "Hwf1 Hs"). iSpecialize ("IH1" with "Hwf2 Hs").
      sim_bind (subst_map _ e2) (subst_map _ e2). iApply (sim_wand with "IH1"). iIntros (v_t v_s) "Hv".
      sim_bind (subst_map _ e1) (subst_map _ e1). iApply (sim_wand with "IH"). iIntros (v_t' v_s') "Hv'".
      discr_source. iPoseProof (val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
      iPoseProof (val_rel_litint_source with "Hv'") as "->".
      by sim_free; sim_val.
    - (* Load *)
      iSpecialize ("IH" with "Hwf Hs").
      sim_bind (subst_map _ e) (subst_map _ e). iApply (sim_wand with "IH").
      iIntros (v_t v_s) "Hv". discr_source. iPoseProof (val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
      by sim_load v_t v_s as "Hv"; sim_val.
    - (* Store *)
      iDestruct "Hwf" as "(Hwf1 & Hwf2)".
      iSpecialize ("IH" with "Hwf1 Hs"). iSpecialize ("IH1" with "Hwf2 Hs").
      sim_bind (subst_map _ e2) (subst_map _ e2). iApply (sim_wand with "IH1").
      iIntros (v_t v_s) "Hv". (* FIXME: fix printing *)
      sim_bind (subst_map _ e1) (subst_map _ e1). iApply (sim_wand with "IH").
      iIntros (v_t' v_s') "Hv'".
      discr_source. iPoseProof (val_rel_loc_source with "Hv'") as (l_t) "(-> & Hrel)".
      by sim_store; [done | sim_val].
    - done.
    - done.
  Qed.

  Theorem heap_bij_refl e : expr_wf e -∗ e ⪯ e {{ val_rel }}.
  Proof.
    iIntros "Hwf". iPoseProof (expr_wf_sound with "Hwf") as "Hwf".
    iSpecialize ("Hwf" $! ∅). setoid_rewrite fmap_empty.
    rewrite !subst_map_empty. iApply "Hwf". rewrite /subst_map_rel.
    by rewrite -map_ForallI_empty.
  Qed.
End refl.
