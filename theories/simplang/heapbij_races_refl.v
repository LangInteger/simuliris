From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst heap_bij_races.

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
  Context `{nabijG Σ}.

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
    | Load o e => o ≠ Na2Ord ∧ expr_wf e
    | Store o e1 e2 => o ≠ Na2Ord ∧ expr_wf e1 ∧ expr_wf e2
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

  Definition sem_wf c e_t e_s : iProp Σ :=
    ∀ π (map : gmap string (val * val)) φ,
      subst_map_rel map -∗
      na_locs π c -∗
      (∀ v_t v_s, val_rel v_t v_s -∗ na_locs π c -∗ φ v_t v_s) -∗
      subst_map (fst <$> map) e_t ⪯{π, weak_val_rel} subst_map (snd <$> map) e_s {{ φ }}.

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

  Lemma sem_wf_var c x : ⊢ sem_wf c (Var x) (Var x).
  Proof.
    iIntros (? xs φ) "#Hs Hc Hφ"; simpl.
    rewrite !lookup_fmap. destruct (xs !! x) as [[v_t v_s] | ] eqn:Heq; simpl.
    { sim_pures; sim_val; iModIntro. iApply ("Hφ" with "[] Hc"). by iApply ("Hs" $! x (v_t, v_s)). }
    source_stuck_prim.
  Qed.

  Lemma sem_wf_let c x e1_t e1_s e2_t e2_s :
    sem_wf c e1_t e1_s -∗ sem_wf c e2_t e2_s -∗ sem_wf c (Let x e1_t e2_t) (Let x e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply ("IH1" with "Hs Hc"). iIntros (v_t v_s) "#Hv Hc".
    sim_pures. rewrite !subst'_subst_map.
    rewrite -(binder_insert_fmap fst (v_t, v_s)).
    rewrite -(binder_insert_fmap snd (v_t, v_s)).
    iApply ("IH2" with "[] Hc Hφ"). by iApply (subst_map_rel_insert with "Hv").
  Qed.

  Lemma sem_wf_call e1_t e1_s e2_t e2_s :
    sem_wf ∅ e1_t e1_s -∗ sem_wf ∅ e2_t e2_s -∗ sem_wf ∅ (Call e1_t e2_t) (Call e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply ("IH2" with "Hs Hc"). iIntros (v_t2 v_s2) "#Hv2 Hc".
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply ("IH1" with "Hs Hc"). iIntros (v_t1 v_s1) "#Hv1 Hc".
    discr_source; first by apply call_not_val. val_discr_source "Hv1".
    iApply (sim_expr_wand with "[Hc]").
    { iApply sim_call; [done..|]. by iFrame. }
    iApply lift_post_mon. iIntros (v_t v_s) "[Hc #Hv]". by iApply "Hφ".
  Qed.

  Lemma sem_wf_unop c e_t e_s o :
    sem_wf c e_t e_s -∗ sem_wf c (UnOp o e_t) (UnOp o e_s).
  Proof.
    iIntros "IH" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply ("IH" with "Hs Hc"). iIntros (v_t v_s) "#Hv Hc".
    destruct o; sim_pures; discr_source; val_discr_source "Hv"; sim_pures; sim_val.
    all: iModIntro; by iApply "Hφ".
  Qed.

  Lemma sem_wf_binop c e1_t e1_s e2_t e2_s o :
    sem_wf c e1_t e1_s -∗ sem_wf c e2_t e2_s -∗ sem_wf c (BinOp o e1_t e2_t) (BinOp o e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply ("IH2" with "Hs Hc"). iIntros (v_t2 v_s2) "#Hv2 Hc".
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply ("IH1" with "Hs Hc"). iIntros (v_t1 v_s1) "#Hv1 Hc".
    destruct o; sim_pures; discr_source; val_discr_source "Hv1"; val_discr_source "Hv2"; sim_pures; [sim_val; by iApply "Hφ".. | | ].
    - iAssert (⌜vals_compare_safe v_t1 v_t2⌝)%I as "%".
      { iPoseProof (val_rel_val_is_unboxed with "Hv1") as "%".
        iPoseProof (val_rel_val_is_unboxed with "Hv2") as "%".
        iPureIntro. by rewrite /vals_compare_safe H1 H2.
      }
      case_bool_decide; subst.
      * iPoseProof (val_rel_inj with "Hv1 Hv2") as "->".
        sim_pures; sim_val. case_bool_decide; by iApply "Hφ".
      * sim_pures; sim_val. case_bool_decide; subst; last by iApply "Hφ".
        by iPoseProof (val_rel_func with "Hv1 Hv2") as "->".
    - iPoseProof (val_rel_loc_source with "Hv1") as (l_t) "(-> & Hl)".
      sim_pures. sim_val. iModIntro; cbn.
      iApply "Hφ"; [|done].
      by iApply heap_bij_loc_shift.
  Qed.

  Lemma sem_wf_if c e1_t e1_s e2_t e2_s e3_t e3_s :
    sem_wf c e1_t e1_s -∗ sem_wf c e2_t e2_s -∗ sem_wf c e3_t e3_s -∗ sem_wf c (If e1_t e2_t e3_t) (If e1_s e2_s e3_s).
  Proof.
    iIntros "IH1 IH2 IH3" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ e1_t) (subst_map _ e1_s).
    iApply ("IH1" with "Hs Hc"). iIntros (v_t1 v_s1) "#Hv Hc".
    discr_source. val_discr_source "Hv". destruct x; sim_pures.
    + by iApply ("IH2" with "Hs Hc").
    + by iApply ("IH3" with "Hs Hc").
  Qed.

  Lemma sem_wf_while c e1_t e1_s e2_t e2_s :
    (□ sem_wf c e1_t e1_s) -∗ (□ sem_wf c e2_t e2_s) -∗ sem_wf c (While e1_t e2_t) (While e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs φ) "#Hs Hc Hφ"; simpl.
    iApply (sim_while_while _ _ _ _ _ _ (na_locs π c ∗ (∀ v_t v_s : val, val_rel v_t v_s -∗ na_locs π c -∗ φ v_t v_s))%I with "[$]").
    iModIntro; iIntros "[Hc Hφ]".
    sim_bind (subst_map _ e1_t) (subst_map _ e1_s).
    iApply ("IH1" with "Hs Hc"). iIntros (v_t1 v_s1) "#Hv1 Hc".
    discr_source. val_discr_source "Hv1". destruct x; sim_pures.
    + sim_bind (subst_map _ e2_t) (subst_map _ e2_s).
      iApply ("IH2" with "Hs Hc"). iIntros (v_t2 v_s2) "#Hv2 Hc".
      sim_pures. iApply sim_expr_base. iRight. by iFrame.
    + iApply sim_expr_base. iLeft. iApply lift_post_val. by iApply "Hφ".
  Qed.

  Lemma sem_wf_pair c e1_t e1_s e2_t e2_s :
    sem_wf c e1_t e1_s -∗ sem_wf c e2_t e2_s -∗ sem_wf c (Pair e1_t e2_t) (Pair e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ e2_t) (subst_map _ e2_s).
    iApply ("IH2" with "Hs Hc"). iIntros (v_t2 v_s2) "#Hv2 Hc".
    sim_bind (subst_map _ e1_t) (subst_map _ e1_s).
    iApply ("IH1" with "Hs Hc"). iIntros (v_t1 v_s1) "#Hv1 Hc".
    sim_pures; sim_val. iModIntro. by iApply "Hφ"; [iSplit|].
  Qed.

  Lemma sem_wf_fst c e_t e_s :
    sem_wf c e_t e_s -∗ sem_wf c (Fst e_t) (Fst e_s).
  Proof.
    iIntros "IH" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ e_t) (subst_map _ e_s).
    iApply ("IH" with "Hs Hc"). iIntros (v_t v_s) "#Hv Hc".
    discr_source. iPoseProof (val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; sim_pures; sim_val; by iApply "Hφ".
  Qed.
  Lemma sem_wf_snd c e_t e_s :
    sem_wf c e_t e_s -∗ sem_wf c (Snd e_t) (Snd e_s).
  Proof.
    iIntros "IH" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ e_t) (subst_map _ e_s).
    iApply ("IH" with "Hs Hc"). iIntros (v_t v_s) "#Hv Hc".
    discr_source. iPoseProof (val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; by sim_pures; sim_val; iApply "Hφ".
  Qed.

  Lemma sem_wf_injl c e_t e_s :
    sem_wf c e_t e_s -∗ sem_wf c (InjL e_t) (InjL e_s).
  Proof.
    iIntros "IH" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ e_t) (subst_map _ e_s).
    iApply ("IH" with "Hs Hc"). iIntros (v_t v_s) "#Hv Hc".
    by sim_pures; sim_val; iApply "Hφ".
  Qed.
  Lemma sem_wf_injr c e_t e_s :
    sem_wf c e_t e_s -∗ sem_wf c (InjR e_t) (InjR e_s).
  Proof.
    iIntros "IH" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ e_t) (subst_map _ e_s).
    iApply ("IH" with "Hs Hc"). iIntros (v_t v_s) "#Hv Hc".
    by sim_pures; sim_val; iApply "Hφ".
  Qed.

  Lemma sem_wf_match c e_t e_s e1_t e1_s e2_t e2_s x1 x2 :
    sem_wf c e_t e_s -∗ sem_wf c e1_t e1_s -∗ sem_wf c e2_t e2_s -∗ sem_wf c (Match e_t x1 e1_t x2 e2_t) (Match e_s x1 e1_s x2 e2_s).
  Proof.
    iIntros "IH IH1 IH2" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ e_t) (subst_map _ e_s).
    iApply ("IH" with "Hs Hc"). iIntros (v_t v_s) "#Hv Hc".
    discr_source.
    + iPoseProof (val_rel_injl_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
      rewrite !subst'_subst_map.
      rewrite -(binder_insert_fmap fst (v_t', x)).
      rewrite -(binder_insert_fmap snd (v_t', x)).
      iApply ("IH1" with "[] Hc Hφ"). by iApply subst_map_rel_insert.
    + iPoseProof (val_rel_injr_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
      rewrite !subst'_subst_map.
      rewrite -(binder_insert_fmap fst (v_t', x)).
      rewrite -(binder_insert_fmap snd (v_t', x)).
      iApply ("IH2" with "[] Hc Hφ"). by iApply subst_map_rel_insert.
  Qed.

  Lemma sem_wf_fork e_t e_s :
    sem_wf ∅ e_t e_s -∗ sem_wf ∅ (Fork e_t) (Fork e_s).
  Proof.
    iIntros "IH" (? xs φ) "#Hs Hc Hφ"; simpl.
    iApply (sim_bij_fork with "Hc [Hφ]").
    - iIntros "Hc". sim_pures. sim_val. by iApply "Hφ".
    - iIntros (?) "Hc". sim_pures. iApply ("IH" with "Hs Hc").
      iIntros (??) "$ $".
  Qed.

  Lemma sem_wf_allocN c e1_t e1_s e2_t e2_s :
    sem_wf c e1_t e1_s -∗ sem_wf c e2_t e2_s -∗ sem_wf c (AllocN e1_t e2_t) (AllocN e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs φ) "#Hs Hc Hφ"; simpl.
    sim_bind (subst_map _ e2_t) (subst_map _ e2_s).
    iApply ("IH2" with "Hs Hc"). iIntros (v_t2 v_s2) "#Hv2 Hc".
    sim_bind (subst_map _ e1_t) (subst_map _ e1_s).
    iApply ("IH1" with "Hs Hc"). iIntros (v_t1 v_s1) "#Hv1 Hc".
    discr_source. val_discr_source "Hv1".
    target_alloc l_t as "Hl_t" "Ha_t"; first done.
    source_alloc l_s as "Hl_s" "Ha_s"; first done.
    iApply (sim_bij_insertN with "Ha_t Ha_s Hl_t Hl_s [Hv1]"); [lia | by rewrite replicate_length.. | | ].
    { rewrite big_sepL2_replicate_l; last by rewrite replicate_length.
      generalize (Z.to_nat x) => n.
      iInduction n as [] "IHn"; cbn; first done. iFrame "Hv2 IHn".
    }
    iIntros "#Hv". sim_pures. sim_val. by iApply "Hφ".
  Qed.

  Lemma sem_wf_freeN e1_t e1_s e2_t e2_s :
    sem_wf ∅ e1_t e1_s -∗ sem_wf ∅ e2_t e2_s -∗ sem_wf ∅ (FreeN e1_t e2_t) (FreeN e1_s e2_s).
  Proof.
    iIntros "IH1 IH2" (? xs φ) "#Hs Hc HΦ"; simpl.
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply ("IH2" with "Hs Hc"). iIntros (v_t v_s) "#Hv Hc".
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply ("IH1" with "Hs Hc"). iIntros (v_t' v_s') "Hv2 Hc".
    discr_source. iPoseProof (val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
    iPoseProof (val_rel_litint_source with "Hv2") as "->".
    iApply (sim_bij_free with "Hrel Hc"); [done|]. iIntros "Hc".
    sim_val. by iApply "HΦ".
  Qed.

  Lemma sem_wf_load o e_t e_s :
    o = ScOrd ∨ o = Na1Ord →
    sem_wf ∅ e_t e_s -∗ sem_wf ∅ (Load o e_t) (Load o e_s).
  Proof.
    move => ?. iIntros "IH" (? xs Φ) "#Hs Hc HΦ"; simpl.
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply ("IH" with "Hs Hc"). iIntros (v_t v_s) "#Hv Hc".
    discr_source; iPoseProof (val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
    all: iApply (sim_bij_load with "Hrel Hc"); [done..|].
    all: iIntros (v_t v_s) "Hv' Hc"; sim_val; by iApply ("HΦ" with "Hv' Hc").
  Qed.

  Lemma sem_wf_store o e1_t e1_s e2_t e2_s :
    o = ScOrd ∨ o = Na1Ord →
    sem_wf ∅ e1_t e1_s -∗ sem_wf ∅ e2_t e2_s -∗ sem_wf ∅ (Store o e1_t e2_t) (Store o e1_s e2_s).
  Proof.
    move => ?. iIntros "IH1 IH2" (? xs Φ) "#Hs Hc HΦ"; simpl.
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply ("IH2" with "Hs Hc"). iIntros (v_t2 v_s2) "#Hv2 Hc".
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply ("IH1" with "Hs Hc"). iIntros (v_t1 v_s1) "#Hv1 Hc".
    discr_source; iPoseProof (val_rel_loc_source with "Hv1") as (l_t) "(-> & Hrel)".
    - iApply (sim_bij_store_sc with "Hrel Hc"); [done|].
      iIntros "Hc". sim_val. by iApply ("HΦ" with "[] Hc").
    - iApply (sim_bij_store_na with "Hrel Hc"); [done..|].
      iIntros "Hc". sim_val. by iApply ("HΦ" with "[] Hc").
  Qed.

  Lemma sem_wf_val v_t v_s c :
    val_rel v_t v_s -∗ sem_wf c (Val v_t) (Val v_s).
  Proof. iIntros "Hv" (? xs Φ) "#Hs Hc HΦ"; simpl. sim_val. iApply ("HΦ" with "Hv Hc"). Qed.

  Lemma sem_wf_empty e_t e_s π : na_locs π ∅ -∗ sem_wf ∅ e_t e_s -∗ e_t ⪯{π, weak_val_rel} e_s {{ weak_val_rel π }}.
  Proof.
    iIntros "Hc Hwf". iSpecialize ("Hwf" $! π ∅ with "[] Hc").
    { iApply subst_map_rel_empty. }
    rewrite !fmap_empty !subst_map_empty.
    iApply "Hwf". iIntros (??) "$ $".
  Qed.

  Lemma expr_wf_sound e : expr_wf e → ⊢ sem_wf ∅ e e.
  Proof.
    intros Hwf. iInduction e as [ ] "IH" forall (Hwf).
    - (* Val *) iApply sem_wf_val. by iApply val_wf_sound.
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
    - (* Load *) destruct Hwf as (? & Hwf2). destruct o => //; iApply (sem_wf_load with "(IH [//])"); naive_solver.
    - (* Store *) destruct Hwf as (? & Hwf1 & Hwf2). destruct o => //; iApply (sem_wf_store with "(IH [//]) (IH1 [//])"); naive_solver.
    - done.
    - done.
  Qed.

  Theorem heap_bij_refl e π : expr_wf e →
    ⊢ na_locs π ∅ -∗ e ⪯{π, weak_val_rel} e {{ weak_val_rel π }}.
  Proof.
    iIntros (Hwf) "Hc". iPoseProof (expr_wf_sound _ Hwf) as "Hwf".
    iSpecialize ("Hwf" $! π ∅ (weak_val_rel π)). setoid_rewrite fmap_empty.
    rewrite !subst_map_empty. iApply ("Hwf" with "[] Hc").
    { rewrite /subst_map_rel. by rewrite -map_ForallI_empty. }
    iIntros (??) "$ $".
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
    | FstCtx | SndCtx | InjLCtx | InjRCtx => True
    | MatchCtx _ e1 _ e2 => expr_wf e1 ∧ expr_wf e2
    | AllocNLCtx v => val_wf v
    | AllocNRCtx e => expr_wf e
    | FreeNLCtx v => val_wf v
    | FreeNRCtx e => expr_wf e
    | LoadCtx o => o ≠ Na2Ord
    | StoreLCtx o v => o ≠ Na2Ord ∧ val_wf v
    | StoreRCtx o e => o ≠ Na2Ord ∧ expr_wf e
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

  (*
  Theorem heap_bij_ectx_refl π K :
    ectx_wf K → ⊢ sim_ectx (weak_val_rel val_rel) π K K (weak_val_rel val_rel π).
  Proof.
    intros Hwf. iInduction (K) as [ | Ki K] "IH".
    { iIntros (v_t v_s) "Hv". sim_pures. by sim_val. }
    destruct Hwf as [Hiwf Kwf].
    iSpecialize ("IH" with "[//]").
    iIntros (v_t v_s) "[Hc #Hv]".
    destruct Ki; sim_pures; iApply sim_bind; (iApply (sim_wand with "[Hc]"); [ iApply (sem_wf_empty with "Hc") | iIntros (??) "?"; by iApply "IH" ]).
    - iApply sem_wf_let; [by iApply sem_wf_val | by iApply expr_wf_sound].
    - iApply sem_wf_call; [by iApply sem_wf_val | by iApply expr_wf_sound].
    - iApply sem_wf_call; [by iApply sem_wf_val | by iApply expr_wf_sound].
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
    - destruct o => //; (iApply sem_wf_load; [naive_solver|]); by iApply sem_wf_val.
    - destruct Hiwf. destruct o => //; (iApply sem_wf_store; [naive_solver|by iApply sem_wf_val |by iApply expr_wf_sound]).
    - destruct Hiwf. destruct o => //; (iApply sem_wf_store; [naive_solver | by iApply expr_wf_sound | by iApply sem_wf_val ]).
    - by destruct Hiwf.
    - by destruct Hiwf.
    - by destruct Hiwf.
    - by destruct Hiwf.
    - by destruct Hiwf.
    - iApply sem_wf_call; [by iApply sem_wf_val | iApply expr_wf_sound; apply Hiwf].
    - iApply sem_wf_call; [iApply expr_wf_sound; apply Hiwf | by iApply sem_wf_val ].
  Qed.
*)
  (* TODO: do the same thing for a general notion of contexts *)
End refl.
