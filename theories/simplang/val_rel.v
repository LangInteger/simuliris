From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst primitive_laws log_rel ctx.

Section struct_val_rel.
  Context `{!sheapGS Σ} `{!sheapInv Σ}.
  Context (loc_rel : loc → loc → iProp Σ).

  Fixpoint struct_val_rel (v_t v_s : val) {struct v_s} : iProp Σ :=
    match v_t, v_s with
    | LitV (LitLoc l_t), LitV (LitLoc l_s) =>
        loc_rel l_t l_s
    | LitV l_t, LitV l_s =>
        ⌜l_t = l_s⌝
    | PairV v1_t v2_t, PairV v1_s v2_s =>
        struct_val_rel v1_t v1_s ∗ struct_val_rel v2_t v2_s
    | InjLV v_t, InjLV v_s =>
        struct_val_rel v_t v_s
    | InjRV v_t, InjRV v_s =>
        struct_val_rel v_t v_s
    | _,_ => False
    end.
  Global Instance struct_val_rel_pers v_t v_s `{!∀ l_t l_s, Persistent (loc_rel l_t l_s)} :
    Persistent (struct_val_rel v_t v_s).
  Proof.
    induction v_s as [[] | | | ] in v_t |-*; destruct v_t as [ [] | | | ]; apply _.
  Qed.

  Lemma struct_val_rel_pair_source v_t v_s1 v_s2 :
    struct_val_rel v_t (v_s1, v_s2) -∗
    ∃ v_t1 v_t2, ⌜v_t = PairV v_t1 v_t2⌝ ∗
      struct_val_rel v_t1 v_s1 ∗
      struct_val_rel v_t2 v_s2.
  Proof.
    simpl. iIntros "H". destruct v_t as [[] | v_t1 v_t2 | |]; simpl; try done.
    iExists v_t1, v_t2. iDestruct "H" as "[$ $]". eauto.
  Qed.
  Lemma struct_val_rel_injl_source v_t v_s :
    struct_val_rel v_t (InjLV v_s) -∗ ∃ v_t', ⌜v_t = InjLV v_t'⌝ ∗ struct_val_rel v_t' v_s.
  Proof. simpl. destruct v_t as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma struct_val_rel_injr_source v_t v_s :
    struct_val_rel v_t (InjRV v_s) -∗ ∃ v_t', ⌜v_t = InjRV v_t'⌝ ∗ struct_val_rel v_t' v_s.
  Proof. simpl. destruct v_t as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.


  Lemma struct_val_rel_litfn_source v_t fn_s :
    struct_val_rel v_t (LitV $ LitFn $ fn_s) -∗ ⌜v_t = LitV $ LitFn $ fn_s⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma struct_val_rel_litint_source v_t n :
    struct_val_rel v_t (LitV $ LitInt n) -∗ ⌜v_t = LitV $ LitInt $ n⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma struct_val_rel_litbool_source v_t b:
    struct_val_rel v_t (LitV $ LitBool b) -∗ ⌜v_t = LitV $ LitBool b⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma struct_val_rel_litunit_source v_t :
    struct_val_rel v_t (LitV $ LitUnit) -∗ ⌜v_t = LitV $ LitUnit⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma struct_val_rel_litpoison_source v_t :
    struct_val_rel v_t (LitV $ LitPoison) -∗ ⌜v_t = LitV $ LitPoison⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma struct_val_rel_loc_source v_t l_s :
    struct_val_rel v_t (LitV $ LitLoc l_s) -∗
    ∃ l_t, ⌜v_t = LitV $ LitLoc l_t⌝ ∗ loc_rel l_t l_s.
  Proof.
    destruct v_t as [[ | | | | l_t | ] | | | ]; simpl;
        first [iIntros "%Ht"; congruence | iIntros "Ht"; eauto].
  Qed.

  Lemma struct_val_rel_pair_target v_s v_t1 v_t2 :
    struct_val_rel (v_t1, v_t2) v_s -∗
    ∃ v_s1 v_s2, ⌜v_s = PairV v_s1 v_s2⌝ ∗
      struct_val_rel v_t1 v_s1 ∗
      struct_val_rel v_t2 v_s2.
  Proof.
    simpl. iIntros "H". destruct v_s as [[] | v_s1 v_s2 | |]; simpl; try done.
    iExists v_s1, v_s2. iDestruct "H" as "[$ $]". eauto.
  Qed.
  Lemma struct_val_rel_injl_target v_t v_s :
    struct_val_rel (InjLV v_t) v_s -∗ ∃ v_s', ⌜v_s = InjLV v_s'⌝ ∗ struct_val_rel v_t v_s'.
  Proof. simpl. destruct v_s as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma struct_val_rel_injr_target v_t v_s :
    struct_val_rel (InjRV v_t) v_s -∗ ∃ v_s', ⌜v_s = InjRV v_s'⌝ ∗ struct_val_rel v_t v_s'.
  Proof. simpl. destruct v_s as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma struct_val_rel_litfn_target v_s fn_t :
    struct_val_rel (LitV $ LitFn $ fn_t) v_s -∗ ⌜v_s = LitV $ LitFn $ fn_t⌝.
  Proof. simpl. destruct v_s as [[] | v_s1 v_s2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma struct_val_rel_litint_target v_s n :
    struct_val_rel (LitV $ LitInt n) v_s -∗ ⌜v_s = LitV $ LitInt $ n⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma struct_val_rel_litbool_target v_s b:
    struct_val_rel (LitV $ LitBool b) v_s -∗ ⌜v_s = LitV $ LitBool b⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma struct_val_rel_litunit_target v_s :
    struct_val_rel (LitV $ LitUnit) v_s -∗ ⌜v_s = LitV $ LitUnit⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma struct_val_rel_litpoison_target v_s :
    struct_val_rel (LitV $ LitPoison) v_s -∗ ⌜v_s = LitV $ LitPoison⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma struct_val_rel_loc_target v_s l_t :
    struct_val_rel (LitV $ LitLoc l_t) v_s -∗
    ∃ l_s, ⌜v_s = LitV $ LitLoc l_s⌝ ∗ loc_rel l_t l_s.
  Proof.
    destruct v_s as [[ | | | | l_s | ] | | | ]; simpl;
        first [iIntros "%Hs"; congruence | iIntros "Hs"; eauto].
  Qed.

End struct_val_rel.
Tactic Notation "val_discr_source" constr(H) :=
  first [iPoseProof (struct_val_rel_litint_source with H) as "->" |
         iPoseProof (struct_val_rel_litbool_source with H) as "->" |
         iPoseProof (struct_val_rel_litfn_source with H) as "->" |
         iPoseProof (struct_val_rel_litunit_source with H) as "->" |
         iPoseProof (struct_val_rel_litpoison_source with H) as "->" |
         idtac].
Tactic Notation "val_discr_target" constr(H) :=
  first [iPoseProof (struct_val_rel_litint_target with H) as "->" |
         iPoseProof (struct_val_rel_litbool_target with H) as "->" |
         iPoseProof (struct_val_rel_litfn_target with H) as "->" |
         iPoseProof (struct_val_rel_litunit_target with H) as "->" |
         iPoseProof (struct_val_rel_litpoison_target with H) as "->" |
         idtac].

Section log_rel.
  Context `{!sheapGS Σ} `{!sheapInv Σ}.
  Context (loc_rel : loc → loc → iProp Σ) `{!∀ l_t l_s, Persistent (loc_rel l_t l_s)}.
  Context (thread_own : thread_id → iProp Σ).
  Notation val_rel := (struct_val_rel loc_rel) (only parsing).
  Notation log_rel := (log_rel val_rel thread_own) (only parsing).

  Lemma val_wf_sound v : val_wf v → ⊢ val_rel v v.
  Proof.
    intros Hv.
    iInduction v as [[] | | | ] "IH"; try by (simpl; try iApply "IH").
    simpl. destruct Hv as [H1 H2]. iSplit; [by iApply "IH" | by iApply "IH1"].
  Qed.

  Local Lemma call_not_val v1 v2 : language.to_val (Call v1 v2) = None.
  Proof.
    rewrite /language.to_val /language.to_class; cbn.
    destruct to_fname; [destruct to_val | ]; done.
  Qed.

  Lemma struct_val_rel_val_is_unboxed v_t v_s : val_rel v_t v_s -∗ ⌜val_is_unboxed v_t ↔ val_is_unboxed v_s⌝.
  Proof.
    iIntros "Hv".
    destruct v_s as [[] | | | ]; val_discr_source "Hv"; [ done .. | |done | | |].
    - by iPoseProof (struct_val_rel_loc_source with "Hv") as (?) "(-> & _)".
    - by iPoseProof (struct_val_rel_pair_source with "Hv") as (??) "(-> & Hv1 & Hv2)".
    - iPoseProof (struct_val_rel_injl_source with "Hv") as (?) "(-> & Hv)".
      destruct v_s as [[] | | | ]; val_discr_source "Hv"; [done.. | | done | | |].
      + by iPoseProof (struct_val_rel_loc_source with "Hv") as (?) "(-> & _)".
      + by iPoseProof (struct_val_rel_pair_source with "Hv") as (??) "(-> & Hv1 & Hv2)".
      + by iPoseProof (struct_val_rel_injl_source with "Hv") as (?) "(-> & Hv)".
      + by iPoseProof (struct_val_rel_injr_source with "Hv") as (?) "(-> & Hv)".
    - iPoseProof (struct_val_rel_injr_source with "Hv") as (?) "(-> & Hv)".
      destruct v_s as [[] | | | ]; val_discr_source "Hv"; [done.. | | done | | |].
      + by iPoseProof (struct_val_rel_loc_source with "Hv") as (?) "(-> & _)".
      + by iPoseProof (struct_val_rel_pair_source with "Hv") as (??) "(-> & Hv1 & Hv2)".
      + by iPoseProof (struct_val_rel_injl_source with "Hv") as (?) "(-> & Hv)".
      + by iPoseProof (struct_val_rel_injr_source with "Hv") as (?) "(-> & Hv)".
  Qed.

  Local Tactic Notation "smart_sim_bind" uconstr(ctx_t) uconstr(ctx_s) uconstr(Hp) :=
    sim_bind ctx_t ctx_s;
    iApply (sim_wand with Hp).

  Lemma log_rel_var x : ⊢ log_rel (Var x) (Var x).
  Proof.
    iIntros (? xs) "!# Hs Ht"; simpl.
    iDestruct (subst_map_rel_lookup _ x with "Hs") as (v_t v_s Hv) "Hrel"; first set_solver.
    rewrite !lookup_fmap Hv /=. sim_val. by iFrame.
  Qed.

  Lemma log_rel_let x e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Let x e1_t e2_t) (Let x e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht #Hv]". sim_pures. rewrite !subst'_subst_map.
    rewrite -(binder_insert_fmap fst (v_t, v_s)).
    rewrite -(binder_insert_fmap snd (v_t, v_s)).
    iApply ("IH2" with "[] Ht").
    iApply (subst_map_rel_insert with "[] Hv").
    iApply (subst_map_rel_weaken with "[$]").
    destruct x as [|x]; first set_solver.
    apply elem_of_subseteq=>x'.
    destruct (decide (x = x')) as [<-|Hne]; set_solver.
  Qed.

  Lemma log_rel_call e1_t e1_s e2_t e2_s :
    (∀ π v_t v_s, ext_rel π v_t v_s ⊣⊢ thread_own π ∗ val_rel v_t v_s) →
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Call e1_t e2_t) (Call e1_s e2_s).
  Proof.
    iIntros (Hext) "#IH1 #IH2". iIntros (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[Ht #Hv1]".
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[Ht #Hv2]".
    discr_source; first by apply call_not_val. val_discr_source "Hv2".
    iApply (sim_wand with "[Ht]"); [ iApply sim_call; [done..|]| iIntros (??) "?"]; rewrite Hext; by iFrame.
  Qed.

  Lemma log_rel_unop e_t e_s o :
    log_rel e_t e_s -∗ log_rel (UnOp o e_t) (UnOp o e_s).
  Proof.
    iIntros "#IH" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht #Hv]".
    destruct o; sim_pures; discr_source; val_discr_source "Hv"; sim_pures; sim_val; by iFrame.
  Qed.

  Lemma log_rel_binop e1_t e1_s e2_t e2_s o :
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (BinOp o e1_t e2_t) (BinOp o e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[Ht Hv2]".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[Ht Hv1]".
    destruct o; sim_pures; discr_source; val_discr_source "Hv1"; val_discr_source "Hv2"; sim_pures; [sim_val; by iFrame .. | | ].
    - iAssert (⌜vals_compare_safe v_t1 v_t2⌝)%I as "%".
      { iPoseProof (struct_val_rel_val_is_unboxed with "Hv1") as "%Hv1".
        iPoseProof (struct_val_rel_val_is_unboxed with "Hv2") as "%Hv2".
        iPureIntro. by rewrite /vals_compare_safe Hv1 Hv2.
      }
      case_bool_decide; subst; sim_pures; sim_val; iFrame.
      * admit.
        (* iPoseProof (struct_val_rel_inj with "Hv1 Hv2") as "->". *)
        (* sim_pures; sim_val. case_bool_decide; done. *)
      * admit.
        (* sim_pures; sim_val. case_bool_decide; subst; last done. *)
        (* by iPoseProof (val_rel_func with "Hv1 Hv2") as "->". *)
    - iPoseProof (struct_val_rel_loc_source with "Hv1") as (l_t) "(-> & Hl)".
      sim_pures. sim_val. iModIntro; cbn.
      admit.
      (* by iApply heap_bij_loc_shift. *)
  Admitted.

  Lemma log_rel_if e1_t e1_s e2_t e2_s e3_t e3_s :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel e3_t e3_s -∗
    log_rel (If e1_t e2_t e3_t) (If e1_s e2_s e3_s).
  Proof.
    iIntros "#IH1 #IH2 #IH3" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    discr_source. val_discr_source "Hv". destruct x; sim_pures.
    + iApply ("IH2" with "[] Ht"). iApply (subst_map_rel_weaken with "[$]"). set_solver.
    + iApply ("IH3" with "[] Ht"). iApply (subst_map_rel_weaken with "[$]"). set_solver.
  Qed.

  Lemma log_rel_while e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (While e1_t e2_t) (While e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    iApply (sim_while_while _ _ _ _ _ (thread_own π)%I with "[$]").
    iModIntro; iIntros "Ht".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    discr_source. val_discr_source "Hv". destruct x; sim_pures.
    + smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] Ht)".
      { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
      iIntros (? ?) "[Ht _]"; sim_pures. iApply sim_expr_base. iRight. by eauto.
    + iApply sim_expr_base. iLeft. iExists #(), #(); eauto.
  Qed.

  Lemma log_rel_pair e1_t e1_s e2_t e2_s :
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (Pair e1_t e2_t) (Pair e1_s e2_s).
  Proof.
    iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t2 v_s2) "[Ht Hv2]".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t1 v_s1) "[Ht Hv1]".
    sim_pures; sim_val. by iFrame.
  Qed.

  Lemma log_rel_fst e_t e_s :
    log_rel e_t e_s -∗ log_rel (Fst e_t) (Fst e_s).
  Proof.
    iIntros "#IH" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    discr_source.
    iPoseProof (struct_val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; sim_pures; sim_val; by iFrame.
  Qed.
  Lemma log_rel_snd e_t e_s :
    log_rel e_t e_s -∗ log_rel (Snd e_t) (Snd e_s).
  Proof.
    iIntros "#IH" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    discr_source.
    iPoseProof (struct_val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; sim_pures; sim_val; by iFrame.
  Qed.

  Lemma log_rel_injl e_t e_s :
    log_rel e_t e_s -∗ log_rel (InjL e_t) (InjL e_s).
  Proof.
    iIntros "#IH" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]"; sim_pures; sim_val; by iFrame.
  Qed.
  Lemma log_rel_injr e_t e_s :
    log_rel e_t e_s -∗ log_rel (InjR e_t) (InjR e_s).
  Proof.
    iIntros "#IH" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]"; sim_pures; sim_val; by iFrame.
  Qed.

  Lemma log_rel_match e_t e_s e1_t e1_s e2_t e2_s x1 x2 :
    log_rel e_t e_s -∗
    log_rel e1_t e1_s -∗
    log_rel e2_t e2_s -∗
    log_rel (Match e_t x1 e1_t x2 e2_t) (Match e_s x1 e1_s x2 e2_s).
  Proof.
    iIntros "#IH #IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e_t) (subst_map _ e_s)  "(IH [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht #Hv]".
    discr_source.
    + iPoseProof (struct_val_rel_injl_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
      rewrite !subst'_subst_map.
      rewrite -(binder_insert_fmap fst (v_t', x)).
      rewrite -(binder_insert_fmap snd (v_t', x)).
      iApply ("IH1" with "[] Ht").
      iApply (subst_map_rel_insert with "[] [//]").
      iApply (subst_map_rel_weaken with "[$]").
      destruct x1 as [|x1]; first set_solver.
      apply elem_of_subseteq=>x'.
      destruct (decide (x1 = x')) as [<-|Hne]; set_solver.
    + iPoseProof (struct_val_rel_injr_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
      rewrite !subst'_subst_map.
      rewrite -(binder_insert_fmap fst (v_t', x)).
      rewrite -(binder_insert_fmap snd (v_t', x)).
      iApply ("IH2" with "[] Ht").
      iApply (subst_map_rel_insert with "[] [//]").
      iApply (subst_map_rel_weaken with "[$]").
      destruct x2 as [|x2]; first set_solver.
      apply elem_of_subseteq=>x'.
      destruct (decide (x2 = x')) as [<-|Hne]; set_solver.
  Qed.

  Lemma log_rel_fork e_t e_s :
    (∀ e_s e_t π Ψ,
     thread_own π -∗
     (thread_own π -∗ #() ⪯{π} #() [{ Ψ }]) -∗
     (∀ π', thread_own π' -∗ e_t ⪯{π'} e_s {{ λ v_t v_s, thread_own π' ∗ val_rel v_t v_s }}) -∗
     Fork e_t ⪯{π} Fork e_s [{ Ψ }]) →
    log_rel e_t e_s -∗ log_rel (Fork e_t) (Fork e_s).
  Proof.
    iIntros (Hfork). iIntros "#IH" (? xs) "!# #Hs Ht"; simpl.
    iApply (Hfork with "Ht"); first by iIntros "?"; sim_pures; sim_val; iFrame.
    iIntros (?) "Ht". iApply (sim_wand with "(IH [] Ht)"); eauto.
  Qed.

  Lemma log_rel_allocN e1_t e1_s e2_t e2_s :
    (∀ (n : Z) v_t v_s π Ψ, (0 < n)%Z →
     thread_own π -∗ val_rel v_t v_s -∗
     (∀ l_t l_s, thread_own π -∗ loc_rel l_t l_s -∗ #l_t ⪯{π} #l_s [{ Ψ }]) -∗
     AllocN #n v_t ⪯{π} AllocN #n v_s [{ Ψ }]) →
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (AllocN e1_t e2_t) (AllocN e1_s e2_s).
  Proof.
    iIntros (Halloc). iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t' v_s') "[Ht Hv']".
    discr_source. val_discr_source "Hv'".
    iApply (Halloc with "Ht Hv"); [done|].
    iIntros (l_t l_s) "Ht Hl". sim_val. by iFrame.
  Qed.

  Lemma log_rel_freeN e1_t e1_s e2_t e2_s :
    (∀ (n : Z) l_t l_s π Ψ, (0 < n)%Z →
     thread_own π -∗ loc_rel l_t l_s -∗
     (thread_own π -∗ #() ⪯{π} #() [{ Ψ }]) -∗
     FreeN #n #l_t ⪯{π} FreeN #n #l_s [{ Ψ }]) →
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (FreeN e1_t e2_t) (FreeN e1_s e2_s).
  Proof.
    iIntros (Hfree). iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]".
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t' v_s') "[Ht Hv']".
    discr_source. iPoseProof (struct_val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
    iPoseProof (struct_val_rel_litint_source with "Hv'") as "->".
    iApply (Hfree with "Ht Hrel"); [done|].
    iIntros "Ht". sim_val. by iFrame.
  Qed.

  Lemma log_rel_load o e_t e_s :
    (∀ l_t l_s π Ψ,
     thread_own π -∗ loc_rel l_t l_s -∗
     (∀ v_t v_s, thread_own π -∗ val_rel v_t v_s -∗ v_t ⪯{π} v_s [{ Ψ }]) -∗
     Load o #l_t ⪯{π} Load o #l_s [{ Ψ }]) →
    log_rel e_t e_s -∗ log_rel (Load o e_t) (Load o e_s).
  Proof.
    iIntros (Hload). iIntros "#IH" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]". discr_source.
    iPoseProof (struct_val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
    iApply (Hload with "Ht Hrel").
    iIntros (v_t v_s) "Ht Hrel". sim_val; by iFrame.
  Qed.

  Lemma log_rel_store o e1_t e1_s e2_t e2_s :
    (∀ l_t l_s v_s v_t π Ψ,
     thread_own π -∗ loc_rel l_t l_s -∗ val_rel v_t v_s -∗
     (thread_own π -∗ #() ⪯{π} #() [{ Ψ }]) -∗
     Store o #l_t v_t ⪯{π} Store o #l_s v_s [{ Ψ }]) →
    log_rel e1_t e1_s -∗ log_rel e2_t e2_s -∗ log_rel (Store o e1_t e2_t) (Store o e1_s e2_s).
  Proof.
    iIntros (Hstore). iIntros "#IH1 #IH2" (? xs) "!# #Hs Ht"; simpl.
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t v_s) "[Ht Hv]". (* FIXME: fix printing *)
    smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] Ht)".
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (v_t' v_s') "[Ht Hv']".
    discr_source. iPoseProof (struct_val_rel_loc_source with "Hv'") as (l_t) "(-> & Hrel)".
    iApply (Hstore with "Ht Hrel Hv").
    iIntros "Ht". sim_val; by iFrame.
  Qed.

  Lemma log_rel_val v_t v_s :
    val_rel v_t v_s -∗ log_rel (Val v_t) (Val v_s).
  Proof. iIntros "#Hv" (? xs) "!# #Hs Ht"; simpl. sim_val; by iFrame. Qed.

  Definition pure_expr_wf (e : expr) : Prop :=
    match e with
    | Val v => val_wf v
    | Var _ | Let _ _ _ | UnOp _ _ | BinOp _ _ _ | If _ _ _ | While _ _
    | Pair _ _ | Fst _ | Snd _ | InjL _ | InjR _ | Match _ _ _ _ _ => True
    | _ => False
    end.

  Theorem pure_expr_wf_sound : log_rel_exprs pure_expr_wf val_rel thread_own.
  Proof.
    intros e_t e_s Hwf Hs. iIntros "IH".
    destruct e_t; simpl in Hs; destruct e_s => //=; simpl in Hs; simplify_eq.
    all: try iDestruct "IH" as "[IH IH1]".
    all: try iDestruct "IH1" as "[IH1 IH2]".
    all: try iDestruct "IH2" as "[IH2 IH3]".
    - (* Val *) iApply log_rel_val. by iApply val_wf_sound.
    - (* Var *) by iApply log_rel_var.
    - (* Let *) by iApply (log_rel_let with "IH IH1").
    - (* UnOp *) by iApply (log_rel_unop with "IH").
    - (* BinOp *) by iApply (log_rel_binop with "IH IH1").
    - (* If *) by iApply (log_rel_if with "IH IH1 IH2").
    - (* While *) by iApply (log_rel_while with "IH IH1").
    - (* Pairs *) by iApply (log_rel_pair with "IH IH1").
    - (* Fst *) by iApply (log_rel_fst with "IH").
    - (* Snd *) by iApply (log_rel_snd with "IH").
    - (* InjL *) by iApply (log_rel_injl with "IH").
    - (* InjR *) by iApply (log_rel_injr with "IH").
    - (* Match *) destruct_and!; simplify_eq.
      by iApply (log_rel_match with "IH IH1 IH2").
  Qed.
End log_rel.
