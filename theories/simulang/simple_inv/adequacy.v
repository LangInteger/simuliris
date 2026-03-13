(** The logical relation implies contextual refinement. *)

From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.
From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls closed_sim gen_log_rel adequacy.
From simuliris.simulang Require Import proofmode tactics pure_refl.
From simuliris.simulang Require Import gen_adequacy behavior wf gen_refl log_rel_structural.
From simuliris.simulang.simple_inv Require Import inv refl.
From iris.prelude Require Import options.

(** Whole-program adequacy. *)
Class simpleGpreS Σ := {
  sbij_pre_heapG :: sheapGpreS Σ;
  sbij_pre_bijG :: heapbijGpreS Σ;
}.
Definition simpleΣ := #[sheapΣ; heapbijΣ].
Global Instance subG_sbijΣ Σ :
  subG simpleΣ Σ → simpleGpreS Σ.
Proof. solve_inG. Qed.

Lemma prog_rel_adequacy Σ `{!simpleGpreS Σ} (p_t p_s : prog):
  isat (∀ `(simpleGS Σ) gs,
    ⌜map_Forall (λ _ v, val_wf v) gs⌝ -∗
    ([∗ map] f ↦ fn ∈ p_t, f @t fn) -∗
    ([∗ map] f ↦ fn ∈ p_s, f @s fn) -∗
    target_globals (dom gs) -∗
    source_globals (dom gs) ==∗
    ([∗ map] v∈gs, val_rel v v) ∗ prog_rel p_t p_s
  ) →
  prog_ref p_t p_s.
Proof.
  intros Hprog. apply simplang_adequacy.
  eapply sat_mono, Hprog. clear Hprog.
  iIntros "Hprog_rel % %gs %".
  iMod (heapbij_init (λ _ _ q, q = Some 1%Qp)) as (?) "Hbij". iModIntro.
  set HΣ := (SimpleGS Σ _ _).
  iExists simple_inv, heapbij.loc_rel.
  iSpecialize ("Hprog_rel" $! HΣ).
  iIntros "Hp_t Hp_s Hmt #Hgs_t #Hgs_s".
  iMod ("Hprog_rel" with "[//] [$] [$] [$] [$]") as "[#Hvs $]".
  iMod (heapbij_insert_globals with "Hbij Hmt Hvs") as (L') "[Hbij #Hls]"; [done| ].
  iModIntro. iSplitL "Hbij"; [|iSplitR; [done|]].
  - iExists _. iFrame. iExists _,_. by iFrame "#".
  - iIntros (??) "$".
Qed.


(** Adequacy for open terms. *)
Theorem log_rel_adequacy Σ `{!simpleGpreS Σ} e_t e_s :
  (∀ `(simpleGS Σ), ⊢ log_rel e_t e_s) →
  ctx_ref e_t e_s.
Proof.
  intros Hrel C fname x p Hpwf HCwf Hvars.
  apply (prog_rel_adequacy Σ). eapply isat_intro.
  iIntros (? gs Hgs) "_ _ _ _ !#".
  iSplit.
  { iApply big_sepM_intro. iIntros "!>" (???). iApply val_wf_sound. by apply: Hgs. }
  iApply prog_rel_refl_insert.
  - iModIntro. iApply log_rel_func; first done.
    iApply log_rel_ctx; first done. iApply Hrel.
  - iIntros "!# %f %fn %Hfn". destruct fn as [arg body].
    destruct (Hpwf _ _ Hfn) as [Hfn_wf Hfn_vars].
    iApply log_rel_func; first set_solver.
    iApply log_rel_refl. done.
Qed.

Definition func_rel_1 `{sheapGS Σ} `{!simulirisGS (iPropI Σ) simp_lang} (fn_t fn_s : func) (gs : gmap string val): iProp Σ :=
  ∀ v_t v_s π, ext_rel π v_t v_s -∗
    target_globals (dom gs) -∗
    source_globals (dom gs) -∗
    (apply_func fn_t v_t) ⪯{π} (apply_func fn_s v_s) {{ ext_rel π }}.

Definition prog_rel_1 `{sheapGS Σ} `{!simulirisGS (iPropI Σ) simp_lang} (P_t : gmap fname func) (P_s : gmap fname func) (gs : gmap string val): iProp Σ :=
  □ ∀ f fn_s, ⌜P_s !! f = Some fn_s⌝ →
    target_globals (dom gs) -∗
    source_globals (dom gs) -∗
    ∃ fn_t, ⌜P_t !! f = Some fn_t⌝ ∗ func_rel_1 fn_t fn_s gs.

(* simpleGS has sheapGS *)
(* replace simpleGS by sheapGS all the way *)
Lemma simplang_adequacy_1 `{sheapGpreS Σ} p_t p_s :
  isat (∀ `(sheapGS Σ) gs,
    ⌜map_Forall (λ _ v, val_wf v) gs⌝ -∗
    |==> ∃ `(sheapInv Σ) loc_rel,
    ([∗ map] f ↦ fn ∈ p_t, f @t fn) -∗
    ([∗ map] f ↦ fn ∈ p_s, f @s fn) -∗
    ([∗ map] n↦v ∈ gs,
      global_loc n ↦t v ∗ target_block_size (global_loc n) (Some 1) ∗
      global_loc n ↦s v ∗ source_block_size (global_loc n) (Some 1)
    ) -∗ 
    target_globals (dom gs) -∗
    source_globals (dom gs) ==∗
    sheap_inv p_s (state_init gs) [Call f#"main" #()] ∗
    ext_rel 0 #() #() ∗
    (∀ v_t v_s, ext_rel 0 v_t v_s -∗ gen_val_rel loc_rel v_t v_s) ∗
    prog_rel_1 p_t p_s gs
  ) →
  prog_ref p_t p_s.
Proof.
  intros Hrel. eapply (slsls_adequacy (sat:=isat)).
  eapply sat_mono, Hrel. clear Hrel.
  iIntros "Hprog_rel %σ_t %σ_s (%gs&%&->&->)".
  iMod (sheap_init p_t _ p_s _) as (HsheapGS) "Hinit".
  iMod ("Hprog_rel" $! HsheapGS gs with "[//]") as (HsheapInv loc_rel) "Hprog_rel".
  iDestruct ("Hinit" $! HsheapInv) as "(Hstate & Hp_t & Hmt_t & Hp_s & Hmt_s & #Hgs_s & #Hgs_t & Hprogs_are)".
  iMod ("Hprog_rel" with "Hp_t Hp_s [Hmt_t Hmt_s] Hgs_t Hgs_s") as "(Hinv & Hunit & Hobs & #Hprog_rel)".
  { rewrite !big_sepM_sep. iFrame. }
  iModIntro. iExists sheapGS_simulirisGS.
  iSplitL "Hprog_rel".
  { unfold prog_rel. iIntros "!# %f %fn_s %Hpsf". iSpecialize ("Hprog_rel" $! f fn_s Hpsf). 
    iDestruct ("Hprog_rel" with "Hgs_t Hgs_s") as (fn_t) "[%Hpt Hfr1]".
    iExists fn_t.
    iSplit. 
    - iPureIntro. exact Hpt.
    - unfold func_rel.
      iIntros (v_t v_s π) "Hext".
      iApply ("Hfr1" with "Hext Hgs_t Hgs_s").
  }
  iFrame "Hprogs_are Hunit".
  iSplitR "Hobs".
  - iApply "Hstate". done.
  - iIntros (??) "Hext". iApply gen_val_rel_obs. iApply "Hobs". done. 
Qed.

Lemma prog_rel_adequacy_1 Σ `{!simpleGpreS Σ} (p_t p_s : prog):
  isat (∀ `(simpleGS Σ) gs,
    ⌜map_Forall (λ _ v, val_wf v) gs⌝ -∗
    ([∗ map] f ↦ fn ∈ p_t, f @t fn) -∗
    ([∗ map] f ↦ fn ∈ p_s, f @s fn) -∗
    target_globals (dom gs) -∗
    source_globals (dom gs) ==∗
    ([∗ map] v∈gs, val_rel v v) ∗ prog_rel_1 p_t p_s gs
  ) →
  prog_ref p_t p_s.
Proof.
  intros Hprog. apply simplang_adequacy_1.
  eapply sat_mono, Hprog. clear Hprog.
  iIntros "Hprog_rel % %gs %".
  iMod (heapbij_init (λ _ _ q, q = Some 1%Qp)) as (?) "Hbij". iModIntro.
  set HΣ := (SimpleGS Σ _ _).
  iExists simple_inv, heapbij.loc_rel.
  iSpecialize ("Hprog_rel" $! HΣ).
  iIntros "Hp_t Hp_s Hmt #Hgs_t #Hgs_s".
  iMod ("Hprog_rel" with "[//] [$] [$] [$] [$]") as "[#Hvs $]".
  iMod (heapbij_insert_globals with "Hbij Hmt Hvs") as (L') "[Hbij #Hls]"; [done| ].
  iModIntro. iSplitL "Hbij"; [|iSplitR; [done|]].
  - iExists _. iFrame. iExists _,_. by iFrame "#".
  - iIntros (??) "$".
Qed.

Definition gen_log_rel_1 `{simpleGS Σ} e_t e_s  : iProp Σ :=
  □ ∀ π (map : gmap string (val * val)) (gs : gmap string val),
    target_globals (dom gs) -∗
    source_globals (dom gs) -∗
    subst_map_rel val_rel (free_vars e_t ∪ free_vars e_s) map -∗
    True -∗
    subst_map (fst <$> map) e_t ⪯{π} subst_map (snd <$> map) e_s
      {{ λ v_t v_s, True ∗ val_rel v_t v_s }}.

Definition log_rel_structural_1 `{simpleGS Σ} (expr_head_wf : expr_head → Prop) : Prop := (∀ e_t e_s,
   let head_t := expr_split_head e_t in
   let head_s := expr_split_head e_s in
   expr_head_wf head_s.1 →
   head_s.1 = head_t.1 →
   ([∗list] e_t';e_s' ∈ head_t.2; head_s.2, gen_log_rel_1 e_t' e_s') -∗
   gen_log_rel_1 e_t e_s).

Locate gen_log_rel_refl.
Theorem gen_log_rel_refl_1 `{simpleGS Σ} e (expr_head_wf : expr_head → Prop) :
  log_rel_structural_1 expr_head_wf →
  gen_expr_wf expr_head_wf e →
  ⊢ gen_log_rel_1 e e.
Proof.
  intros He Hwf.
  iInduction e as [ ] "IH" forall (Hwf); destruct Hwf; iApply He. 
  all: try iDestruct ("IH" with "[%]") as "$".
  all: try iDestruct ("IH1" with "[%]") as "$".
  all: try iDestruct ("IH2" with "[%]") as "$".
  all: naive_solver.
Qed.

Local Tactic Notation "smart_sim_bind" uconstr(ctx_t) uconstr(ctx_s) uconstr(Hp) :=
  sim_bind ctx_t ctx_s;
  iApply (sim_wand with Hp).

Locate log_rel_call.
Lemma log_rel_call_1 `{simpleGS Σ}  e1_t e1_s e2_t e2_s :
  (∀ π v_t v_s, ext_rel π v_t v_s ⊣⊢ True ∗ val_rel v_t v_s) →
  gen_log_rel_1 e1_t e1_s -∗ gen_log_rel_1 e2_t e2_s -∗ gen_log_rel_1 (Call e1_t e2_t) (Call e1_s e2_s).
Proof.
  rewrite /gen_log_rel.
  iIntros (Hext) "#IH1 #IH2". iIntros (? xs gs) "!# #Htg #Hst #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t1 v_s1) "[Ht #Hv1]".
  smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t2 v_s2) "[Ht #Hv2]".
  discr_source. val_discr_source "Hv2".
  iApply (sim_call with "[Ht]"); [done..| rewrite Hext; by iFrame| ].
  iIntros (??) "?". iApply lift_post_val. rewrite Hext. by iFrame.
Qed.

Lemma log_rel_val `{simpleGS Σ} v_t v_s :
  val_rel v_t v_s -∗ gen_log_rel_1 (Val v_t) (Val v_s).
Proof.
  rewrite /gen_log_rel.
  iIntros "#Hv" (? xs gs) "!# Hgs Hgt Hs Ht"; simpl. sim_val; by iFrame.
Qed.

Locate log_rel_let.
Lemma log_rel_var `{simpleGS Σ} x : ⊢ gen_log_rel_1 (Var x) (Var x).
Proof.
  rewrite /gen_log_rel.
  iIntros (? xs gs) "!# Hgs Hgt Hs Ht"; simpl.
  iDestruct (subst_map_rel_lookup _ x with "Hs") as (v_t v_s Hv) "Hrel"; first set_solver.
  rewrite !lookup_fmap Hv /=. sim_val. by iFrame.
Qed.

Locate pure_log_rel_structural.
Check sheap_inv_contains_globalbij.
Locate sim_global_var.
Lemma log_rel_global_var `{simpleGS Σ} x :
  sheap_inv_contains_globalbij heapbij.loc_rel →
  ⊢ gen_log_rel_1 (GlobalVar x) (GlobalVar x).
Proof.
  rewrite /log_rel /gen_log_rel.
  iIntros (Hrel ? xs gs) "!# Hgs Hgt Hs Ht"; simpl.
  iApply (sim_global_var heapbij.loc_rel); first done. iIntros (??) "Hrel".
  iApply lift_post_val. iFrame.
Qed.

Lemma log_rel_let `{simpleGS Σ} x e1_t e1_s e2_t e2_s :
  gen_log_rel_1 e1_t e1_s -∗ gen_log_rel_1 e2_t e2_s -∗ gen_log_rel_1 (Let x e1_t e2_t) (Let x e1_s e2_s).
Proof.
  unfold gen_log_rel_1.
  iIntros "#IH1 #IH2" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] [] [Hs] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t v_s) "[Ht #Hv]". sim_pures. rewrite !subst'_subst_map.
  rewrite -(binder_insert_fmap fst (v_t, v_s)).
  rewrite -(binder_insert_fmap snd (v_t, v_s)).
  iApply ("IH2" with "[] [] [] Ht"); eauto.
  iApply (subst_map_rel_insert with "[]  [Hv]"); last done.
  iApply (subst_map_rel_weaken with "[$]").
  destruct x as [|x]; first set_solver.
  apply elem_of_subseteq=>x'.
  destruct (decide (x = x')) as [<-|Hne]; set_solver.
Qed.

Lemma log_rel_unop `{simpleGS Σ} e_t e_s o :
  gen_log_rel_1 e_t e_s -∗ gen_log_rel_1 (UnOp o e_t) (UnOp o e_s).
Proof.
  unfold gen_log_rel_1.
  iIntros "#IH" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] [] [Hs] Ht)"; eauto.
  (* { iApply (subst_map_rel_weaken with "[$]"). set_solver. } *)
  iIntros (v_t v_s) "[Ht Hv]".
  destruct o; sim_pures; discr_source; val_discr_source "Hv"; sim_pures; sim_val; by iFrame.
Qed.

Lemma log_rel_binop `{simpleGS Σ} e1_t e1_s e2_t e2_s o :
  loc_rel_func_law heapbij.loc_rel →
  loc_rel_inj_law heapbij.loc_rel →
  loc_rel_offset_law heapbij.loc_rel →
  gen_log_rel_1 e1_t e1_s -∗ gen_log_rel_1 e2_t e2_s -∗ gen_log_rel_1 (BinOp o e1_t e2_t) (BinOp o e1_s e2_s).
Proof.
  unfold gen_log_rel_1.
  iIntros (Hfunc Hinj Hshift). iIntros "#IH1 #IH2" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t2 v_s2) "[Ht Hv2]".
  smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t1 v_s1) "[Ht Hv1]".
  destruct o; sim_pures; discr_source; try val_discr_source "Hv1"; try val_discr_source "Hv2"; sim_pures; try (sim_val; by iFrame); [| | |].
  - (* Quot *)
    source_binop.
    { rewrite /bin_op_eval /=. rewrite decide_False //. }
    target_binop.
    { rewrite /bin_op_eval /=. rewrite decide_False //. }
    sim_val; by iFrame.
  - (* Rem *)
    source_binop.
    { rewrite /bin_op_eval /=. rewrite decide_False //. }
    target_binop.
    { rewrite /bin_op_eval /=. rewrite decide_False //. }
    sim_val; by iFrame.
  - (* Eq *)
    iAssert (⌜vals_compare_safe v_t1 v_t2⌝)%I as "%".
    { iPoseProof (gen_val_rel_val_is_unboxed with "Hv1") as "%Hv1".
      iPoseProof (gen_val_rel_val_is_unboxed with "Hv2") as "%Hv2".
      iPureIntro. by rewrite /vals_compare_safe Hv1 Hv2.
    }
    sim_pures; sim_val. iFrame. case_bool_decide; subst.
    * iDestruct (gen_val_rel_func with "Hv1 Hv2") as %->; [done|]. by case_bool_decide.
    * case_bool_decide; [|done]; subst. by iDestruct (gen_val_rel_inj with "Hv1 Hv2") as %?.
  - (* Offset *)
    sim_val. iModIntro; simpl. iFrame. by iApply Hshift.
Qed.

Lemma log_rel_if `{simpleGS Σ} e1_t e1_s e2_t e2_s e3_t e3_s :
  gen_log_rel_1 e1_t e1_s -∗
  gen_log_rel_1 e2_t e2_s -∗
  gen_log_rel_1 e3_t e3_s -∗
  gen_log_rel_1 (If e1_t e2_t e3_t) (If e1_s e2_s e3_s).
Proof.
  unfold gen_log_rel_1.
  iIntros "#IH1 #IH2 #IH3" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t v_s) "[Ht Hv]".
  discr_source. val_discr_source "Hv". rename select bool into b.
  destruct b; sim_pures.
  + iApply ("IH2" with "[] [] [] Ht"); eauto. iApply (subst_map_rel_weaken with "[$]"). set_solver.
  + iApply ("IH3" with "[] [] [] Ht"); eauto. iApply (subst_map_rel_weaken with "[$]"). set_solver.
Qed.

Lemma log_rel_while `{simpleGS Σ} e1_t e1_s e2_t e2_s :
  gen_log_rel_1 e1_t e1_s -∗
  gen_log_rel_1 e2_t e2_s -∗
  gen_log_rel_1 (While e1_t e2_t) (While e1_s e2_s).
Proof.
  unfold gen_log_rel_1.
  iIntros "#IH1 #IH2" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  iApply (sim_while_while True with "[$]"); eauto.
  iModIntro; iIntros "Ht".
  smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t v_s) "[Ht Hv]".
  discr_source. val_discr_source "Hv".
  rename select bool into b.
  destruct b; sim_pures.
  + smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] [] [] Ht)"; eauto.
    { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
    iIntros (? ?) "[Ht _]"; sim_pures. iApply sim_expr_base. iRight. by eauto.
  + iApply sim_expr_base. iLeft. iExists #(), #(); eauto.
Qed.


Lemma log_rel_pair `{simpleGS Σ} e1_t e1_s e2_t e2_s :
  gen_log_rel_1 e1_t e1_s -∗
  gen_log_rel_1 e2_t e2_s -∗
  gen_log_rel_1 (Pair e1_t e2_t) (Pair e1_s e2_s).
Proof.
  rewrite /gen_log_rel.
  iIntros "#IH1 #IH2" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t2 v_s2) "[Ht Hv2]".
  smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t1 v_s1) "[Ht Hv1]".
  sim_pures; sim_val. by iFrame.
Qed.

Lemma log_rel_fst `{simpleGS Σ} e_t e_s :
  gen_log_rel_1 e_t e_s -∗ gen_log_rel_1 (Fst e_t) (Fst e_s).
Proof.
  rewrite /gen_log_rel.
  iIntros "#IH" (? xs gs) "!# #Hgs #Hgt Hs Ht"; simpl.
  smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] [] [Hs] Ht)"; eauto.
  (* { iApply (subst_map_rel_weaken with "[$]"). set_solver. } *)
  iIntros (v_t v_s) "[Ht Hv]".
  discr_source.
  iPoseProof (gen_val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; sim_pures; sim_val; by iFrame.
Qed.

Lemma log_rel_snd `{simpleGS Σ} e_t e_s :
  gen_log_rel_1 e_t e_s -∗ gen_log_rel_1 (Snd e_t) (Snd e_s).
Proof.
  rewrite /gen_log_rel.
  iIntros "#IH" (? xs gs) "!# #Hgs #Hgt Hs Ht"; simpl.
  smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] [] [Hs] Ht)"; eauto.
  (* { iApply (subst_map_rel_weaken with "[$]"). set_solver. } *)
  iIntros (v_t v_s) "[Ht Hv]".
  discr_source.
  iPoseProof (gen_val_rel_pair_source with "Hv") as (??) "(-> & ? & ?)"; sim_pures; sim_val; by iFrame.
Qed.

Lemma log_rel_injl `{simpleGS Σ} e_t e_s :
  gen_log_rel_1 e_t e_s -∗ gen_log_rel_1 (InjL e_t) (InjL e_s).
Proof.
  unfold gen_log_rel_1.
  iIntros "#IH" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] [] [] Ht)"; eauto.
  iIntros (v_t v_s) "[Ht Hv]"; sim_pures; sim_val; by iFrame.
Qed.

Lemma log_rel_injr `{simpleGS Σ} e_t e_s :
  gen_log_rel_1 e_t e_s -∗ gen_log_rel_1 (InjR e_t) (InjR e_s).
Proof.
  unfold gen_log_rel_1.
  iIntros "#IH" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ e_t) (subst_map _ e_s) "(IH [] [] [] Ht)"; eauto.
  iIntros (v_t v_s) "[Ht Hv]"; sim_pures; sim_val; by iFrame.
Qed.

Lemma log_rel_match `{simpleGS Σ} e_t e_s e1_t e1_s e2_t e2_s x1 x2 :
  gen_log_rel_1 e_t e_s -∗
  gen_log_rel_1 e1_t e1_s -∗
  gen_log_rel_1 e2_t e2_s -∗
  gen_log_rel_1 (Match e_t x1 e1_t x2 e2_t) (Match e_s x1 e1_s x2 e2_s).
Proof.
  unfold gen_log_rel_1.
  iIntros "#IH #IH1 #IH2" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ e_t) (subst_map _ e_s)  "(IH [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t v_s) "[Ht #Hv]".
  discr_source.
  + iPoseProof (gen_val_rel_injl_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
    rewrite !subst'_subst_map.
    match goal with |- context[gen_val_rel loc_rel (InjLV ?vt) (InjLV ?vs)] =>
      rename vt into v_t'; rename vs into v_s'
    end.
    rewrite -(binder_insert_fmap fst (v_t', v_s')).
    rewrite -(binder_insert_fmap snd (v_t', v_s')).
    iApply ("IH1" with "[] [] [] Ht"); eauto.
    iApply (subst_map_rel_insert with "[] []"); last done.
    iApply (subst_map_rel_weaken with "[$]").
    destruct x1 as [|x1]; first set_solver.
    apply elem_of_subseteq=>x'.
    destruct (decide (x1 = x')) as [<-|Hne]; set_solver.
  + iPoseProof (gen_val_rel_injr_source with "Hv") as (v_t') "(-> & ?)". sim_pures.
    rewrite !subst'_subst_map.
    match goal with |- context[gen_val_rel loc_rel (InjRV ?vt) (InjRV ?vs)] =>
      rename vt into v_t'; rename vs into v_s'
    end.
    rewrite -(binder_insert_fmap fst (v_t', v_s')).
    rewrite -(binder_insert_fmap snd (v_t', v_s')).
    iApply ("IH2" with "[] [] [] Ht"); eauto.
    iApply (subst_map_rel_insert with "[] []"); last done.
    iApply (subst_map_rel_weaken with "[$]").
    destruct x2 as [|x2]; first set_solver.
    apply elem_of_subseteq=>x'.
    destruct (decide (x2 = x')) as [<-|Hne]; set_solver.
Qed.

Definition thread_own `{simpleGS Σ} : thread_id → iProp Σ := λ _ : thread_id, True%I.
Lemma log_rel_fork `{simpleGS Σ} e_t e_s :
  (∀ e_s e_t π Ψ,
   thread_own π -∗
   (thread_own π -∗ #() ⪯{π} #() [{ Ψ }]) -∗
   (∀ π', thread_own π' -∗ e_t ⪯{π'} e_s {{ λ v_t v_s, thread_own π' ∗ val_rel v_t v_s }}) -∗
   Fork e_t ⪯{π} Fork e_s [{ Ψ }]) →
  gen_log_rel_1 e_t e_s -∗ gen_log_rel_1 (Fork e_t) (Fork e_s).
Proof.
  unfold gen_log_rel_1.
  iIntros (Hfork). iIntros "#IH" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  iApply (Hfork with "Ht"); first by iIntros "?"; sim_pures; sim_val; iFrame.
  iIntros (?) "Ht". iApply (sim_wand with "(IH [] [] [] Ht)"); eauto.
Qed.

Lemma log_rel_allocN `{simpleGS Σ} e1_t e1_s e2_t e2_s :
  (∀ (n : Z) v_t v_s π Ψ, (0 < n)%Z →
   thread_own π -∗ val_rel v_t v_s -∗
   (∀ l_t l_s, thread_own π -∗ loc_rel l_t l_s -∗ #l_t ⪯{π} #l_s [{ Ψ }]) -∗
   AllocN #n v_t ⪯{π} AllocN #n v_s [{ Ψ }]) →
  gen_log_rel_1 e1_t e1_s -∗ gen_log_rel_1 e2_t e2_s -∗ gen_log_rel_1 (AllocN e1_t e2_t) (AllocN e1_s e2_s).
Proof.
  rewrite /gen_log_rel.
  iIntros (Halloc). iIntros "#IH1 #IH2" (? xs gs) "!# #Hs #Hgs #Hgt Ht"; simpl.
  smart_sim_bind (subst_map _ e2_t) (subst_map _ e2_s) "(IH2 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t v_s) "[Ht Hv]".
  smart_sim_bind (subst_map _ e1_t) (subst_map _ e1_s) "(IH1 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t' v_s') "[Ht Hv']".
  discr_source. val_discr_source "Hv'".
  iApply (Halloc with "Ht Hv"); [done|].
  iIntros (l_t l_s) "Ht Hl". sim_val. by iFrame.
Qed.

Lemma log_rel_freeN `{simpleGS Σ} e1_t e1_s e2_t e2_s :
  (∀ (n : Z) l_t l_s π Ψ, (0 < n)%Z →
   thread_own π -∗ loc_rel l_t l_s -∗
   (thread_own π -∗ #() ⪯{π} #() [{ Ψ }]) -∗
   FreeN #n #l_t ⪯{π} FreeN #n #l_s [{ Ψ }]) →
  gen_log_rel_1 e1_t e1_s -∗ gen_log_rel_1 e2_t e2_s -∗ gen_log_rel_1 (FreeN e1_t e2_t) (FreeN e1_s e2_s).
Proof.
  rewrite /gen_log_rel.
  iIntros (Hfree). iIntros "#IH1 #IH2" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t v_s) "[Ht Hv]".
  smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t' v_s') "[Ht Hv']".
  discr_source. iPoseProof (gen_val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
  iPoseProof (gen_val_rel_litint_source with "Hv'") as "->".
  iApply (Hfree with "Ht Hrel"); [done|].
  iIntros "Ht". sim_val. by iFrame.
Qed.

Lemma log_rel_load `{simpleGS Σ} o e_t e_s :
  (∀ l_t l_s π Ψ,
   thread_own π -∗ loc_rel l_t l_s -∗
   (∀ v_t v_s, thread_own π -∗ val_rel v_t v_s -∗ v_t ⪯{π} v_s [{ Ψ }]) -∗
   Load o #l_t ⪯{π} Load o #l_s [{ Ψ }]) →
  gen_log_rel_1 e_t e_s -∗ gen_log_rel_1 (Load o e_t) (Load o e_s).
Proof.
  unfold gen_log_rel_1.
  iIntros (Hload). iIntros "#IH" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH [] [] [] Ht)"; eauto.
  iIntros (v_t v_s) "[Ht Hv]". discr_source.
  iPoseProof (gen_val_rel_loc_source with "Hv") as (l_t) "(-> & Hrel)".
  iApply (Hload with "Ht Hrel").
  iIntros (v_t v_s) "Ht Hrel". sim_val; by iFrame.
Qed.

Lemma log_rel_store `{simpleGS Σ} o e1_t e1_s e2_t e2_s :
  (∀ l_t l_s v_s v_t π Ψ,
   thread_own π -∗ loc_rel l_t l_s -∗ val_rel v_t v_s -∗
   (thread_own π -∗ #() ⪯{π} #() [{ Ψ }]) -∗
   Store o #l_t v_t ⪯{π} Store o #l_s v_s [{ Ψ }]) →
  gen_log_rel_1 e1_t e1_s -∗ gen_log_rel_1 e2_t e2_s -∗ gen_log_rel_1 (Store o e1_t e2_t) (Store o e1_s e2_s).
Proof.
  unfold gen_log_rel_1.
  iIntros (Hstore). iIntros "#IH1 #IH2" (? xs gs) "!# #Hgs #Hgt #Hs Ht"; simpl.
  smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH2 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t v_s) "[Ht Hv]". (* FIXME: fix printing *)
  smart_sim_bind (subst_map _ _) (subst_map _ _) "(IH1 [] [] [] Ht)"; eauto.
  { iApply (subst_map_rel_weaken with "[$]"). set_solver. }
  iIntros (v_t' v_s') "[Ht Hv']".
  discr_source. iPoseProof (gen_val_rel_loc_source with "Hv'") as (l_t) "(-> & Hrel)".
  iApply (Hstore with "Ht Hrel Hv").
  iIntros "Ht". sim_val; by iFrame.
Qed.

Check gen_log_rel_1.
Lemma gen_log_rel_singleton `{simpleGS Σ} e_t e_s v_t v_s arg π (gs : gmap string val) :
  free_vars e_t ∪ free_vars e_s ⊆ {[ arg ]} →
  target_globals (dom gs) -∗
  source_globals (dom gs) -∗
  gen_log_rel_1 e_t e_s -∗
  val_rel v_t v_s -∗
  thread_own π -∗
  subst_map {[arg := v_t]} e_t ⪯{π} subst_map {[arg := v_s]} e_s
    {{ λ v_t v_s, thread_own π ∗ val_rel v_t v_s }}.
Proof.
  iIntros (?) "Hgt Hgs Hlog Hval Hπ".
  unfold gen_log_rel_1.
  iDestruct ("Hlog" $! _ {[arg := (v_t, v_s)]} gs with "[Hgt] [Hgs] [Hval] Hπ") as "Hsim"; eauto.
  { by iApply subst_map_rel_singleton. }
  rewrite !map_fmap_singleton. done.
Qed.

Lemma gen_log_rel_func `{simpleGS Σ} (x : string) e_t e_s (gs : gmap string val) :
  (∀ v_t v_s π, ext_rel π v_t v_s ⊣⊢ thread_own π ∗ val_rel v_t v_s) →
  free_vars e_t ∪ free_vars e_s ⊆ {[x]} →
  gen_log_rel_1 e_t e_s -∗
  func_rel_1 (pair x e_t) (pair x e_s) gs.
Proof.
    iIntros (Hext_val Hvars) "Hlog %v_t %v_s %π".
    rewrite Hext_val. iIntros "[Hthread Hval]". iIntros "Hgt Hgs".
    iApply (sim_wand with "[-]").
    - rewrite /= /apply_func /= -!subst_map_singleton.
      iApply (gen_log_rel_singleton with "Hgt Hgs Hlog Hval Hthread"); done.
    - iIntros "%vt0 %vs0 [Hto Hvalrel]". iApply Hext_val. iFrame.
Qed.

Theorem pure_log_rel_structural `{simpleGS Σ} :
  loc_rel_func_law loc_rel →
  loc_rel_inj_law loc_rel →
  loc_rel_offset_law loc_rel →
  sheap_inv_contains_globalbij loc_rel →
  log_rel_structural_1 pure_expr_head_wf.
Proof.
  intros ???? e_t e_s head_t head_s Hwf Hs. iIntros "IH".
  destruct e_t; simpl in Hs; destruct e_s => //=; simpl in Hs; simplify_eq.
  all: try iDestruct "IH" as "[IH IH1]".
  all: try iDestruct "IH1" as "[IH1 IH2]".
  all: try iDestruct "IH2" as "[IH2 IH3]".
  - (* Val *) iApply log_rel_val. by iApply val_wf_sound.
  - (* Var *) by iApply log_rel_var.
  - (* GlobalVar *) by iApply log_rel_global_var.
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
  - (* Match *) by iApply (log_rel_match with "IH IH1 IH2").
Qed.

Locate simple_log_rel_structural.
Theorem simple_log_rel_structural_1 `{simpleGS Σ} : log_rel_structural_1 simulang_wf.
Proof.
  intros e_t e_s ?? Hwf Hs. iIntros "IH".
  destruct e_s, e_t => //; simpl in Hs; simplify_eq.
  all: try by iApply pure_log_rel_structural; unfold loc_rel_func_law, loc_rel_inj_law, loc_rel_offset_law; eauto using heapbij_loc_func, heapbij_loc_inj, heapbij_loc_shift, sim_bij_contains_globalbij.
  all: try iDestruct "IH" as "[IH IH1]".
  all: try iDestruct "IH1" as "[IH1 IH2]".
  all: try iDestruct "IH2" as "[IH2 IH3]".
  - (* Call *)
    iApply (log_rel_call_1 with "IH IH1").
    iIntros (???). rewrite /= left_id. auto.
  - (* Fork *)
    iApply (log_rel_fork with "IH").
    iIntros (?????) "Hsim Hfork". iApply (sim_fork with "(Hsim [//])").
    iIntros (?). iApply (sim_wand with "[Hfork]"). { by iApply "Hfork". }
    iIntros (??). rewrite /= left_id. auto.
  - (* AllocN *)
    iApply (log_rel_allocN with "IH IH1").
    iIntros (n ??????) "Hv Hcont".
    target_alloc l_t as "Hl_t" "Ha_t"; first done.
    source_alloc l_s as "Hl_s" "Ha_s"; first done.
    iApply (sim_bij_insertN with "Ha_t Ha_s Hl_t Hl_s [Hv]"); [lia | by rewrite length_replicate.. | | ].
    { iDestruct "Hv" as "#Hv".
      rewrite big_sepL2_replicate_l; last by rewrite length_replicate.
      generalize (Z.to_nat n) => n'.
      iInduction n' as [] "IHn"; cbn; first done. iFrame "Hv IHn".
    }
    by iApply "Hcont".
  - (* FreeN *)
    iApply (log_rel_freeN with "IH IH1").
    iIntros (???????) "Hv Hcont". sim_free. by iApply "Hcont".
  - (* Load *)
    iApply (log_rel_load with "IH").
    iIntros (?????) "Hv Hcont". iApply (sim_bij_load with "Hv"). iIntros (??). by iApply "Hcont".
  - (* Store *)
    iApply (log_rel_store with "IH IH1").
    iIntros (???????) "Hl Hv Hcont". iApply (sim_bij_store with "Hl Hv"). by iApply "Hcont".
Qed.

Corollary log_rel_ctx `{simpleGS Σ} C e_t e_s :
  ctx_wf C →
  gen_log_rel_1 e_t e_s -∗ gen_log_rel_1 (fill_ctx C e_t) (fill_ctx C e_s).
Proof.
  intros Hwf. iInduction (C) as [ | Ci C] "IH" using rev_ind; first by eauto.
  iIntros "Hrel".
  rewrite ->gen_ctx_wf_snoc in Hwf. destruct Hwf as [Kwf [Hewf Hiwf]].
  iSpecialize ("IH" with "[//] Hrel").
  rewrite !fill_ctx_app /=.
  pose proof (simple_log_rel_structural_1) as He.
  destruct Ci; simpl; iApply He => //=; iFrame "IH".
  all: move: Hiwf; rewrite /= ?Forall_cons ?Forall_nil => Hiwf.
  all: repeat iSplit; try done.
  all: iApply gen_log_rel_refl_1; [done|].
  all: naive_solver.
Qed.

Corollary log_rel_refl `{simpleGS Σ} e :
  expr_wf e →
  ⊢ gen_log_rel_1 e e.
Proof.
  intros ?. iApply gen_log_rel_refl_1; first by apply simple_log_rel_structural_1. done.
Qed.

Lemma log_rel_func `{simpleGS Σ} (x : string) e_t e_s (gs : gmap string val) :
  free_vars e_t ∪ free_vars e_s ⊆ {[x]} →
  gen_log_rel_1 e_t e_s -∗
  func_rel_1 (pair x e_t) (pair x e_s) gs.
Proof.
  apply gen_log_rel_func.
  iIntros (v_t v_s π). rewrite /= left_id. eauto.
Qed.

Lemma prog_rel_refl_insert_1 `{sheapGS Σ} `{!simulirisGS (iPropI Σ) simp_lang} P (fname : string) (fn_t fn_s : func) (gs : gmap string val) :
  □ func_rel_1 fn_t fn_s gs -∗
  □ (∀ f fn, ⌜P !! f = Some fn⌝ -∗ func_rel_1 fn fn gs) -∗
  prog_rel_1 (<[fname:=fn_t]> P) (<[fname:=fn_s]> P) gs.
Proof.
  rewrite /prog_rel.
  iIntros "#He #Hp !# %f %fn".
  destruct (decide (f = fname)) as [->|Hne].
  - rewrite !lookup_insert_eq.
    iIntros ([= <-]). iIntros "Hgt Hgs". iExists _. iSplitR; done.
  - rewrite !lookup_insert_ne //.
    iIntros (Hf). iIntros "Hgt Hgs". iExists fn. iSplitR; first done.
    by iApply "Hp".
Qed.

Theorem log_rel_adequacy_1 Σ `{!simpleGpreS Σ} e_t e_s (gss : gmap string val) :
  (∀ `(simpleGS Σ), ⊢ 
    gen_log_rel_1 e_t e_s) →
  ctx_ref e_t e_s.
Proof.
  intros Hrel C fname x p Hpwf HCwf Hvars.
  apply (prog_rel_adequacy_1 Σ). eapply isat_intro.
  iIntros (? gs Hgs) "_ _ Hgs Hgt !#".
  iSplitR "Hgs Hgt".
  { iApply big_sepM_intro. iIntros "!>" (???). iApply val_wf_sound. by apply: Hgs. }
  iApply prog_rel_refl_insert_1.
  - iModIntro. iApply log_rel_func; first done.
    iApply log_rel_ctx; first done. iApply Hrel.
  - iIntros "!# %f %fn %Hfn". destruct fn as [arg body].
    destruct (Hpwf _ _ Hfn) as [Hfn_wf Hfn_vars].
    iApply log_rel_func; first set_solver.
    iApply log_rel_refl. done.
Qed.
