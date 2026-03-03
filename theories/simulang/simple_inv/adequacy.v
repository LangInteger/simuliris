(** The logical relation implies contextual refinement. *)

From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.
From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls closed_sim gen_log_rel.
From simuliris.simulang Require Import proofmode tactics.
From simuliris.simulang Require Import gen_adequacy behavior wf gen_refl.
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

Print gen_log_rel.
Print log_rel.

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

Locate prog_ref.
Locate ctx_ref.
Print expr_wf.
Print ctx_ref.
Print log_rel.
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


Definition gen_log_rel_1 `{simpleGS Σ} e_t e_s  : iProp Σ :=
  □ ∀ π (map : gmap string (val * val)) (gs : gmap string val),
    target_globals (dom gs) -∗
    source_globals (dom gs) ==∗
    subst_map_rel val_rel (free_vars e_t ∪ free_vars e_s) map -∗
    subst_map (fst <$> map) e_t ⪯{π} subst_map (snd <$> map) e_s
      {{ λ v_t v_s, val_rel v_t v_s }}.

Print log_rel_ctx.
Check log_rel_ctx.
Locate log_rel_ctx.
Locate gen_log_rel_ctx.
Locate log_rel_structural.

Definition log_rel_structural_1 `{simpleGS Σ} : Prop := (∀ e_t e_s,
   let head_t := expr_split_head e_t in
   let head_s := expr_split_head e_s in
   simulang_wf head_s.1 →
   head_s.1 = head_t.1 →
   ([∗list] e_t';e_s' ∈ head_t.2; head_s.2, gen_log_rel_1 e_t' e_s') -∗
   gen_log_rel_1 e_t e_s).


Theorem gen_log_rel_refl_1 `{simpleGS Σ} e :
  log_rel_structural_1 →
  gen_expr_wf simulang_wf e →
  ⊢ gen_log_rel_1 e e.
Proof.
  intros He Hwf.
  iInduction e as [ ] "IH" forall (Hwf); destruct Hwf; iApply He. 
  all: try iDestruct ("IH" with "[%]") as "$".
  all: try iDestruct ("IH1" with "[%]") as "$".
  all: try iDestruct ("IH2" with "[%]") as "$".
  all: naive_solver.
Qed.

Theorem simple_log_rel_structural_1 `{simpleGS Σ} : log_rel_structural_1.
Proof.
Admitted.
  (* intros e_t e_s ?? Hwf Hs. iIntros "IH".
  destruct e_s, e_t => //; simpl in Hs; simplify_eq.
  all: try by iApply pure_log_rel_structural; unfold loc_rel_func_law, loc_rel_inj_law, loc_rel_offset_law; eauto using heapbij_loc_func, heapbij_loc_inj, heapbij_loc_shift, sim_bij_contains_globalbij.
  all: try iDestruct "IH" as "[IH IH1]".
  all: try iDestruct "IH1" as "[IH1 IH2]".
  all: try iDestruct "IH2" as "[IH2 IH3]".
  - (* Call *)
    iApply (log_rel_call with "IH IH1").
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
Qed. *)

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

Theorem log_rel_adequacy_1 Σ `{!simpleGpreS Σ} e_t e_s :
  (∀ `(simpleGS Σ), ⊢ gen_log_rel_1 e_t e_s) →
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
