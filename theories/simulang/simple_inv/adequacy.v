(** The logical relation implies contextual refinement. *)

From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.
From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls global_sim gen_log_rel.
From simuliris.simulang Require Import proofmode tactics.
From simuliris.simulang Require Import gen_adequacy behavior wf gen_refl.
From simuliris.simulang.simple_inv Require Import inv refl.
From iris.prelude Require Import options.

(** Instantiate our notion of contextual refinement. *)
Notation ctx_rel := (gen_ctx_rel expr_head_wf).

(** Whole-program adequacy. *)
Class simpleGpreS Σ := {
  sbij_pre_heapG :> sheapGpreS Σ;
  sbij_pre_bijG :> heapbijGpreS Σ;
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
    target_globals (dom (gset string) gs) -∗
    source_globals (dom (gset string) gs) ==∗
    ([∗ map] v∈gs, val_rel v v) ∗ prog_rel p_t p_s
  ) →
  beh_rel p_t p_s.
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
  ctx_rel e_t e_s.
Proof.
  intros Hrel C fname x p Hpwf HCwf Hvars.
  apply (prog_rel_adequacy Σ). eapply isat_intro.
  iIntros (? gs Hgs) "_ _ _ _ !#".
  iSplit. { iApply big_sepM_intro. iIntros "!>" (???). iApply val_wf_sound. by apply: Hgs. }
  rewrite /prog_rel.
  iIntros "!# %f %arg %body".
  iDestruct (Hrel _) as "Hrel". clear Hrel.
  destruct (decide (f = fname)) as [->|Hne].
  - rewrite !lookup_insert.
    iIntros ([= <- <-]). iExists _, _. iSplitR; first done.
    (* TODO Factor this into a general lemma? *)
    iIntros (v_t v_s π) "#Hval /=".
    iApply sim_wand.
    + iApply (gen_log_rel_singleton with "[Hrel] Hval []"); first done.
      * by iApply log_rel_ctx.
      * done.
    + simpl. iIntros (??). rewrite left_id. auto.
  - rewrite !lookup_insert_ne //.
    iIntros (Hf). iExists arg, body. iSplit; first done.
    specialize (Hpwf _ _ Hf). destruct Hpwf as [HKwf HKclosed].
    (* TODO Factor this into a lemma? *)
    iIntros (v_t v_s π) "#Hval /=".
    iApply sim_wand.
    + iApply (gen_log_rel_singleton with "[Hrel] Hval []"); first set_solver.
      * by iApply log_rel_refl.
      * done.
    + simpl. iIntros (??). rewrite left_id. auto.
Qed.
