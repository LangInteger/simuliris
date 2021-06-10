(** The logical relation implies contextual refinement. *)

From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.

From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls global_sim.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import gen_adequacy behavior wf parallel_subst.
From simuliris.simplang.simple_inv Require Import inv refl.

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

Lemma prog_rel_adequacy `{!simpleGpreS Σ} p_t p_s :
  isat (∀ `(simpleGS Σ), prog_rel p_t p_s) →
  beh_rel p_t p_s.
Proof.
  intros Hprog. apply simplang_adequacy.
  eapply sat_bupd, sat_mono, Hprog. clear Hprog.
  iIntros "Hprog_rel !> %".
  iMod heapbij_init as (?) "Hbij". iModIntro.
  iExists simple_inv, heapbij.loc_rel.
  iSpecialize ("Hprog_rel" $! (SimpleGS Σ _ _)).
  iFrame "Hprog_rel".
  iSplitL "Hbij".
  { rewrite /sheap_inv /=. iExists ∅. by iFrame. }
  iSplitR; first done.
  iIntros (??) "$".
Qed.

(** Adequacy for open terms. *)
Theorem log_rel_adequacy `{!simpleGpreS Σ} e_t e_s :
  isat (∀ `(simpleGS Σ), log_rel e_t e_s) →
  ctx_rel e_t e_s.
Proof.
  (* TODO *)
Abort.
