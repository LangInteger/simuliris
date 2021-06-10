From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.

From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls global_sim.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import gen_adequacy.
From simuliris.simplang.simple_inv Require Import inv refl.

Class simpleGpreS Σ := {
  sbij_pre_heapG :> sheapGpreS Σ;
  sbij_pre_bijG :> heapbijGpreS Σ;
}.
Definition simpleΣ := #[sheapΣ; heapbijΣ].

Global Instance subG_sbijΣ Σ :
  subG simpleΣ Σ → simpleGpreS Σ.
Proof. solve_inG. Qed.

Lemma adequacy `{!simpleGpreS Σ} p_t p_s :
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
