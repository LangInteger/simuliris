From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls global_sim adequacy.
From simuliris.simplang Require Import proofmode tactics behavior.
From simuliris.simplang Require Import parallel_subst gen_val_rel wf.

(** Generic adequacy theorem for sheap-based logical relations. *)
Section adequacy.
  Lemma simplang_adequacy `{sheapGpreS Σ} p_t p_s :
    isat (∀ `(sheapGS Σ) gs,
      ⌜map_Forall (λ _ v, val_wf v) gs⌝ -∗
      |==> ∃ `(sheapInv Σ) loc_rel,
      ([∗ map] f ↦ K ∈ p_t, f @t K) -∗
      ([∗ map] f ↦ K ∈ p_s, f @s K) -∗
      ([∗ map] n↦v ∈ gs, global_loc n ↦t v ∗ target_block_size (global_loc n) (Some 1) ∗
                          global_loc n ↦s v ∗ source_block_size (global_loc n) (Some 1)) -∗
      target_globals (dom _ gs) -∗
      source_globals (dom _ gs) ==∗
      sheap_inv p_s (state_init gs) [Call f#"main" #()] ∗
      ext_rel 0 #() #() ∗
      (∀ v_t v_s, ext_rel 0 v_t v_s -∗ gen_val_rel loc_rel v_t v_s) ∗
      prog_rel p_t p_s
    ) →
    beh_rel p_t p_s.
  Proof.
    intros Hrel. eapply (slsls_adequacy (sat:=isat)).
    eapply sat_mono, Hrel. clear Hrel.
    iIntros "Hprog_rel %σ_t %σ_s (%gs&%&->&->)".
    iMod (sheap_init p_t _ p_s _) as (HsheapGS) "Hinit".
    iMod ("Hprog_rel" $! HsheapGS gs with "[//]") as (HsheapInv loc_rel) "Hprog_rel".
    iDestruct ("Hinit" $! HsheapInv) as "(Hstate & Hp_t & Hmt_t & Hp_s & Hmt_s & Hg_s & Hg_t & Hprogs_are)".
    iMod ("Hprog_rel" with "Hp_t Hp_s [Hmt_t Hmt_s] Hg_t Hg_s") as "(Hinv & Hunit & Hobs & Hprog_rel)".
    { rewrite !big_sepM_sep. iFrame. }
    iModIntro. iExists sheapGS_simulirisGS.
    iFrame "Hprog_rel Hprogs_are Hunit".
    iSplitR "Hobs".
    - iApply "Hstate". done.
    - iIntros (??) "Hext". iApply gen_val_rel_obs. iApply "Hobs". done.
  Qed.

End adequacy.
