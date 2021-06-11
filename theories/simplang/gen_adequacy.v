From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls global_sim adequacy.
From simuliris.simplang Require Import proofmode tactics behavior.
From simuliris.simplang Require Import parallel_subst gen_val_rel.

(** Generic adequacy theorem for sheap-based logical relations. *)
Section adequacy.
  Lemma simplang_adequacy `{sheapGpreS Σ} p_t p_s :
    isat (∀ `(sheapGS Σ), |==> ∃ `(sheapInv Σ) loc_rel,
      sheap_inv p_s state_empty [Call ##"main" #()] ∗
      ext_rel 0 #() #() ∗
      (∀ v_t v_s, ext_rel 0 v_t v_s -∗ gen_val_rel loc_rel v_t v_s) ∗
      prog_rel p_t p_s
    ) →
    beh_rel p_t p_s.
  Proof.
    intros Hrel. eapply (slsls_adequacy (sat:=isat)).
    eapply sat_mono, Hrel. clear Hrel.
    iIntros "Hprog_rel %σ_t %σ_s".
    iMod sheap_init as (HsheapGS) "Hinit".
    iMod ("Hprog_rel" $! HsheapGS) as (HsheapInv loc_rel) "(Hinv & Hunit & Hobs & Hprog_rel)".
    iDestruct ("Hinit" $! HsheapInv) as "[Hstate Hprogs_are]".
    iModIntro. iExists sheapGS_simulirisGS.
    iFrame "Hprog_rel Hprogs_are Hunit".
    iSplitR "Hobs".
    - iIntros ([-> ->]). iApply "Hstate". done.
    - iIntros (??) "Hext". iApply gen_val_rel_obs. iApply "Hobs". done.
  Qed.

End adequacy.
