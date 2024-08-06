From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors.
From simuliris.tree_borrows Require Import wishlist.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_base random_lemmas.
From simuliris.tree_borrows.trees_equal Require Import trees_equal_source_read trees_equal_transitivity.
From iris.prelude Require Import options.

(** * Simulation lemmas using the ghost state for proving optimizations *)

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

(** ** Copy lemma *)

Lemma source_copy_any v_t v_rd sz l_hl l_rd t π Ψ tk :
  sz ≠ 0%nat → (* if it is 0, use the zero-sized read lemma *)
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  t $$ tk -∗
  l_hl ↦s∗[tk]{t} v_t -∗
  (∀ v_res, l_hl ↦s∗[tk]{t} v_t -∗ t $$ tk -∗ ⌜(v_res = #v_rd ∨ v_res = #(replicate sz ☠%S))⌝ -∗ source_red v_res π Ψ)%E -∗
  source_red (Copy (Place l_rd t sz)) π Ψ.
Proof.
  iIntros (Hnz Hread Hsameblk) "Htag Hs Hsim". eapply read_range_length in Hread as HH. subst sz.
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s T_s K_s) "((HP_t & HP_s & Hbor)&[%Ht_s %Hpoolsafe])".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  eapply pool_safe_implies in Ht_s as Hfoo. 2: done.
  destruct Hfoo as [(v_rd'&Hv_rd&Hcont&Hreadsome&_)|[(v_nil&Hread_nil&Hiszero)|(Hcont&Happly_none&Hmemsome)]]; last first.
  2: lia.
  { (* poison *)
    iExists _, _. iSplit.
    { iPureIntro. destruct l_rd. econstructor 2. 1: by eapply FailedCopyBS.
      econstructor; done. }
    iModIntro. iFrame "HP_t HP_s". iSpecialize ("Hsim" $! _ with "Hs Htag []"); last first.
    1: iSplitR "Hsim"; last by iApply "Hsim".
    1: do 4 iExists _; destruct σ_s; iApply "Hbor".
    iPureIntro. right. done. }
  iPoseProof (bor_interp_readN_source_after_accesss with "Hbor Hs Htag") as "(%it&%tr&%Hit&%Htr&%Hown)".
  1: exact Hread. 1: done. 1: done. 1: done. 1: exact Hreadsome.
  opose proof* (read_range_list_to_heaplet_read_memory_strict) as READ_MEM. 1: exact Hread. 1: done.
  { intros i Hi. by eapply Hown. }
  destruct l_hl as [blk off_hl], l_rd as [blk2 off_rd]; simpl in *; subst blk2.
  odestruct (bor_state_own_enables_read false (off_rd, length v_rd)) as (Hcontain&trs'&Htrs').
  1: exact Hwf_s.
  { intros l (Hl1&Hl2); simpl in *. exists it, tr. do 2 (split; first done). assert (∃ (i:nat), l = off_rd + i) as (ii&Hii).
    1: exists (Z.to_nat (l - off_rd)); lia. subst l. eapply Hown. lia. } 1: simpl; lia.
  iExists _, _.
  eassert (base_step P_s (Copy (Place (blk, off_rd) t (length v_rd))) σ_s _ _ []) as Hstep.
  { eapply copy_base_step'. 1: done. 2: exact READ_MEM. 2: exact Htrs'. done. }
  iSplit; first done.
  assert (trees_equal (scs σ_s) Forwards trs' (strs σ_t)) as Hstrs_eq'.
  { eapply trees_equal_trans. 9: eapply Hstrs_eq.
    1,3,5,7: by eapply Hwf_s.
    1-3: eapply base_step_wf in Hwf_s; last done. 1-3: by eapply Hwf_s.
    change Forwards with (direction_flip Backwards).
    eapply trees_equal_sym.
    eapply apply_within_trees_lift. 2: exact Htrs'. 1: by eapply Hwf_s. simpl.
    intros trX tr' HH1 HH2 HH3. simpl in *. assert (tr = trX) as <- by congruence.
    eapply tree_equal_asymmetric_read_source.
    4: eapply HH3. 2: done. 1: by eapply Hwf_s.
    eapply source_only_read_pre_from_bor_state_own. 3: done. 2: done. 1: done. intros off (Ho1&Ho2); simpl in *.
    assert (∃ (i:nat), off = off_rd + i) as (i&->) by (exists (Z.to_nat (off - off_rd)); lia).
    eapply Hown. 1: lia. }

  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hs".

  iModIntro.
  iSplitR "Hs Htag Hsim".
  2: { iApply ("Hsim" with "Hs Htag"). iPureIntro; by left. }
  iFrame "HP_t HP_s". iExists M_call, M_tag, M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Hpub_cid". 2: iSplit; last iSplit; last (iPureIntro; split_and!).
  - iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
  - repeat (iSplit; first done).
    simpl. iIntros (l) "Hs". iPoseProof (state_rel_pub_or_priv with "Hs Hsrel") as "$".
  - done.
  - (* tag invariant *)
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom & Hunq1 & Hunq2). split_and!; [ | done..].
    intros t' tk' Htk_some. destruct (Htag_interp _ _ Htk_some) as (Hsnp_lt_t & Hsnp_lt_s & Hlocal & Hctrl_t & Hctrl_s & Hag).
    split_and!; [ done | done | | | | done ].
    + done.
    + eapply Hctrl_t.
    + intros l sc_s Hsc_s. eapply loc_controlled_read_preserved_everywhere.
      1: eapply Htrs'. 1-4: done.
      by eapply Hctrl_s.
  - eapply (base_step_wf P_s). 2: exact Hwf_s. eapply copy_base_step'. 1: done. 2: exact READ_MEM. 2: exact Htrs'. done.
  - done.
Qed.

End lifting.
