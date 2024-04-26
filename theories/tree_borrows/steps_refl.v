From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import trees_equal wishlist steps_progress steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors.
From iris.prelude Require Import options.

Section lifting.
Context `{!sborGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

Lemma sim_value_result v_t v_s (Φ : result → result → iProp Σ) π :
  Φ (ValR v_t) (ValR v_s) -∗ #v_t ⪯{π} #v_s {{ Φ }}.
Proof. iIntros "H". iApply sim_expr_base. iExists (ValR v_t), (ValR v_s). eauto. Qed.

Lemma sim_place_result l_t t_t T_t l_s t_s T_s (Φ : result → result → iProp Σ) π :
  Φ (PlaceR l_t t_t T_t) (PlaceR l_s t_s T_s) -∗ Place l_t t_t T_t ⪯{π} Place l_s t_s T_s {{ Φ }}.
Proof. iIntros "H". iApply sim_expr_base. iExists (PlaceR _ _ _), (PlaceR _ _ _); eauto. Qed.

Lemma sim_result r_t r_s (Φ : result → result → iProp Σ) π :
  Φ r_t r_s -∗ of_result r_t ⪯{π} of_result r_s {{ Φ }}.
Proof. iIntros "H". iApply sim_expr_base. by iApply lift_post_val. Qed.

Lemma init_mem_lookup_fresh_poison blk off (n:nat) h :
  0 ≤ off ∧ off < n →
  init_mem (blk, 0) n h !! (blk, off) = Some ScPoison.
Proof.
  intros (Hpos & Hlt).
  pose proof (init_mem_lookup (blk, 0) n h) as (Hinit1&_).
  ospecialize (Hinit1 (Z.to_nat off) _); first lia.
  rewrite /= /shift_loc /= Z.add_0_l Z2Nat.id // in Hinit1.
Qed.

Lemma init_mem_lookup_fresh_None blk off (n:nat) h :
  (forall off, (blk, off) ∉ dom h) →
  (off < 0 ∨ n ≤ off) →
  init_mem (blk, 0) n h !! (blk, off) = None.
Proof.
  intros Hfresh Hout.
  pose proof (init_mem_lookup (blk, 0) n h) as (_&Hinit2).
  rewrite (Hinit2 (blk, off)).
  + eapply not_elem_of_dom, Hfresh.
  + intros i Hlt.
    rewrite /= /shift_loc /= Z.add_0_l.
    intros [= ->]. destruct Hout as [Hout|Hout]; lia.
Qed.

Lemma init_mem_lookup_fresh_old blk blk' off (n:nat) h :
  blk ≠ blk' →
  init_mem (blk, 0) n h !! (blk', off) = h !! (blk', off).
Proof.
  intros Hfresh.
  pose proof (init_mem_lookup (blk, 0) n h) as (_&Hinit2).
  apply Hinit2.
  intros ? _ [=]. done.
Qed.


Lemma init_mem_lookup_fresh_inv blk blk' off (n:nat) h k :
  (forall off, (blk, off) ∉ dom h) →
  init_mem (blk, 0) n h !! (blk', off) = k →
  (k = Some ScPoison ∧ blk = blk' ∧ 0 ≤ off ∧ off < n)
∨ (k = None ∧ blk = blk' ∧ (off < 0 ∨ n ≤ off))
∨ (k = h !! (blk', off) ∧ blk ≠ blk').
Proof.
  intros Hfresh Hinit.
  destruct (decide (blk = blk')) as [Heqblk|Hne].
  1: subst blk'; destruct (decide (0 ≤ off)) as [Hpos|Hneg].
  1: destruct (decide (off < n)) as [Hlt|Hge].
  { left. subst k. split_and!; try done. by rewrite init_mem_lookup_fresh_poison. }
  1-2: right; left; split_and!; try done; last lia.
  1-2: subst k; rewrite init_mem_lookup_fresh_None; try done; lia.
  { right. right. split; last done. subst k. by apply init_mem_lookup_fresh_old. }
Qed.


Lemma sim_alloc_public T Φ π :
  (∀ t l, t $$ tk_pub -∗
    rrel (PlaceR l (t) T) (PlaceR l (t) T) -∗
    Place l (t) T ⪯{π} Place l (t) T [{ Φ }]) -∗
  Alloc T ⪯{π} Alloc T [{ Φ }].
Proof.
  iIntros "Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  specialize (pool_safe_implies Hsafe Hpool) as Hnonzero.
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iSplitR. { iPureIntro. do 3 eexists. eapply alloc_base_step; assumption. }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_alloc_inv _ _ _ _ _ _ Hhead_t) as (_ & -> & -> & ->).

  (* allocate tag *)
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  assert (M_tag !! (σ_t.(snp)) = None) as HNone.
  { destruct (M_tag !! (σ_t.(snp))) as [[tk' []] | ] eqn:Hs; last done. exfalso.
    apply Htag_interp in Hs as (_ & H & _). unfold tag_valid in H. lia.
  }
  iMod (tkmap_insert tk_pub (σ_t.(snp)) () ltac:(done) with "Htag_auth") as "[Htag_auth #Ht]".
  iModIntro.
  pose (blk := (fresh_block σ_t.(shp))). (* can be σ_s and σ_t, it does not matter. *)
  pose (l := (blk, 0)). pose (nt := σ_t.(snp)).
  pose (α_t' := extend_trees ((snp σ_t)) blk 0 T (strs σ_t)).
  pose (α_s' := extend_trees ((snp σ_s)) blk 0 T (strs σ_s)).
  pose (σ_t' := (mkState (init_mem l T σ_t.(shp)) α_t' σ_t.(scs) (S σ_t.(snp)) σ_t.(snc))).
  pose (σ_s' := (mkState (init_mem l T σ_s.(shp)) α_s' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Alloc T) σ_s (Place l (nt) T) σ_s' []).
  { subst σ_s' nt α_s' blk l. rewrite -Hsnp_eq -(fresh_block_det σ_s σ_t); last done.
    eapply alloc_base_step; assumption.
  }
  iExists _, [], _. iSplitR; first done. simpl. iFrame "HP_t HP_s".
  iSplitR "Hsim Ht"; first last.
  { iSplitL; last done. subst nt l blk. iApply ("Hsim" with "Ht").
    iFrame "Ht". done.
  }
  (* re-establish the invariants *)
  iExists M_call, (<[nt := (tk_pub, ())]> M_tag), M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit. 
  - (* pub cid *)
    iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; done.
    (* state rel *) 
  - iSplit; last iSplit; last iSplit; last iSplit; last iSplit.
    + cbn. iPureIntro. rewrite init_mem_dom. rewrite (init_mem_dom _ _ (shp σ_t)).
      f_equal. apply Hdom_eq.
    + iPureIntro. subst α_s'. cbn. rewrite Hsnp_eq. eapply trees_equal_init_trees. done.
    + iPureIntro. cbn. by rewrite Hsnp_eq.
    + iPureIntro. cbn. by rewrite Hsnc_eq.
    + iPureIntro. cbn. by rewrite Hscs_eq. 
    + simpl. fold blk. iIntros ((blk'&off') [sc Hsc]).
      apply init_mem_lookup_fresh_inv in Hsc as Hsc'; last eapply is_fresh_block.
      destruct Hsc' as [([= ->] & -> & Hpos & Hlt)|[([=] & _)|(Hthru&Hne)]].
      * iLeft. iIntros (sc_t Hlu).
        rewrite Hsc in Hlu.
        injection Hlu as <-. 
        iExists ScPoison. iSplit; last done. iPureIntro.
        rewrite init_mem_lookup_fresh_poison //. 
      * iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
        unshelve iDestruct ("Hsrel" $! (blk', off') _) as "[Hsrel2|%Hpriv]".
        -- by eexists. 
        -- iLeft. iIntros (sc_t Hsc_t). cbn in Hsc_t.
           rewrite Hsc Hthru in Hsc_t.
           iDestruct ("Hsrel2" $! sc_t Hsc_t) as (sc_s Hsc_s) "Hsrel3".
           iExists (sc_s). subst σ_s'. cbn. rewrite init_mem_lookup_fresh_old; last done.
           iFrame "Hsrel3". done.
        -- iRight. iPureIntro. destruct Hpriv as (tg & tk & HtagSome & HSome & Hcases).
           exists tg, tk. split_and!; [|done..].
           rewrite lookup_insert_ne; first done.
           intros <-. by rewrite HNone in HtagSome.
  - (* call interp *) 
    iPureIntro.
    intros c M Hc. simpl. specialize (Hcall_interp c M Hc) as (Hc1 & Hc2).
    split; first done. intros t L Ht.
    specialize (Hc2 t L Ht) as (Hc3 & Hc4).
    split.
    { eapply tag_valid_mono; try done; lia. }
    intros l' b' Hl'. specialize (Hc4 l' b' Hl').
    destruct b'.
    + destruct Hc4 as (it & Hit & Hperm).
      exists it; split; last done.
      destruct Hit as (trr&Hit1&Hit2); eexists; split; last done.
      rewrite /extend_trees lookup_insert_ne //.
      intros Heq. rewrite -Heq in Hit1.
      eapply elem_of_dom_2 in Hit1.
      rewrite state_wf_dom // in Hit1.
      by eapply is_fresh_block_fst in Hit1.
    + intros it (tr&Htr&Hit). simpl. eapply Hc4.
      exists tr; split; last done. rewrite /extend_trees in Htr.
      eapply lookup_insert_Some in Htr as [(Htr1&Htr2)|(Htr1&Htr2)]; last done.
      subst tr. destruct Hit as (H1&H2). eapply init_tree_contains_only in H1. subst t.
      rewrite /tag_valid in Hc3. lia.
  - (* tag interp *)
    iPureIntro. destruct Htag_interp as (Htag_interp & Hdom_t & Hdom_s & Hunq1 & Hunq2). split_and!.
    { simpl. intros tr tk. rewrite lookup_insert_Some. intros [[<- [= <-]] | [Hneq Hsome]].
      - (* new tag: as these are public, the locations under this tag are not directly controlled *)
        split_and!; [ rewrite /tag_valid; lia | rewrite /tag_valid; lia | | |].
        + intros l' sc_t Hsc_t. exfalso. specialize (Hdom_t nt l' ltac:(eauto)) as (? &?). subst nt. congruence.
        + intros l' sc_t Hsc_t. exfalso. specialize (Hdom_s nt l' ltac:(eauto)) as (? &?). subst nt. congruence.
        + apply dom_agree_on_tag_not_elem. 
          * intros l'. destruct heaplet_lookup eqn:Hs; last done.
            destruct (Hdom_t nt l' ltac:(eauto)) as (? & ?).
            subst nt. congruence.
          * intros l'. destruct heaplet_lookup eqn:Hs; last done.
            destruct (Hdom_s nt l' ltac:(eauto)) as (? & ?).
            subst nt. congruence.
      - (* old tag *)
        specialize (Htag_interp _ _ Hsome) as (Hv1 & Hv2 & Hcontrol_t & Hcontrol_s & Hag).
        split_and!; [inversion Hv1; simplify_eq; econstructor; lia | inversion Hv1; simplify_eq; econstructor; lia | .. | done].
        + intros l' sc_t Hcontrol%Hcontrol_t. clear Hhead_s. eapply loc_controlled_alloc_update; done.
        + intros l' sc_s Hcontrol%Hcontrol_s. clear α_t' σ_t' Hhead_s. subst σ_s' α_s' l blk.
          erewrite fresh_block_det; last done.
          eapply loc_controlled_alloc_update; try done.
          by rewrite Hsnp_eq.
    }
    { intros t l'. rewrite lookup_insert_is_Some'. eauto. }
    { intros t l'. rewrite lookup_insert_is_Some'. eauto. }
    { done. }
    { done. }
  - iPureIntro. by eapply base_step_wf.
  - iPureIntro. by eapply base_step_wf.
Qed.

Lemma sim_free_public sz sz' l_t l_s bor_t bor_s Φ π :
  rrel (PlaceR l_t bor_t sz') (PlaceR l_s bor_s sz) -∗
  #[☠] ⪯{π} #[☠] [{ Φ }] -∗
  Free (Place l_t bor_t sz') ⪯{π} Free (Place l_s bor_s sz) [{ Φ }].
Proof.
  iIntros "[#Hscrel ->] Hsim".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[%Heq Hpub]". injection Heq as [= -> ->].
  iClear "Hscrel".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  specialize (pool_safe_implies Hsafe Hpool) as (trs' & Hdealloc_s & Hpos & Hcontain & Happly_s).
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  odestruct (apply_within_trees_equal _ _ _ _ _ _ _ Happly_s) as (trt' & Happly_t & Heq'); [|exact Hsst_eq|].
  { intros ttr1 ttr1' ttr2 H1 H2 Httr1 Httr1' Httr2.
    assert (tree_contains bor_s ttr1) as Hcont' by rewrite /trees_contain /trees_at_block Httr1 // in Hcontain.
    edestruct tree_equal_allows_same_deallocation as (ttr2'&Httr2').
    5: eapply mk_is_Some, H1. 3: done.
    1-3: eapply wf_tree_tree_unique.
    1,3: by eapply Hwf_s. 1: by eapply Hwf_t.
    1: done.
    exists ttr2'; split; first done.
    eapply tree_equal_memory_deallocate. 5,6,4,3: done.
    all: eapply wf_tree_tree_unique. 1: by eapply Hwf_s. by eapply Hwf_t. }
  iSplitR.
  { iPureIntro. do 3 eexists. eapply dealloc_base_step'; try done.
    - setoid_rewrite <- elem_of_dom. setoid_rewrite <- elem_of_dom in Hdealloc_s. rewrite -Hdom_eq //.
    - rewrite - trees_equal_same_tags //.
    - rewrite -Hscs_eq. eapply Happly_t.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_free_inv _ _ _ _ _ _ _ _ Hhead_t) as (α'0 & Hdealloc' & _ & Hcontain' & Hα'0 & -> & -> & ->).
  assert (α'0 = trt') as ->.
  { rewrite -Hscs_eq Happly_t in Hα'0. by injection Hα'0 as <-. }
  iModIntro.
  pose (σ_s' := (mkState (free_mem l_s sz σ_s.(shp)) (delete l_s.1 trs') σ_s.(scs) σ_s.(snp) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Free (Place l_s bor_s sz)) σ_s (ValR [☠]%S) σ_s' []).
  { eapply dealloc_base_step'; eauto. }
  iExists (#[☠])%E, [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitR "Hsim"; first last. { iSplitL; done. }

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%Hpub".

  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  (* re-establish the invariants *)
  iExists M_call, M_tag, M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
  - (* pub cid *)
    iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; done.
  - (* re-establish the state relation *)
    iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hsrel)".
    iSplitR. { iPureIntro. simpl. apply free_mem_dom. done. }
    simpl. iSplit.
    1: iPureIntro; by eapply trees_equal_delete.
    do 3 (iSplit; first done).
    iIntros (l (sc & Hsome)).
    destruct (free_mem_lookup_case l l_s sz σ_t.(shp)) as [[Hi Hfreet] | (i & _ & -> & ?)]; last congruence.
    rewrite Hfreet in Hsome. iDestruct ("Hsrel" $! l with "[]") as "[Hpubl | Hprivl]"; first by eauto.
    + iLeft. iIntros (sc_t Hsc_t). simpl in *.
      rewrite Hfreet in Hsc_t. simplify_eq.
      iDestruct ("Hpubl" $! sc Hsome) as (sc_s) "[%Hsc_s Hscr]".
      iExists sc_s. iSplitR; last done.
      iPureIntro.
      destruct (free_mem_lookup_case l l_s sz σ_s.(shp)) as [[_ Hfrees] | (i' & Hi' & -> & _)].
      2: { specialize (Hi i' Hi'). congruence. }
      rewrite Hfrees Hsc_s. done.
    + iRight. done.
  - (* re-establish the call set interpretation *)
    iPureIntro.
    iIntros (c M' Hc). simpl. specialize (Hcall_interp _ _ Hc) as (Hcs & HM'). split; first done.
    intros t L HL. specialize (HM' _ _ HL) as (Hvalid & HM'). split; first done.
    intros l b Hl. specialize (HM' l b Hl).
    eapply tag_protected_preserved_by_delete. 4: apply HM'.
    1: apply Hwf_t. 1: eassumption. 1: apply Hcs.
  - (* re-establish the tag interpretation *)
    destruct Htag_interp as (Htag_interp & Hdom_t & Hdom_s & Hunq1 & Hunq2).
    iPureIntro. split_and!; [ | done..].
    intros t tk Ht. simpl. specialize (Htag_interp _ _ Ht) as (? & ? & Hcontrol_t & Hcontrol_s & Hag).
    split_and!; [done | done | | | done].
    + intros l sc_t Hsc_t%Hcontrol_t. rewrite Hscs_eq in Happly_t.
      eapply loc_controlled_dealloc_update; [ apply Happly_t | done | done | | done ].
      intros -> _. rewrite Hpub in Ht. congruence.
    + intros l sc_s Hsc_s%Hcontrol_s.
      eapply loc_controlled_dealloc_update; [apply Happly_s | done | done | | done].
      intros -> _. rewrite Hpub in Ht. congruence.
  - iPureIntro. by eapply base_step_wf.
  - iPureIntro. by eapply base_step_wf.
Qed.

Lemma sim_copy_public Φ π l_t bor_t sz l_s bor_s sz_t :
  rrel (PlaceR l_t bor_t sz_t) (PlaceR l_s bor_s sz) -∗
  (∀ v_t v_s, value_rel v_t v_s -∗ v_t ⪯{π} ValR v_s [{ Φ }]) -∗
  Copy (PlaceR l_t bor_t sz_t) ⪯{π} Copy (PlaceR l_s bor_s sz) [{ Φ }].
Proof.
  iIntros "[#Hscrel ->] Hsim".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[%Heq Hpub]". injection Heq as [= -> ->].
  iClear "Hscrel".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  specialize (pool_safe_implies Hsafe Hpool) as [(vr_s&Hreadmem&Hcontain_s&(trs_s'&Htrss))|(Hcontain_s&Hnotrees)];
  pose proof Hcontain_s as Hcontain_t; rewrite trees_equal_same_tags in Hcontain_t; try done; last first.
  { (* We get poison *)
    assert (apply_within_trees (memory_access AccessRead (scs σ_s) bor_s (l_s.2, sz)) l_s.1 (strs σ_t) = None) as Hnotrees_t.
    { destruct apply_within_trees eqn:HSome in |-*; try done.
      eapply mk_is_Some, trees_equal_allows_same_access in HSome as (x&Hx); first by erewrite Hnotrees in Hx.
      1: by eapply trees_equal_sym. 1: by eapply Hwf_t. 1: by eapply Hwf_s. 1: done. }
    iSplit. 
    { iPureIntro. do 3 eexists. eapply failed_copy_base_step'; try done.
      rewrite -Hscs_eq //.
    }
    iIntros (e_t' efs_t σ_t') "%Hhead_t".
    specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead_t) as (Hcontain'&->&[(Hnotree&->&Hpoison)|(trs'&Htrs'&->&Hσ_t'&Hreadmem&Hsometree)]); last congruence.
    iModIntro. iExists e_t', [], σ_s. iSplit.
    { iPureIntro. subst e_t'. destruct σ_s, l_s. simpl. do 2 econstructor; by eauto. }
    simpl. iFrame. iSplit; last done. subst e_t'.
    iApply "Hsim". iApply big_sepL_sepL2_diag. iApply big_sepL_forall. by iIntros (k v (->&_)%lookup_replicate_1).
  }
  edestruct trees_equal_allows_same_access as (trs_t'&Htrst).
  1: done. 1: eapply Hwf_s. 1: eapply Hwf_t. 1: done. 1: by eapply mk_is_Some.
  opose proof (trees_equal_preserved_by_access _ _ Hstrs_eq _ Htrss Htrst) as Hstrs_eq'.
  1: eapply Hwf_s. 1: eapply Hwf_t. 1: done.
  assert (is_Some (read_mem l_s sz (shp σ_t))) as (vr_t&Hreadmem_t).
  { eapply read_mem_is_Some'. eapply mk_is_Some in Hreadmem. rewrite -read_mem_is_Some' Hdom_eq in Hreadmem. done. }
  iSplit.
  { iPureIntro. do 3 eexists. eapply copy_base_step'. 1-3: done. rewrite -Hscs_eq. done. }
  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead_t) as (Hcontain'&->&[(Hnotree&->&Hpoison)|(tr'&vr_t'&->&Hσ_t'&H3&H4)]); first congruence.
  assert (vr_t' = vr_t) as -> by congruence.
  assert (tr' = trs_t') as -> by congruence.
  clear H3 H4.
  iModIntro.
  pose (σ_s' := (mkState (shp σ_s) trs_s' (scs σ_s) (snp σ_s) (snc σ_s))).
  assert (Hhead_s : base_step P_s (Copy (Place l_s bor_s sz)) σ_s (ValR vr_s) σ_s' []).
  { eapply copy_base_step'; eauto. }
  iExists (Val vr_s), [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%Hpub".

  iSplitR "Hsim".
  {
    (* re-establish the invariants *)
    iExists M_call, M_tag, M_t, M_s.
    iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
    subst σ_s' σ_t'.
    iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
    - (* pub cid *)
      iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
    - repeat (iSplit; first done).
      simpl. iIntros (l) "Hs". iPoseProof (state_rel_pub_or_priv with "Hs Hsrel") as "$".
    - (* call invariant *)
      iPureIntro. intros c M' HM'_some.
      specialize (Hcall_interp c M' HM'_some) as (Hin & Hprot).
      split; first by apply Hin. intros pid L HL_some. specialize (Hprot pid L HL_some) as [Hpid Hprot].
      split; first by apply Hpid. intros l b Hin_l.
      specialize (Hprot l b Hin_l).
      eapply (tag_protected_preserved_by_access). 2: apply Htrst. 1: apply Hwf_t.
      1: by rewrite Hscs_eq. done.
    - (* tag invariant *)
      iPureIntro. destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom & Hunq1 & Hunq2). split_and!; [ | done..].
      intros t tk Htk_some. destruct (Htag_interp t tk Htk_some) as (Hsnp_lt_t & Hsnp_lt_s & Hctrl_t & Hctrl_s & Hag).
      split_and!; [ done | done | | | done ].
      + intros l sc_t Hsc_t. eapply loc_controlled_read_preserved_everywhere.
        1: rewrite Hscs_eq in Htrst; eapply Htrst. 1: done. 1: by rewrite -Hscs_eq. 1-2: done.
        by eapply Hctrl_t.
      + intros l sc_s Hsc_s. eapply loc_controlled_read_preserved_everywhere.
        1: eapply Htrss. 1-4: done.
        by eapply Hctrl_s.
    - (* source state wf *)
      iPureIntro. eapply base_step_wf; done.
    - (* target state wf *)
      iPureIntro. eapply base_step_wf; done.
  }
  iSplitL; last done.

  iApply "Hsim".
  (* proving the value relation *)
  specialize (read_mem_values _ _ _ _ Hreadmem_t) as [Hlen_t Hvr_t].
  specialize (read_mem_values _ _ _ _ Hreadmem) as [Hlen_s Hvr_s].

  iApply big_sepL2_forall; iSplit; first (iPureIntro;lia).
  iIntros (i sc_t sc_s) "%Hs_t %Hs_s".
  assert (i < sz)%nat as Hi. { rewrite -Hlen_t. eapply lookup_lt_is_Some_1. eauto. }
  assert (is_Some (shp σ_t !! (l_s +ₗ i))) as Htloc.
  { exists sc_t. rewrite -Hs_t. by eapply Hvr_t. }
  iPoseProof (state_rel_pub_if_not_priv _ _ _ _ _ _ (l_s +ₗ i) with "[] Hsrel []") as "Hpubloc".
  1: done. 
  { iPureIntro. intros t Hpriv.
    eapply (protected_priv_loc_does_not_survive_access σ_t σ_t'). 10: exact Hpriv.
    1: rewrite Hscs_eq in Htrst. 1-3: by rewrite Hσ_t'. 1: done. 1: done. 1: simpl; lia.
    1: done. 1: done. 1: done.
    intros tg tk sc HH1 HH2.
    destruct (Htag_interp) as (H1&H2&H3&H4&H5).
    destruct (H1 tg tk HH1) as (_&_&HH3&HH4).
    apply HH3. done.
  }
  iPoseProof (pub_loc_lookup with "[] Hpubloc") as "(%sc_t' & %sc_s' & %Hread_both & Hsc_rel)"; first by eauto.
  enough (sc_t = sc_t' ∧ sc_s = sc_s') by naive_solver.
  move : Hread_both (Hvr_t i Hi) (Hvr_s i Hi) Hs_t Hs_s.
  by move => [-> ->] <- <- [= ->] [= ->].
Qed.

(** Write *)
Lemma sim_write_public Φ π l_t tg_t sz_t l_s tg_s sz_s v_t' v_s' :
  rrel (PlaceR l_t tg_t sz_t) (PlaceR l_s tg_s sz_s) -∗
  value_rel v_t' v_s' -∗
  (#[☠] ⪯{π} #[☠] [{ Φ }]) -∗
  Write (Place l_t tg_t sz_t) v_t' ⪯{π} Write (Place l_s tg_s sz_s) v_s' [{ Φ }].
Proof.
  iIntros "[#Hscrel ->] #Hvrel Hsim".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[%Heq Hpub]". injection Heq as [= -> ->].
  iClear "Hscrel".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  specialize (pool_safe_implies Hsafe Hpool) as (Hread_s & Hcontain_s & (trs_s' & Htrss) & Hlen).
  pose proof Hcontain_s as Hcontain_t; rewrite trees_equal_same_tags in Hcontain_t; try done.
  iPoseProof (value_rel_length with "Hvrel") as "%Hlen_t'".

  assert (∃ xx, apply_within_trees (memory_access AccessWrite (scs σ_t) tg_s (l_s.2, sz_s)) l_s.1 (strs σ_t) = Some xx) as (trs_t' & Htrst).
  { eapply trees_equal_allows_same_access. 1: by rewrite -Hscs_eq. 1: by apply Hwf_s. 1: by apply Hwf_t. 1: done. rewrite -Hscs_eq -Hlen. by eexists. }
  eassert (trees_equal _ trs_s' trs_t') as Htrseq.
  { eapply trees_equal_preserved_by_access. 3: done. 1: eapply Hwf_s. 1: eapply Hwf_t. 2: exact Htrss. 2: rewrite Hscs_eq Hlen //. done. }
  iSplitR.
  { iPureIntro. do 3 eexists. eapply write_base_step'; [lia | | |].
    - rewrite -Hdom_eq. intros n Hn. apply Hread_s. lia.
    - done.
    - apply Htrst.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_write_inv _ _ _ _ _ _ _ _ _ Hhead_t) as (trst_2 & -> & -> & -> & _ & Hin_dom & _ & Htrst').
  assert (trst_2 = trs_t') as -> by congruence.
  iModIntro.
  pose (σ_s' := (mkState (write_mem l_s v_s' σ_s.(shp)) trs_s' σ_s.(scs) σ_s.(snp) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Write (Place l_s tg_s sz_s) v_s') σ_s (ValR [☠]%S) σ_s' []).
  { eapply write_base_step'; eauto. 2: by rewrite -Hlen. intros. rewrite Hdom_eq. apply Hin_dom. lia. }
  iExists (#[☠])%E, [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitR "Hsim"; first last. { iSplitL; done. }

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%"; try done.

  (* we keep the base_step hypotheses to use the [base_step_wf] lemma below *)
  (* re-establish the invariants *)
  iExists M_call, M_tag, M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Hpub_cid"; last iSplit; last iSplit; last iSplit; last iSplit.
  - (* pub cid *)
    iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
  - (* state rel *)
    rewrite /state_rel; simpl. iSplitL.
    { iPureIntro. erewrite !write_mem_dom_sane; first done. all: eauto. }
    do 4 (iSplitL; first done). iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hsrel)".
    iIntros (l) "%Hs".
    specialize (write_mem_lookup l_s v_s' σ_s.(shp)) as (Heq & Heq').
    specialize (write_mem_lookup_case l_s v_t' σ_t.(shp) l) as [(i & Hi & -> & Hwrite) | (Hi & Hwrite)].
    + (* we wrote to the location, and the written values must be related *)
      iLeft. iIntros (sc_t Hsc_t). simpl in Hsc_t. rewrite Heq; last lia.
      iExists (v_s' !!! i). rewrite Hwrite in Hsc_t.
      rewrite -(list_lookup_total_correct _ _ _ Hsc_t).
      iSplitR. { iPureIntro. apply list_lookup_lookup_total. apply lookup_lt_is_Some_2. lia. }
      iApply (value_rel_lookup_total with "Hvrel"). lia.
    + (* unaffected location *)
      simpl. rewrite Hwrite in Hs.
      iDestruct ("Hsrel" $! l with "[//]") as "[Hpubl | Hprivl]"; last by iRight.
      iLeft. rewrite /pub_loc Hwrite Heq'; first done. intros. apply Hi. lia.
  - (* call invariant *)
    iPureIntro. intros c M' HM'_some. simpl.
    specialize (Hcall_interp c M' HM'_some) as (Hin & Hprot).
    split; first done. intros t L [Ht HL]%Hprot. split; first done.
    intros l b Hprotl%HL.
    eapply tag_protected_preserved_by_access; last done.
    1: by eapply Hwf_t. 1: done. apply Hin.
  - (* tag invariant *)
    iPureIntro. destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom & Hunq1 & Hunq2). split_and!; [ | done..].
    intros t tk Ht.
    specialize (Htag_interp _ _ Ht) as (? & ? & Hcontrolled_t & Hcontrolled_s & Hdom).
    split_and!; [ done | done | | | done ].
    + intros l sc_t Hcontrol%Hcontrolled_t.
      destruct (decide (l.1 = l_s.1 ∧ l_s.2 ≤ l.2 < l_s.2 + sz_s)) as [(Hin1&Hin2)|Hout]; first 
      destruct (decide (t = tg_s)) as [->|Htgne].
      * assert (tk = tk_pub) as -> by congruence.
        eapply loc_controlled_write_invalidates_pub'; last done.
        all: done.
      * rewrite /loc_controlled. eapply loc_controlled_write_invalidates_others; last done.
        all: done.
      * eapply loc_controlled_access_outside; first done. all: try done.
        rewrite /= write_mem_lookup_outside // Hlen_t' Hlen //.
    + intros l sc_s Hcontrol%Hcontrolled_s.
      destruct (decide (l.1 = l_s.1 ∧ l_s.2 ≤ l.2 < l_s.2 + sz_s)) as [(Hin1&Hin2)|Hout]; first 
      destruct (decide (t = tg_s)) as [->|Htgne].
      * assert (tk = tk_pub) as -> by congruence.
        eapply loc_controlled_write_invalidates_pub'; last done.
        all: try done. by rewrite Hlen.
      * rewrite /loc_controlled. eapply loc_controlled_write_invalidates_others; last done.
        all: try done. by rewrite Hlen.
      * eapply loc_controlled_access_outside; first done. all: try done.
        2: by rewrite Hlen.
        rewrite /= write_mem_lookup_outside // Hlen //.
  - (* source state wf *)
    iPureIntro. eapply base_step_wf; done.
  - (* target state wf *)
    iPureIntro. eapply base_step_wf; done.
Qed.

(*

(** Retag *)
Lemma bor_interp_retag_public σ_s σ_t c l ot rkind kind T nt α' nxtp' :
  retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l ot rkind kind T = Some (nt, α', nxtp') →
  state_wf (mkState σ_t.(shp) α' σ_t.(scs) nxtp' σ_t.(snc)) →   (* could remove that assumption *)
  state_wf (mkState σ_s.(shp) α' σ_s.(scs) nxtp' σ_s.(snc)) →   (* could remove that assumption *)
  sc_rel (ScPtr l ot) (ScPtr l ot) -∗
  bor_interp sc_rel σ_t σ_s ==∗
  sc_rel (ScPtr l nt) (ScPtr l nt) ∗
  bor_interp sc_rel (mkState σ_t.(shp) α' σ_t.(scs) nxtp' σ_t.(snc)) (mkState σ_s.(shp) α' σ_s.(scs) nxtp' σ_s.(snc)).
Proof.
  intros Hretag Hwf_t' Hwf_s'.
  iIntros "Hscrel Hbor". iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".

  iDestruct "Hscrel" as "[_ #Hrel]".
  iAssert (⌜untagged_or_public M_tag ot⌝)%I as %Hpub.
  { iDestruct "Hrel" as "[[-> _] | (%t1 & %t2 & -> & -> & <- & Hpub)]"; first done.
    iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%". done.
  }

  (* allocate resources *)
  set (M_tag' := if decide (ot = nt) then M_tag else if nt is Tagged nt then <[nt := (tk_pub, ())]> M_tag else M_tag).
  specialize (retag_change_nxtp _ _ _ _ _ _ _ _ _ _ _ _ Hretag) as Hle.
  specialize (retag_change_tag _ _ _ _ _ _ _ _ _ _ _ _ Hretag) as Hnt.
  iAssert (|==> (if decide (ot = nt) then True%I else if nt is Tagged nt then nt $$ tk_pub else True%I) ∗ tkmap_auth tag_name 1 M_tag')%I with "[Htag_auth]" as "Hnt".
  { destruct (decide (ot = nt)) as [ | Hneq]; first by eauto.
    destruct Hnt as [ -> | Hnt]; first done.
    destruct nt as [ nt | ]; last by eauto. destruct Hnt as [-> ->].
    iMod (tkmap_insert tk_pub σ_s.(snp) tt with "Htag_auth") as "[$ $]"; last done.
    destruct (M_tag !! snp σ_s) as [ [? []] | ]eqn:Htag; last done.
    apply Htag_interp in Htag as (? & ? & _). lia.
  }
  iMod "Hnt" as "[Hnt Htag_auth]". iModIntro.
  iSplitL "Hnt Hrel".
  { destruct (decide (ot = nt)) as [-> | Hneq]. { iSplit; done. }
    destruct nt. {  iSplit; first done. eauto 10. }
    iSplit; first done. by iLeft.
  }

  iAssert (⌜retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l ot rkind kind T = Some (nt, α', nxtp')⌝)%I as "%Hretag_t".
  { iPoseProof (state_rel_calls_eq with "Hsrel") as "<-".
    iPoseProof (state_rel_stacks_eq with "Hsrel") as "<-".
    iPoseProof (state_rel_snp_eq with "Hsrel") as "<-". done. }

  (* re-establishing the interpretation *)
  iPoseProof (state_rel_get_pure with "Hsrel") as "%Hp".
  iExists M_call, M_tag', M_t, M_s.
  iFrame "Htag_t_auth Hc Htag_auth Htag_s_auth". iSplitL "Htainted".
  { (* tainted *) iApply (tag_tainted_interp_retag with "Htainted"). done. }
  iSplitL "Hpub_cid". { iFrame "Hpub_cid". }
  iSplitL.
  { (* state relation *)
    rewrite /state_rel. simpl. iDestruct "Hsrel" as "(-> & %Hs_eq & %Hsnp_eq & -> & -> & Hsrel)".
    do 5 (iSplitL; first done). iIntros (l' Hsl').
    iDestruct ("Hsrel" $! l' with "[//]") as "[Hpub | [%t' %Hpriv]]"; first (iLeft; iApply "Hpub").
    iRight. iPureIntro. exists t'.
    (* private locations are preserved: t' cannot be part of the range affected by the retag, because that is public *)
    destruct Hpriv as (tk' & Hsome_tk' & Ht_l' & Htk'). exists tk'.
    split_and!; [ | done | done].
    subst M_tag'. destruct (decide (ot = nt)) as [ | Hneq]; first done.
    destruct nt as [ nt | ]; last done.
    destruct (decide (t' = nt)) as [-> | Hneq']; first last.
    { rewrite lookup_insert_ne; done. }
    exfalso. (* contradiction with Hsome_tk' *)
    destruct Hnt as [<- | [-> ->]]; first congruence.
    apply Htag_interp in Hsome_tk' as (? & _). lia.
  }
  iSplitL.
  { (* call interpretation. *)
    iPureIntro. intros c' M' [Hc' HM']%Hcall_interp. simpl. split; first done.
    specialize (retag_change_nxtp _ _ _ _ _ _ _ _ _ _ _ _ Hretag) as Hnxtp'.
    intros t' S HS. simpl. specialize (HM' t' S HS) as (Ht' & Hprot).
    split; first lia. intros l' Hl'.
    specialize (Hprot l' Hl') as (s & pm' & Hs & Hit & Hpm').
    specialize (retag_item_active_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag_t l' s (Tagged t') c' pm' Hs Hc' Hit) as (s' & -> & Hin'). eauto.
  }
  iSplitL.
  { (* tag interpretation. *)
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
    destruct Hp as (Hsst & Hsnp & Hsnc & Hscs).
    iPureIntro. split_and!.
    { intros t tk' Hsome.
      assert ((nt = Tagged σ_t.(snp) ∧ t = σ_t.(snp) ∧ tk' = tk_pub ∧ nxtp' = S σ_t.(snp)) ∨ M_tag !! t = Some (tk', ())) as [(-> & -> & -> & ->) | Hsome'].
      { subst M_tag'. destruct (decide (ot = nt)) as [<- | Hneq]; first by eauto.
        destruct nt as [ nt | ]; last by eauto.
        destruct Hnt as [<- | [-> ?]]; first congruence.
        destruct (decide (t = σ_s.(snp))) as [-> | Hneq'].
        - rewrite lookup_insert in Hsome. injection Hsome as [= <-]. left; naive_solver.
        - rewrite lookup_insert_ne in Hsome; last done. by right.
      }
      - (* the new tag: nothing to show, since we don't put the tagged locations under control *)
        simpl. set (nt := σ_t.(snp)).
        assert (∀ l', M_t !! (nt, l') = None) as Mt_nt.
        { intros l'. destruct (M_t !! (nt, l')) eqn:Heq; last done.
          specialize (Ht_dom σ_t.(snp) l' ltac:(eauto)) as ([? []] & [? _]%Htag_interp). lia. }
        assert (∀ l', M_s !! (nt, l') = None) as Ms_nt.
        { intros l'. destruct (M_s !! (nt, l')) eqn:Heq; last done.
          specialize (Hs_dom σ_t.(snp) l' ltac:(eauto)) as ([? []] & [? _]%Htag_interp). lia. }
        split_and!; [lia | lia | | | ].
        + intros l' sc_t HM_t. congruence.
        + intros l' sc_s HM_s. congruence.
        + apply dom_agree_on_tag_not_elem; done.
      - (* old tags are preserved *)
        simpl. specialize (Htag_interp _ _ Hsome') as (? & ? & Hcontrolled_t & Hcontrolled_s & Hdom).
        split_and!; [lia | lia | | | ].
        + intros. eapply loc_controlled_retag_update; [ done | done | | done | by apply Hcontrolled_t].
          intros <-. move : Hpub. rewrite /untagged_or_public. congruence.
        + intros. eapply loc_controlled_retag_update; [ done | done | | done | by apply Hcontrolled_s].
          intros <-. move : Hpub. rewrite /untagged_or_public. congruence.
        + done.
    }
    { subst M_tag'. destruct (decide (ot = nt)); first done. destruct nt as [nt | ]; last done.
      intros. rewrite lookup_insert_is_Some'. right; eauto.
    }
    { subst M_tag'. destruct (decide (ot = nt)); first done. destruct nt as [nt | ]; last done.
      intros. rewrite lookup_insert_is_Some'. right; eauto.
    }
  }
  iSplit; done.
Qed.

Lemma sim_retag_public l_t l_s ot os c kind T rkind π Φ :
  value_rel [ScPtr l_t ot] [ScPtr l_s os] -∗
  (∀ nt, value_rel [ScPtr l_t nt] [ScPtr l_s nt] -∗
    #[ScPtr l_t nt] ⪯{π} #[ScPtr l_s nt] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] kind T rkind ⪯{π} Retag #[ScPtr l_s os] #[ScCallId c] kind T rkind [{ Φ }].
Proof.
  rewrite {1}/value_rel big_sepL2_singleton.
  iIntros "#Hscrel Hsim".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[%Heq Hpub]". injection Heq as [= -> <-].
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "((HP_t & HP_s & Hbor) & %Hthread & %Hsafe)".
  (* exploit source to gain knowledge about stacks & that c is a valid id *)
  specialize (pool_safe_implies Hsafe Hthread) as (c' & ot' & l' & [= <- <-] & [= <-] & Hc_active & Hretag_some_s).
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  have Hretag_some_t : is_Some (retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l_s ot rkind kind T).
  { destruct Hp as (<- & <- & _ & <- & _). done. }
  iModIntro. iSplitR.
  { iPureIntro.
    destruct Hretag_some_t as ([[] ] & Hretag_some_t).
    do 3 eexists. eapply retag_base_step'; last done.
    destruct Hp as (_ & _ & _ & <- & _). done.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_retag_inv _ _ _ _ _ _ _ _ _ _ _ Hhead_t) as (nt & α' & nxtp' & Hretag_t & -> & -> & -> & Hc).
  have Hretag_s : retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l_s ot rkind kind T = Some (nt, α', nxtp').
  { destruct Hp as (-> & -> & _ & -> & _). done. }
  assert (Hhead_s : base_step P_s (Retag #[ScPtr l_s ot] #[ScCallId c] kind T rkind) σ_s #[ScPtr l_s nt]%E (mkState (shp σ_s) α' (scs σ_s) nxtp' (snc σ_s)) []).
  { eapply retag_base_step'; done. }

  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %Hwf_s]".
  iMod (bor_interp_retag_public _ _ _ _ _ _ _ _ _ _ _ Hretag_s with "Hscrel Hbor") as "[Hscrel' Hbor]".
  { by eapply base_step_wf. }
  { by eapply base_step_wf. }
  iModIntro.

  iExists #[ScPtr l_s nt]%E, [], (mkState σ_s.(shp) α' σ_s.(scs) nxtp' σ_s.(snc)).
  iSplitR; first done.
  iFrame "Hbor HP_t HP_s".
  iSplitL; last done. iApply "Hsim". iApply big_sepL2_singleton. done.
Qed. *)

(** InitCall *)

Lemma bor_interp_init_call σ_t σ_s :
  bor_interp sc_rel σ_t σ_s ==∗
  σ_t.(snc) @@ ∅ ∗
  bor_interp sc_rel
    (mkState σ_t.(shp) σ_t.(strs) ({[ σ_t.(snc) ]} ∪ σ_t.(scs)) σ_t.(snp) (S σ_t.(snc)))
    (mkState σ_s.(shp) σ_s.(strs) ({[ σ_s.(snc) ]} ∪ σ_s.(scs)) σ_s.(snp) (S σ_s.(snc))).
Proof.
  iIntros "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iPoseProof (state_rel_snc_eq with "Hsrel") as "%Hsnc_eq".
  assert (M_call !! σ_t.(snc) = None) as Hfresh.
  { destruct (M_call !! σ_t.(snc)) as [ M' | ] eqn:HM'; last done. apply Hcall_interp in HM' as (Hin & _).
    apply Hwf_t in Hin. lia. }
  iMod (ghost_map_insert σ_t.(snc) ∅ Hfresh with "Hc") as "[Hc Hcall]".
  iModIntro. iFrame "Hcall".
  iExists (<[σ_t.(snc) := ∅]> M_call), M_tag, M_t, M_s. iFrame.
  iSplitL "Hpub_cid".
  { (* pub cid *) iApply (pub_cid_interp_preserve_initcall with "Hpub_cid"); done. }
  iSplitL.
  { iDestruct "Hsrel" as "(H1 & %H2 & H3 & %H4 & %H5 & H6)". rewrite /state_rel. simpl.
    iFrame "H1 H3".
    iSplit. { iPureIntro. rewrite union_comm_L. eapply trees_equal_mono; last done. apply Hwf_s. }
    iSplit. { iPureIntro. lia. }
    iSplit. { rewrite H5 Hsnc_eq. done. }
    iIntros (l Hl). iDestruct ("H6" $! l with "[//]") as "[Hpub | (%t & %Hpriv)]".
    - iLeft. iApply "Hpub".
    - iRight. iPureIntro. exists t.
      destruct Hpriv as (tk & Htk & Hs & [-> | (c' & -> & Hin)]).
      { exists tk_local. split_and!; eauto. }
      exists (tk_unq tk_act). split_and!; [done.. | ]. right. exists c'. split; first done.
      destruct Hin as (M' & HM' & Hin). exists M'.
      split; last done. apply lookup_insert_Some. right. split; last done.
      apply Hcall_interp in HM' as (Hwf_tag & _).
      specialize (state_wf_cid_agree _ Hwf_t _ Hwf_tag). lia.
  }
  iSplitL.
  { iPureIntro. intros c M'. simpl. rewrite lookup_insert_Some. intros [(<- & <-) | [Hneq Hsome]].
    - split; first set_solver. intros ? ?. rewrite lookup_empty. congruence.
    - rewrite elem_of_union. apply Hcall_interp in Hsome as [Hin Ha]. split; [by eauto | done].
  }
  iSplitL.
  { iPureIntro. destruct Htag_interp as (H1&H2&H3&H4&H5). split; last done.
    intros t tk (H6&H7&Hl&Hr&H8)%H1. split_and!; try done.
    - intros l sc H%Hl. eapply loc_controlled_add_protected; last done; try done.
      intros blk tg it c (tr&Htr1&Htr2) Hpp. simpl.
      rewrite /call_is_active. split; first set_solver.
      intros [Heq%elem_of_singleton|?]%elem_of_union; last set_solver.
      pose proof (state_wf_tree_compat _ Hwf_t blk tr Htr1) as Hitems.
      setoid_rewrite every_node_iff_every_lookup in Hitems.
      2: by eapply wf_tree_tree_item_determined, Hwf_t.
      apply Hitems in Htr2. eapply (item_cid_valid _ _ _ Htr2) in Hpp. lia.
    - intros l sc H%Hr. rewrite -!Hsnc_eq. eapply loc_controlled_add_protected; last done; try done.
      intros blk tg it c (tr&Htr1&Htr2) Hpp. simpl.
      rewrite /call_is_active. split; first set_solver.
      intros [Heq%elem_of_singleton|?]%elem_of_union; last set_solver.
      pose proof (state_wf_tree_compat _ Hwf_s blk tr Htr1) as Hitems.
      setoid_rewrite every_node_iff_every_lookup in Hitems.
      2: by eapply wf_tree_tree_item_determined, Hwf_s.
      apply Hitems in Htr2. eapply (item_cid_valid _ _ _ Htr2) in Hpp. lia.
     }
  iSplit; iPureIntro.
  all: by eapply initcall_step_wf_inner.
Qed.

Lemma sim_init_call π Φ :
  (∀ c, c @@ ∅ -∗
    #[ScCallId c] ⪯{π} #[ScCallId c] [{ Φ }]) -∗
  InitCall ⪯{π} InitCall [{ Φ }].
Proof.
  iIntros "Hsim". iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s T_s K_s) "((HP_t & HP_s & Hbor) & _ & _)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  iMod (bor_interp_init_call with "Hbor") as "[Hc Hbor]". iModIntro.
  iSplitR.
  { iPureIntro. do 3 eexists. eapply init_call_base_step. }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_init_call_inv _ _ _ _ _ Hhead) as (c & Heqc & -> & -> & ->).
  iModIntro. iExists (#[ScCallId σ_s.(snc)])%E, [], (mkState σ_s.(shp) σ_s.(strs) ({[ σ_s.(snc) ]} ∪ σ_s.(scs)) σ_s.(snp) (S σ_s.(snc))).
  iSplitR. { iPureIntro. eapply init_call_base_step. }
  iSplitR "Hsim Hc"; first last.
  { iSplitL; last done. destruct Hp as (_ & _ & Heqc' & _). rewrite Heqc Heqc'. by iApply "Hsim". }
  iFrame.
Qed.

Lemma sim_cid_make_public c e_t e_s π Φ :
  c @@ ∅ -∗
  (sc_rel (ScCallId c) (ScCallId c) -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }].
Proof.
  iIntros "Hown Hsim". iApply sim_update_si. iIntros (P_t σ_t P_s σ_s T_s) "(HP_t & HP_s & Hbor)".
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iMod (call_id_make_public with "Hpub_cid Hown") as "[#Hpub Hpub_cid]".
  iModIntro. iSplitR "Hsim".
  { iFrame "HP_t HP_s". iExists M_call, M_tag, M_t, M_s. iFrame. eauto. }
  iApply "Hsim".
  simpl. eauto.
Qed.

(** EndCall *)

Lemma sim_endcall_own c π Φ :
  c @@ ∅ -∗ (* needs to be empty so we don't trip private locations *)
  #[☠] ⪯{π} #[☠] [{ Φ }] -∗
  EndCall #[ScCallId c] ⪯{π} EndCall #[ScCallId c] [{ Φ }].
Proof.
  iIntros "Hcall Hsim". iApply sim_lift_base_step_both.
  iIntros (P_t P_s σ_t σ_s T_s K_s) "((HP_t & HP_s & Hbor) & %Hpool & %Hsafe)".
  iModIntro.
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  specialize (pool_safe_implies Hsafe Hpool) as (?&[= <-]&Hcall_in & trss' & Htrss).
  edestruct trees_equal_read_all_protected_initialized as (trst' & Htrst & Htrseq').
  3: exact Hstrs_eq. 3: exact Htrss. 1: by eapply Hwf_s. 1: by eapply Hwf_t.
  iSplit.
  { iPureIntro. do 3 eexists. eapply end_call_base_step. all: by rewrite -Hscs_eq. }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_end_call_inv _ _ _ _ _ _ Hhead) as (? & H & Hcall_int & -> & -> & ->).
  rewrite -Hscs_eq Htrst in H; injection H as <-.
  iExists (#[ ☠]%V)%E, [], (mkState σ_s.(shp) trss' (σ_s.(scs) ∖ {[c]}) σ_s.(snp) σ_s.(snc)).
  iSplitR. { iPureIntro. by eapply end_call_base_step. }
  iSplitR "Hsim"; last (simpl; by iFrame).
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  specialize (state_wf_cid_agree _ Hwf_s _ Hcall_in) as Hlt_s.
  iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hlookup".
  iMod (ghost_map_delete with "Hc Hcall") as "Hc". iModIntro. simpl. iFrame "HP_s HP_t".
  iExists (delete c M_call), M_tag, M_t, M_s. rewrite /bor_interp_inner. iFrame.
  iSplitL "Hpub_cid".
  { iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); simpl; [set_solver.. | done]. }
  iSplitL "Hsrel".
  { iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hl)". rewrite /state_rel. simpl.
    iSplit; first done. iSplit.
    { iPureIntro. eapply trees_equal_remove_call. 7: done. 5-6: done. 1,3: by eapply Hwf_s. 1,2: by eapply Hwf_t. }
    do 3 (iSplit; first (iPureIntro; try done; by f_equal)).
    iIntros (l Hl). iDestruct ("Hl" $! l Hl) as "[Hpub|%Hpriv]".
    { iLeft. rewrite /pub_loc /=. iApply "Hpub". }
    { iRight. iPureIntro. destruct Hpriv as (t&tk&Htk&Hlu&Ht). exists t, tk. do 2 (split; first done).
      destruct Ht as [->|(c'&->&M&HM&Hin)]; first by left. right.
      exists c'; split; first done. exists M. split; last done.
      rewrite lookup_delete_ne //. intros <-.
      rewrite Hlookup in HM. injection HM as <-.
      destruct Hin as (x&b&Hx&_). by rewrite lookup_empty in Hx. }
  }
  iSplit.
  { iPureIntro. eapply call_set_interp_remove; simpl. 5: exact Hwf_t. 1-4,6: done.
    rewrite -Hscs_eq //. }
  iSplit.
  { iPureIntro. split_and!. 2-5: by eapply Htag_interp.
    destruct Htag_interp as (H1&H2&H3&H4&H5).
    intros t tk Htk. simpl. destruct (H1 t tk Htk) as (Hval1&Hval2&Hlu1&Hlu2&Hagree).
    split_and!; try done.
    - intros l sc Hlusc.
      specialize (Hlu1 l sc Hlusc).
      eapply loc_controlled_trees_read_all_protected_initialized. 8: exact Hlu1.
      1: rewrite -Hscs_eq; exact Htrst. 1-4: done. 1-2: done.
    - intros l sc Hlusc.
      specialize (Hlu2 l sc Hlusc).
      eapply loc_controlled_trees_read_all_protected_initialized. 8: exact Hlu2.
      1: exact Htrss. 1-4: done. 1-2: done.
 }
  iSplit; iPureIntro.
  all: eapply endcall_step_wf_inner.
  all: try done; by rewrite -Hscs_eq.
Qed.

Lemma sim_endcall π Φ c c' :
  sc_rel (ScCallId c') (ScCallId c) -∗
  #[☠] ⪯{π} #[☠] [{ Φ }] -∗
  EndCall #[ScCallId c'] ⪯{π} EndCall #[ScCallId c] [{ Φ }].
Proof.
  iIntros "#[-> Hsc] Hsim". iApply sim_lift_base_step_both.
  iIntros (P_t P_s σ_t σ_s T_s K_s) "((HP_t & HP_s & Hbor) & %Hpool & %Hsafe)".
  iModIntro.
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  specialize (pool_safe_implies Hsafe Hpool) as (?&[= <-]&Hcall_in & trss' & Htrss).
  edestruct trees_equal_read_all_protected_initialized as (trst' & Htrst & Htrseq').
  3: exact Hstrs_eq. 3: exact Htrss. 1: by eapply Hwf_s. 1: by eapply Hwf_t.
  iSplit.
  { iPureIntro. do 3 eexists. eapply end_call_base_step. all: by rewrite -Hscs_eq. }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_end_call_inv _ _ _ _ _ _ Hhead) as (? & H & Hcall_int & -> & -> & ->).
  rewrite -Hscs_eq Htrst in H; injection H as <-.
  iExists (#[ ☠]%V)%E, [], (mkState σ_s.(shp) trss' (σ_s.(scs) ∖ {[c]}) σ_s.(snp) σ_s.(snc)).
  iSplitR. { iPureIntro. by eapply end_call_base_step. }
  iSplitR "Hsim"; last (simpl; by iFrame).
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  specialize (state_wf_cid_agree _ Hwf_s _ Hcall_in) as Hlt_s.
  iPoseProof (pub_cid_endcall with "Hsc Hpub_cid") as "(Hcall & Hpub_cid)".
  1: done. 1: done. 1: by rewrite -Hsnc_eq.
  iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hlookup".
  iMod (ghost_map_delete with "Hc Hcall") as "Hc". iModIntro. simpl. iFrame "HP_s HP_t".
  iExists (delete c M_call), M_tag, M_t, M_s. rewrite /bor_interp_inner. iFrame.
  iSplitL "Hsrel".
  { iDestruct "Hsrel" as "(_ & _ & _ & _ & _ & Hl)". rewrite /state_rel. simpl.
    iSplit; first done. iSplit.
    { iPureIntro. eapply trees_equal_remove_call. 7: done. 5-6: done. 1,3: by eapply Hwf_s. 1,2: by eapply Hwf_t. }
    do 3 (iSplit; first (iPureIntro; try done; by f_equal)).
    iIntros (l Hl). iDestruct ("Hl" $! l Hl) as "[Hpub|%Hpriv]".
    { iLeft. rewrite /pub_loc /=. iApply "Hpub". }
    { iRight. iPureIntro. destruct Hpriv as (t&tk&Htk&Hlu&Ht). exists t, tk. do 2 (split; first done).
      destruct Ht as [->|(c'&->&M&HM&Hin)]; first by left. right.
      exists c'; split; first done. exists M. split; last done.
      rewrite lookup_delete_ne //. intros <-.
      rewrite Hlookup in HM. injection HM as <-.
      destruct Hin as (x&b&Hx&_). by rewrite lookup_empty in Hx. }
  }
  iSplit.
  { iPureIntro. eapply call_set_interp_remove; simpl. 5: exact Hwf_t. 1-4,6: done.
    rewrite -Hscs_eq //. }
  iSplit.
  { iPureIntro. split_and!. 2-5: by eapply Htag_interp.
    destruct Htag_interp as (H1&H2&H3&H4&H5).
    intros t tk Htk. simpl. destruct (H1 t tk Htk) as (Hval1&Hval2&Hlu1&Hlu2&Hagree).
    split_and!; try done.
    - intros l sc Hlusc.
      specialize (Hlu1 l sc Hlusc).
      eapply loc_controlled_trees_read_all_protected_initialized. 8: exact Hlu1.
      1: rewrite -Hscs_eq; exact Htrst. 1-4: done. 1-2: done.
    - intros l sc Hlusc.
      specialize (Hlu2 l sc Hlusc).
      eapply loc_controlled_trees_read_all_protected_initialized. 8: exact Hlu2.
      1: exact Htrss. 1-4: done. 1-2: done.
 }
  iSplit; iPureIntro.
  all: eapply endcall_step_wf_inner.
  all: try done; by rewrite -Hscs_eq.
Qed.

(** Call *)
Lemma sim_call fn (r_t r_s : result) π Φ :
  rrel r_t r_s -∗
  (∀ r_t r_s : result, rrel r_t r_s -∗ Φ (of_result r_t) (of_result r_s)) -∗
  Call #[ScFnPtr fn] r_t ⪯{π} Call #[ScFnPtr fn] r_s [{ Φ }].
Proof.
  iIntros "Hval Hsim". iApply (sim_lift_call _ fn r_t r_s with "[Hval]"); first done. by iApply "Hsim".
Qed.

(** Coinduction on while loops *)
Lemma sim_while_while inv c_t c_s b_t b_s π Ψ :
  inv -∗
  □ (inv -∗
      (if: c_t then b_t ;; while: c_t do b_t od else #[☠])%E ⪯{π}
      (if: c_s then b_s ;; while: c_s do b_s od else #[☠])%E
        [{ λ e_t e_s, Ψ e_t e_s ∨ (⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗ inv) }]) -∗
  (while: c_t do b_t od ⪯{π} while: c_s do b_s od [{ Ψ }])%E.
Proof.
  iIntros "Hinv_init #Hstep".
  iApply (sim_lift_coind_pure inv with "[] Hinv_init");
    [apply pure_while | apply pure_while | done.. ].
Qed.


(** fork *)
Lemma sim_fork π e_t e_s Ψ :
  #[☠] ⪯{π} #[☠] [{ Ψ }] -∗
  (∀ π', e_t ⪯{π'} e_s {{ rrel }}) -∗
  Fork e_t ⪯{π} Fork e_s [{ Ψ }].
Proof.
  iIntros "Hval Hsim". iApply sim_lift_base_step_both.
  iIntros (??????) "[Hstate [% %]] !>".
  iSplitR. { iPureIntro. eexists _, _, _. econstructor. econstructor. }
  iIntros (e_t' efs_t σ_t') "%"; inv_base_step.
  iModIntro. iExists _, _, _. iSplitR. { iPureIntro. econstructor. econstructor. }
  simpl. iFrame. iSplitL; last done.
  iApply "Hsim".
Qed.

End lifting.


