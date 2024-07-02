From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors.
From simuliris.tree_borrows Require Import wishlist trees_equal.
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

(** ** Copy lemmas *)
(* works with any tag *)
Lemma target_copy_protected v_t v_rd sz l_hl l_rd t Ψ c tk M L :
  sz ≠ 0%nat → (* if it is 0, use the zero-sized read lemma *)
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  (∀ off, range'_contains (l_rd.2, sz) off → ∃ ae, L !! (l_rd.1, off) = Some (EnsuringAccess ae)) →
  M !! t = Some L →
  c @@ M -∗
  t $$ tk -∗
  l_hl ↦t∗[tk]{t} v_t -∗
  (l_hl ↦t∗[tk]{t} v_t -∗ t $$ tk -∗ c @@ M -∗ target_red #v_rd Ψ)%E -∗
  target_red (Copy (Place l_rd t sz)) Ψ.
Proof.
  iIntros (Hnz Hread Hsameblk Hprot1 Hprot2) "Hprot3 Htag Ht Hsim". eapply read_range_length in Hread as HH. subst sz.
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iPoseProof (bor_interp_readN_target_protected with "Hbor Hprot3 Ht Htag") as "(%it&%tr&%Hit&%Htr&%Hprot&%Hown)".
  1: exact Hread. 1: done. 1: done. 1: done. 1: done.
  opose proof* (read_range_list_to_heaplet_read_memory_strict) as READ_MEM. 1: exact Hread. 1: done.
  { intros i Hi. by eapply Hown. }
  destruct l_hl as [blk off_hl], l_rd as [blk2 off_rd]; simpl in *; subst blk2.
  odestruct (bor_state_own_enables_read false (off_rd, length v_rd)) as (Hcontain&trs'&Htrs').
  1: exact Hwf_t.
  { intros l (Hl1&Hl2); simpl in *. exists it, tr. do 2 (split; first done). assert (∃ (i:nat), l = off_rd + i) as (ii&Hii).
    1: exists (Z.to_nat (l - off_rd)); lia. subst l. eapply Hown. lia. } 1: simpl; lia.
  iSplit.
  { iPureIntro. do 3 eexists. eapply copy_base_step'. 1: done. 2: exact READ_MEM. 2: exact Htrs'. done. }
  iIntros (??? Hstep). pose proof Hstep as Hstep2.
  eapply head_copy_inv in Hstep2 as (->&[((HNone&_&_&_)&_)|(trs''&v'&->&->&Hreadv'&[(_&Htrs''&Hnon)|(Hzero&->&->)])]).
  1: rewrite /= Htrs' // in HNone. 2: done.
  assert (trs'' = trs') as ->.
  { rewrite /memory_access Htrs' in Htrs''. congruence. }
  assert (v_rd = v') as -> by congruence.
  assert (trees_equal (scs σ_s) (strs σ_s) trs') as Hstrs_eq'.
  { eapply trees_equal_trans. 3: eassumption. 1: rewrite Hscs_eq. 1-2: by eapply Hwf_t.
    eapply apply_within_trees_lift. 2: exact Htrs'. 1: by eapply Hwf_t. simpl.
    intros trX tr' HH1 HH2 HH3. simpl in *. assert (tr = trX) as <- by congruence.
    eapply tree_equal_asymmetric_read_protected.
    5: rewrite Hscs_eq; eapply HH3. 2: done. 1: by eapply Hwf_t. 1: by rewrite Hscs_eq.
    eapply asymmetric_read_prot_pre_from_bor_state_own. 3: done. 2: done. 1: done. intros off (Ho1&Ho2); simpl in *.
    assert (∃ (i:nat), off = off_rd + i) as (i&->) by (exists (Z.to_nat (off - off_rd)); lia).
    eapply Hown. 1: lia. }

  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag".
  iPoseProof (ghost_map_lookup with "Htag_t_auth Ht") as "%Ht".
  iPoseProof (ghost_map_lookup with "Hc Hprot3") as "%Hprot3".

  iModIntro. iSplit; first done.
  iSplitR "Ht Htag Hprot3 Hsim".
  2: iApply ("Hsim" with "Ht Htag Hprot3").
  iFrame "HP_t HP_s". iExists M_call, M_tag, M_t, M_s.
  iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
  iSplitL "Hpub_cid". 2: iSplit; last iSplit; last (iPureIntro; split_and!).
  - iApply (pub_cid_interp_preserve_sub with "Hpub_cid"); done.
  - repeat (iSplit; first done).
    simpl. iIntros (l) "Hs". iPoseProof (state_rel_pub_or_priv with "Hs Hsrel") as "$".
  - (* call invariant *)
    iPureIntro. intros c' M' HM'_some.
    specialize (Hcall_interp _ M' HM'_some) as (Hin & Hprot').
    split; first by apply Hin. intros pid L' HL_some. specialize (Hprot' _ _ HL_some) as [Hpid Hprot'].
    split; first by apply Hpid. intros l b Hin_l.
    specialize (Hprot' l b Hin_l).
    eapply (tag_protected_preserved_by_access). 2: apply Htrs'. 1: apply Hwf_t. all: done.
  - (* tag invariant *)
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom & Hunq1 & Hunq2). split_and!; [ | done..].
    intros t' tk' Htk_some. destruct (Htag_interp _ _ Htk_some) as (Hsnp_lt_t & Hsnp_lt_s & Hlocal & Hctrl_t & Hctrl_s & Hag).
    split_and!; [ done | done | | | | done ].
    + done.
    + intros l sc_t Hsc_t. eapply loc_controlled_read_preserved_everywhere.
      1: eapply Htrs'. 1: done. 1: by rewrite -Hscs_eq. 1-2: done.
      by eapply Hctrl_t.
    + eapply Hctrl_s.
  - done.
  - eapply base_step_wf; done.
Qed.

Lemma source_copy_protected v_t v_rd sz l_hl l_rd t π Ψ c tk M L :
  sz ≠ 0%nat → (* if it is 0, use the zero-sized read lemma *)
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  (∀ off, range'_contains (l_rd.2, sz) off → ∃ ae, L !! (l_rd.1, off) = Some (EnsuringAccess ae)) →
  M !! t = Some L →
  c @@ M -∗
  t $$ tk -∗
  l_hl ↦s∗[tk]{t} v_t -∗
  (l_hl ↦s∗[tk]{t} v_t -∗ t $$ tk -∗ c @@ M -∗ source_red #v_rd π Ψ)%E -∗
  source_red (Copy (Place l_rd t sz)) π Ψ.
Proof.
  iIntros (Hnz Hread Hsameblk Hprot1 Hprot2) "Hprot3 Htag Hs Hsim". eapply read_range_length in Hread as HH. subst sz.
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s T_s K_s) "((HP_t & HP_s & Hbor)&%Ht_s)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iPoseProof (bor_interp_readN_source_protected with "Hbor Hprot3 Hs Htag") as "(%it&%tr&%Hit&%Htr&%Hprot&%Hown)".
  1: exact Hread. 1: done. 1: done. 1: done. 1: done.
  opose proof* (read_range_list_to_heaplet_read_memory_strict) as READ_MEM. 1: exact Hread. 1: done.
  { intros i Hi. by eapply Hown. }
  destruct l_hl as [blk off_hl], l_rd as [blk2 off_rd]; simpl in *; subst blk2.
  odestruct (bor_state_own_enables_read false (off_rd, length v_rd)) as (Hcontain&trs'&Htrs').
  1: exact Hwf_s.
  { intros l (Hl1&Hl2); simpl in *. exists it, tr. do 2 (split; first done). assert (∃ (i:nat), l = off_rd + i) as (ii&Hii).
    1: exists (Z.to_nat (l - off_rd)); lia. subst l. eapply Hown. lia. } 1: simpl; lia.
  iExists _, _.
  iSplit.
  { iPureIntro.  eapply copy_base_step'. 1: done. 2: exact READ_MEM. 2: exact Htrs'. done. }
  assert (trees_equal (scs σ_s) trs' (strs σ_t)) as Hstrs_eq'.
  { eapply trees_equal_sym, trees_equal_trans. 3: eapply trees_equal_sym; eassumption. 1-2: by eapply Hwf_s.
    eapply apply_within_trees_lift. 2: exact Htrs'. 1: by eapply Hwf_s. simpl.
    intros trX tr' HH1 HH2 HH3. simpl in *. assert (tr = trX) as <- by congruence.
    eapply tree_equal_asymmetric_read_protected.
    5: eapply HH3. 2: done. 1: by eapply Hwf_s. 1: done.
    eapply asymmetric_read_prot_pre_from_bor_state_own. 3: done. 2: done. 1: done. intros off (Ho1&Ho2); simpl in *.
    assert (∃ (i:nat), off = off_rd + i) as (i&->) by (exists (Z.to_nat (off - off_rd)); lia).
    eapply Hown. 1: lia. }

  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hs".
  iPoseProof (ghost_map_lookup with "Hc Hprot3") as "%Hprot3".

  iModIntro.
  iSplitR "Hs Htag Hprot3 Hsim".
  2: iApply ("Hsim" with "Hs Htag Hprot3").
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

(*

Lemma source_copy_protected v_s v_rd sz l_hl l_rd t π Ψ :
  read_range l_rd.2 sz (list_to_heaplet v_s l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  t $$ tk_local -∗
  l_hl ↦s∗[tk_local]{t} v_s -∗
  (l_hl ↦s∗[tk_local]{t} v_s -∗ t $$ tk_local -∗ source_red #v_rd π Ψ)%E -∗
  source_red (Copy (Place l_rd t sz)) π Ψ.
Proof.
  iIntros (Hread Hsameblk) "Htag Ht Hsim". eapply read_range_length in Hread as HH. subst sz.
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s T_s K_s) "((HP_t & HP_s & Hbor)&%HT_s&%Hpool_safe)".
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %]".
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iPoseProof (bor_interp_readN_source_local with "Hbor Ht Htag") as "(%Hd & %it & %Hit & %Hitinv & %Hittag)".
  opose proof* (read_range_list_to_heaplet_read_memory) as READ_MEM. 1: exact Hread. 1: done. 1: exact Hd.
  destruct l_hl as [blk off_hl], l_rd as [blk2 off_rd]; simpl in *; subst blk2.
  eapply mk_is_Some in Hread as Hrangebounds. rewrite -read_range_valid_iff in Hrangebounds.
  setoid_rewrite <- list_to_heaplet_dom in Hrangebounds.
  opose proof* (local_access_preserves_unchanged _ _ _ _ off_hl off_rd v_s (length v_rd)) as TREES_NOCHANGE. 3: exact Hd.
  3: exists it; split; first done; split; first done; exact Hittag. 1: done.
  { destruct v_rd as [|? v_rd]; first by left. simpl in *. right. split. 1: ospecialize (Hrangebounds off_rd _); try lia.
    ospecialize (Hrangebounds (off_rd + (length v_rd)) _); lia. }
  do 2 iExists _.
  iSplit.
  { iPureIntro. eapply copy_base_step'. 1: done. 2: exact READ_MEM. 2: exact TREES_NOCHANGE.
    rewrite /trees_contain /trees_at_block /= Hit. subst t. cbv. tauto. }
  iModIntro.
  iSplitR "Htag Ht Hsim"; last first.
  1: iApply ("Hsim" with "Ht Htag").
  iFrame. destruct σ_s; simpl.
  iExists _, _, _, _. iApply "Hbor".
Qed.

(** ** Write *)

Lemma target_write_protected_active v_t v_wr sz l_hl l_rd v_t' t Ψ :
  write_range l_hl.2 l_rd.2 v_wr v_t = Some v_t' →
  l_hl.1 = l_rd.1 →
  sz = length v_wr →
  t $$ tk_local -∗
  l_hl ↦t∗[tk_local]{t} v_t -∗
  (l_hl ↦t∗[tk_local]{t} v_t' -∗ t $$ tk_local -∗ target_red #[☠] Ψ)%E -∗
  target_red (Write (Place l_rd t sz) #v_wr) Ψ.
Proof.
  iIntros (Hwrite Hsameblk Hlen) "Htag Ht Hsim". eapply write_range_same_length in Hwrite as Hlength. subst sz.
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iPoseProof (bor_interp_readN_target_local with "Hbor Ht Htag") as "(%Hd & %it & %Hit & %Hitinv & %Hittag)".
  opose proof* (write_range_write_memory) as (hp'&WRITE_MEM&Hd'). 1: exact Hwrite. 1: done. 1: exact Hd.
  destruct l_hl as [blk off_hl], l_rd as [blk2 off_rd]; simpl in *; subst blk2.
  eapply mk_is_Some in Hwrite as Hrangebounds. rewrite -write_range_valid_iff in Hrangebounds.
  opose proof* (local_access_preserves_unchanged _ _ _ _ off_hl off_rd v_t (length v_wr)) as TREES_NOCHANGE. 3: exact Hd.
  3: exists it; split; first done; split; first done; exact Hittag. 1: done.
  { destruct v_wr as [|x v_wr]; first by left. simpl in *. right. split; lia. }
  assert (∀ n : nat, (n < length v_wr)%nat → (blk, off_rd) +ₗ n ∈ dom (shp σ_t)) as WRITE_PRE.
  { intros n Hn. assert (∃ k, off_rd + n = off_hl + (k + n)%nat) as [k Hk].
    { eexists (Z.to_nat (off_rd - off_hl)). simpl. lia. }
    rewrite /shift_loc /= Hk. eapply elem_of_dom. rewrite (Hd (k+n)%nat). 2: lia.
    eapply lookup_lt_is_Some. lia. }
  iSplit.
  { iPureIntro. do 3 eexists. eapply write_base_step'. 1: done. 3: exact TREES_NOCHANGE.
    2: { rewrite /trees_contain /trees_at_block /= Hit. subst t. cbv. tauto. } done. } 
  iIntros (??? Hstep). pose proof Hstep as Hstep2.
  eapply head_write_inv in Hstep2 as (trs'&->&->&->&_&Hiinv&[(Hcont&Happly&Hlen)|(Hlen&->)]); last first.
  { iModIntro. iSplit; first done.
    assert (v_wr = nil) as -> by by destruct v_wr. iFrame.
    iSplitL "Hbor". 1: repeat iExists _; destruct σ_t; done.
    eapply write_range_to_list_is_Some in Hwrite as (x&Hx&_). simpl in Hx. subst v_t'.
    iApply ("Hsim" with "Ht Htag"). }
  rewrite WRITE_MEM. simpl in Happly. assert (trs' = strs σ_t) as -> by congruence.
  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag".
  iPoseProof (ghost_map_lookup with "Htag_t_auth Ht") as "%Hhl".
  iMod (ghost_map_update (list_to_heaplet v_t' off_hl) with "Htag_t_auth Ht") as "(Htag_t_auth&Ht)". simpl.
  iModIntro.
  iSplit; first done.
  iSplitR "Hsim Htag Ht".
  2: iApply ("Hsim" with "Ht Htag"). iFrame "HP_t HP_s".
  iExists M_call, M_tag, (<[(t, blk):=list_to_heaplet v_t' off_hl]> M_t), M_s.
  iFrame. simpl. iSplit.
  { iSplit; last iSplit; last iSplit; last iSplit; last iSplit; try iPureIntro.
    { simpl. rewrite Hdom_eq. subst hp'. erewrite write_mem_dom_sane; first done. done. }
    1-4: done.
    simpl. iIntros (l Hl%elem_of_dom). rewrite -WRITE_MEM write_mem_dom_sane in Hl. 2: exact WRITE_PRE.
    eapply elem_of_dom in Hl.
    iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
    destruct (decide (l.1 = blk ∧ off_hl ≤ l.2 < off_hl + length v_t')) as [(<-&Hrange)|Hout].
    { iRight. iExists t. iPureIntro. exists tk_local. split; first done. split; last by left.
      rewrite /heaplet_lookup lookup_insert /=. destruct (list_to_heaplet v_t' off_hl !! l.2) eqn:HH; first done.
      eapply list_to_heaplet_lookup_None in HH. lia. }
    { iDestruct ("Hsrel" $! l Hl) as "[H|%Hpriv]".
      - iLeft. iIntros (sc Hsc). iApply "H".
        iPureIntro. rewrite /= -WRITE_MEM write_mem_lookup_outside // in Hsc. simpl; lia.
      - iRight. iPureIntro. destruct Hpriv as (t'&tk&Htk&Htkhl&Hrst). exists t', tk.
        split; first done. split; last done. rewrite /heaplet_lookup /= lookup_insert_ne //.
        intros [= -> ->]. destruct Htkhl as (x&(hl2&Hhl2&HHhl2)%bind_Some). simpl in *.
        rewrite Hhl2 in Hhl. injection Hhl as ->. eapply list_to_heaplet_lookup_Some in HHhl2. lia. } }
  iPureIntro. split_and!.
  - eapply call_set_interp_mono. 2: exact Hcall_interp.
    intros ?? l it' ???? (tk&Htk&Hhltk).
    exists tk. split; first done. rewrite /heaplet_lookup /=.
    destruct (decide ((t, blk) = (itag it', l.1))) as [Heq|Hne].
    2: by rewrite lookup_insert_ne.
    rewrite Heq lookup_insert /=. eapply elem_of_dom, list_to_heaplet_dom.
    rewrite -Hlength. eapply list_to_heaplet_dom, elem_of_dom. rewrite /heaplet_lookup -Heq Hhl /= // in Hhltk.
  - destruct Htag_interp as (Ht1&Ht2&Ht3&Ht4&Ht5). split_and!.
    + intros t' tk' Htk'. destruct (Ht1 t' tk' Htk') as (HHt1&HHt2&HHtlocal&HHt3&HHt4&HHt5). split_and!.
      * done.
      * done.
      * intros ->. destruct (HHtlocal) as (Htl1&Htl2); first done. split.
        -- intros ? M [([= -> ->]&H2)|(H1&H2)]%lookup_insert_Some.
           2: by eapply Htl1. subst M. intros H%list_to_heaplet_empty_length.
           eapply Htl1. 1: eapply Hhl. simpl. eapply list_to_heaplet_empty_length. lia.
        -- done.
      * intros l sc (M&HM%lookup_insert_Some&HinM)%bind_Some. simpl in HM.
        destruct HM as [([= -> ->]&HM)|(Hne&HM)].
        -- assert (tk' = tk_local) as -> by congruence. simpl. subst M. 
           assert (∃ sc_old, heaplet_lookup M_t (t', l) = Some sc_old) as [sc_old Hscold].
           { rewrite /heaplet_lookup /= Hhl /=. eapply elem_of_dom_2 in HinM. simpl in HinM.
             erewrite list_to_heaplet_dom_1 in HinM. 2: symmetry; exact Hlength.
             by eapply elem_of_dom in HinM. }
           specialize (HHt3 _ _ Hscold) as (HH1&HH2). 1: done. intros _.
           split.
           1: by destruct σ_t.
           eapply list_to_heaplet_lookup_Some in HinM as HinM2. simpl in HinM2. simpl.
           assert (∃ (i:nat), l.2 = off_hl + i) as [i Hi].
           1: exists (Z.to_nat (l.2-off_hl)); lia.
           ospecialize (Hd' i _). 1: lia. destruct l as [l1 l2]. rewrite /= /shift_loc /= -Hi /= in Hd'. 
           rewrite Hd'. rewrite Hi /= list_to_heaplet_nth // in HinM.
        -- simpl. intros H. destruct (HHt3 l sc) as [HH1 HH2].
           1: rewrite /heaplet_lookup HM /= HinM //. 1: apply H. split; first exact HH1.
           simpl. subst hp'. rewrite -HH2. eapply write_mem_lookup_outside. simpl.
           intros (Hx1&Hx2). eapply loc_controlled_write_invalidates_others.
           9: exact H. 8: { split; done. } 1: exact TREES_NOCHANGE. 2-4: done. 1: done. 1: congruence.
           subst t. rewrite /trees_contain /trees_at_block Hit. cbv. tauto.
      * done.
      * eapply dom_agree_on_tag_target_insert_same_dom. 3: done. 1: done.
        eapply list_to_heaplet_dom_1. lia.
    + intros ?? H%elem_of_dom. rewrite dom_insert_lookup_L in H. 2: done. by eapply Ht2, elem_of_dom.
    + done.
    + intros ??? H H2. rewrite !dom_insert_lookup_L in H,H2; last done. by eapply Ht4.
    + done.  
  - done.
  - subst hp'. eapply base_step_wf. 1: done. done.
Qed.

Lemma source_write_protected_active v_s v_wr sz l_hl l_rd v_s' t π Ψ :
  write_range l_hl.2 l_rd.2 v_wr v_s = Some v_s' →
  l_hl.1 = l_rd.1 →
  t $$ tk_local -∗
  l_hl ↦s∗[tk_local]{t} v_s -∗
  (l_hl ↦s∗[tk_local]{t} v_s' -∗ t $$ tk_local -∗ source_red #[☠] π Ψ)%E -∗
  source_red (Write (Place l_rd t sz) #v_wr) π Ψ.
Proof.
  iIntros (Hwrite Hsameblk) "Htag Hs Hsim". eapply write_range_same_length in Hwrite as Hlength.
  iApply source_red_lift_base_step. iIntros (P_t σ_t P_s σ_s T_s K_s) "((HP_t & HP_s & Hbor)&%HT_s&%Hpool_safe)".
  eapply @pool_safe_implies in Hpool_safe. 2: eapply safe_implies_write_length. 2: done.
  subst sz.
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iPoseProof (bor_interp_readN_source_local with "Hbor Hs Htag") as "(%Hd & %it & %Hit & %Hitinv & %Hittag)".
  opose proof* (write_range_write_memory) as (hp'&WRITE_MEM&Hd'). 1: exact Hwrite. 1: done. 1: exact Hd.
  destruct l_hl as [blk off_hl], l_rd as [blk2 off_rd]; simpl in *; subst blk2.
  eapply mk_is_Some in Hwrite as Hrangebounds. rewrite -write_range_valid_iff in Hrangebounds.
  opose proof* (local_access_preserves_unchanged _ _ _ _ off_hl off_rd v_s (length v_wr)) as TREES_NOCHANGE. 3: exact Hd.
  3: exists it; split; first done; split; first done; exact Hittag. 1: done.
  { destruct v_wr as [|x v_wr]; first by left. simpl in *. right. split; lia. }
  assert (∀ n : nat, (n < length v_wr)%nat → (blk, off_rd) +ₗ n ∈ dom (shp σ_s)) as WRITE_PRE.
  { intros n Hn. assert (∃ k, off_rd + n = off_hl + (k + n)%nat) as [k Hk].
    { eexists (Z.to_nat (off_rd - off_hl)). simpl. lia. }
    rewrite /shift_loc /= Hk. eapply elem_of_dom. rewrite (Hd (k+n)%nat). 2: lia.
    eapply lookup_lt_is_Some. lia. }
  assert (trees_contain t (strs σ_s) blk) as Hcontain.
  { rewrite /trees_contain /trees_at_block /= Hit. subst t. cbv. tauto. }
  iExists _, _. iSplit.
  { iPureIntro. eapply write_base_step'. 1: done. 3: exact TREES_NOCHANGE. all: done. }
  rewrite WRITE_MEM.
  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hhl".
  iMod (ghost_map_update (list_to_heaplet v_s' off_hl) with "Htag_s_auth Hs") as "(Htag_s_auth&Hs)". simpl.
  iModIntro. iFrame "HP_t HP_s".
  iSplitR "Hsim Htag Hs".
  2: iApply ("Hsim" with "Hs Htag"). 
  iExists M_call, M_tag, M_t, (<[(t, blk):=list_to_heaplet v_s' off_hl]> M_s).
  iFrame. simpl. iSplit.
  { iSplit; last iSplit; last iSplit; last iSplit; last iSplit; try iPureIntro.
    { simpl. rewrite -Hdom_eq. subst hp'. erewrite write_mem_dom_sane; first done. done. }
    1-4: done.
    simpl. iIntros (l Hl%elem_of_dom). simpl.
    iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
    destruct (decide (l.1 = blk ∧ off_hl ≤ l.2 < off_hl + length v_s')) as [(<-&Hrange)|Hout].
    { iRight. iExists t. iPureIntro. exists tk_local. split; first done. split; last by left.
      destruct Htag_interp as (Hti&_). specialize (Hti _ _ Htag).
      destruct Hti as (_&_&_&_&_&_&Hti). eapply Hti. simpl in Hhl.
      rewrite /heaplet_lookup Hhl /=. destruct (list_to_heaplet v_s off_hl !! l.2) eqn:HH; first done.
      eapply list_to_heaplet_lookup_None in HH. lia. }
    { eapply elem_of_dom in Hl. iDestruct ("Hsrel" $! l Hl) as "[H|%Hpriv]".
      - iLeft. iIntros (sc Hsc). iDestruct ("H" $! sc Hsc) as "(%sc2&%HH&HH)".
        iExists sc2. iSplit; last done. iPureIntro. simpl.
        rewrite /= -WRITE_MEM write_mem_lookup_outside //. simpl; lia.
      - iRight. iPureIntro. destruct Hpriv as (t'&tk&Htk&Htkhl&Hrst). exists t', tk.
        split; first done. split; last done. done. } }
  iPureIntro. split_and!.
  - done.
  - destruct Htag_interp as (Ht1&Ht2&Ht3&Ht4&Ht5). split_and!.
    + intros t' tk' Htk'. destruct (Ht1 t' tk' Htk') as (HHt1&HHt2&HHtlocal&HHt3&HHt4&HHt5). split_and!.
      * done.
      * done.
      * intros ->. destruct (HHtlocal) as (Htl1&Htl2); first done. split.
        -- done.
        -- intros ? M [([= -> ->]&H2)|(H1&H2)]%lookup_insert_Some.
           2: by eapply Htl2. subst M. intros H%list_to_heaplet_empty_length.
           eapply Htl2. 1: eapply Hhl. simpl. eapply list_to_heaplet_empty_length. lia.
      * done.
      * intros l sc (M&HM%lookup_insert_Some&HinM)%bind_Some. simpl in HM.
        destruct HM as [([= -> ->]&HM)|(Hne&HM)].
        -- assert (tk' = tk_local) as -> by congruence. simpl. subst M. 
           assert (∃ sc_old, heaplet_lookup M_s (t', l) = Some sc_old) as [sc_old Hscold].
           { rewrite /heaplet_lookup /= Hhl /=. eapply elem_of_dom_2 in HinM. simpl in HinM.
             erewrite list_to_heaplet_dom_1 in HinM. 2: symmetry; exact Hlength.
             by eapply elem_of_dom in HinM. }
           specialize (HHt4 _ _ Hscold) as (HH1&HH2). 1: done. intros _.
           split.
           1: done.
           eapply list_to_heaplet_lookup_Some in HinM as HinM2. simpl in HinM2. simpl.
           assert (∃ (i:nat), l.2 = off_hl + i) as [i Hi].
           1: exists (Z.to_nat (l.2-off_hl)); lia.
           ospecialize (Hd' i _). 1: lia. destruct l as [l1 l2]. rewrite /= /shift_loc /= -Hi /= in Hd'. 
           rewrite Hd'. rewrite Hi /= list_to_heaplet_nth // in HinM.
        -- simpl. intros H. destruct (HHt4 l sc) as [HH1 HH2].
           1: rewrite /heaplet_lookup HM /= HinM //. 1: apply H. split; first exact HH1.
           simpl. subst hp'. rewrite -HH2. eapply write_mem_lookup_outside. simpl.
           intros (Hx1&Hx2). eapply loc_controlled_write_invalidates_others.
           9: exact H. 8: { split; done. } 1: exact TREES_NOCHANGE. 2-4: done. 1: done. 1: congruence.
           subst t. rewrite /trees_contain /trees_at_block Hit. cbv. tauto.
      * eapply dom_agree_on_tag_source_insert_same_dom. 3: done. 1: done.
        eapply list_to_heaplet_dom_1. lia.
    + done.
    + intros ?? H%elem_of_dom. rewrite dom_insert_lookup_L in H. 2: done. by eapply Ht3, elem_of_dom.
    + done.  
    + intros ??? H H2. rewrite !dom_insert_lookup_L in H,H2; last done. by eapply Ht5.
  - subst hp'. eapply (base_step_wf P_s). 2: exact Hwf_s.
    eapply write_base_step'. 1: done. 3: exact TREES_NOCHANGE. all: done.
  - done.
Qed. *)

End lifting.
