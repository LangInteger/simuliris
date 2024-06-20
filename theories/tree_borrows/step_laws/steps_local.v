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
Lemma target_copy_local v_t v_rd sz l_hl l_rd t Ψ :
  read_range l_rd.2 sz (list_to_heaplet v_t l_hl.2) = Some v_rd →
  l_hl.1 = l_rd.1 →
  t $$ tk_local -∗
  l_hl ↦t∗[tk_local]{t} v_t -∗
  (l_hl ↦t∗[tk_local]{t} v_t -∗ t $$ tk_local -∗ target_red #v_rd Ψ)%E -∗
  target_red (Copy (Place l_rd t sz)) Ψ.
Proof.
  iIntros (Hread Hsameblk) "Htag Ht Hsim". eapply read_range_length in Hread as HH. subst sz.
  iApply target_red_lift_base_step. iIntros (P_t σ_t P_s σ_s ?) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %]".
  iModIntro. iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iPoseProof (bor_interp_readN_target_local with "Hbor Ht Htag") as "(%Hd & %it & %Hit & %Hitinv & %Hittag)".
  opose proof* (read_range_list_to_heaplet_read_memory) as READ_MEM. 1: exact Hread. 1: done. 1: exact Hd.
  destruct l_hl as [blk off_hl], l_rd as [blk2 off_rd]; simpl in *; subst blk2.
  eapply mk_is_Some in Hread as Hrangebounds. rewrite -read_range_valid_iff in Hrangebounds.
  setoid_rewrite <- list_to_heaplet_dom in Hrangebounds.
  opose proof* (local_access_preserves_unchanged _ _ _ _ off_hl off_rd v_t (length v_rd)) as TREES_NOCHANGE. 3: exact Hd.
  3: exists it; split; first done; split; first done; exact Hittag. 1: done.
  { destruct v_rd as [|x v_rd]; first by left. simpl in *. right. split. 1: ospecialize (Hrangebounds off_rd _); try lia.
    ospecialize (Hrangebounds (off_rd + (length v_rd)) _); lia. }
  iSplit.
  { iPureIntro. do 3 eexists. eapply copy_base_step'. 1: done. 2: exact READ_MEM. 2: exact TREES_NOCHANGE.
    rewrite /trees_contain /trees_at_block /= Hit. subst t. cbv. tauto. }
  iIntros (??? Hstep).
  eapply head_copy_inv in Hstep as (->&[((HNone&_&_&_)&_)|(trs'&v'&->&->&Hreadv'&[(_&Happly&Hnon)|(Hzero&->&->)])]).
  1: rewrite /= TREES_NOCHANGE // in HNone.
  - iModIntro. iSplitR; first done.
    assert (v_rd = v') as -> by congruence.
    iSplitR "Htag Ht Hsim"; last first.
    1: iApply ("Hsim" with "Ht Htag").
    iFrame. simpl in Happly. assert (trs' = strs σ_t) as -> by congruence.
    iExists _, _, _, _. destruct σ_t. iApply "Hbor".
  - iModIntro. iSplitR; first done.
    assert (v_rd = []) as -> by by destruct v_rd.
    iSplitR "Htag Ht Hsim"; last first.
    1: iApply ("Hsim" with "Ht Htag").
    iFrame.
    iExists _, _, _, _. destruct σ_t. iApply "Hbor".
Qed.



Lemma source_copy_local v_s v_rd sz l_hl l_rd t π Ψ :
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

Lemma target_write_local v_t v_wr sz l_hl l_rd v_t' t Ψ :
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

Lemma source_write_local v_s v_wr sz l_hl l_rd v_s' t π Ψ :
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
Qed.


(** ** Alloc *)
Lemma sim_alloc_local sz Φ π :
  (∀ t l, t $$ tk_local -∗
    l ↦t∗[tk_local]{t} replicate sz ☠%S -∗
    l ↦s∗[tk_local]{t} replicate sz ☠%S -∗
    Place l t sz ⪯{π} Place l t sz [{ Φ }]) -∗
  Alloc sz ⪯{π} Alloc sz [{ Φ }].
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

  (* allocate tag and heaplets *)
  pose (nt := σ_t.(snp)).
  pose vs := replicate sz ☠%S.
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  assert (M_tag !! nt = None) as HNone.
  { destruct (M_tag !! nt) as [[tk' []] | ] eqn:Hs; last done. exfalso.
    apply Htag_interp in Hs as (_ & H & _). unfold tag_valid in H. lia.
  }
  iMod (tkmap_insert tk_local nt () ltac:(done) with "Htag_auth") as "[Htag_auth Ht]".
  assert (∀ blk, M_t !! (nt, blk) = None) as HtNone.
  { intros blk. destruct Htag_interp as (_&H&_). specialize (H nt blk).
    destruct (M_t !! (nt, blk)); last done. destruct H as [x Hx]; try done. congruence. }
  assert (∀ blk, M_s !! (nt, blk) = None) as HsNone.
  { intros blk. destruct Htag_interp as (_&_&H&_). specialize (H nt blk).
    destruct (M_s !! (nt, blk)); last done. destruct H as [x Hx]; try done. congruence. }

  pose (blk := (fresh_block σ_t.(shp))). (* can be σ_s and σ_t, it does not matter. *)
  iMod (ghost_map_array_tag_insert _ _ vs nt (blk, 0) tk_local with "Htag_t_auth") as "(Hhl_t&Htag_t_auth)".
  1: by eapply HtNone.
  iMod (ghost_map_array_tag_insert _ _ vs nt (blk, 0) tk_local with "Htag_s_auth") as "(Hhl_s&Htag_s_auth)".
  1: by eapply HsNone.
  rewrite /array_tag_map /= -!insert_union_singleton_l.
  iModIntro.
  pose (l := (blk, 0)). 
  pose (α_t' := extend_trees ((snp σ_t)) blk 0 sz (strs σ_t)).
  pose (α_s' := extend_trees ((snp σ_s)) blk 0 sz (strs σ_s)).
  pose (σ_t' := (mkState (init_mem l sz σ_t.(shp)) α_t' σ_t.(scs) (S σ_t.(snp)) σ_t.(snc))).
  pose (σ_s' := (mkState (init_mem l sz σ_s.(shp)) α_s' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc))).
  assert (Hhead_s : base_step P_s (Alloc sz) σ_s (Place l (nt) sz) σ_s' []).
  { subst σ_s' nt α_s' blk l. rewrite -Hsnp_eq -(fresh_block_det σ_s σ_t); last done.
    eapply alloc_base_step; assumption.
  }
  iExists _, [], _. iSplitR; first done. simpl. iFrame "HP_t HP_s".
  iSplitR "Hsim Ht Hhl_s Hhl_t"; first last.
  { iSplitL; last done. subst nt l blk. iApply ("Hsim" with "Ht Hhl_t Hhl_s"). }
  (* re-establish the invariants *)
  iExists M_call, (<[nt := (tk_local, ())]> M_tag), (<[(nt, blk):=list_to_heaplet vs 0]> M_t), (<[(nt, blk):=list_to_heaplet vs 0]> M_s).
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
      * iRight. iPureIntro. exists nt, tk_local. subst vs.
        rewrite /heaplet_lookup !lookup_insert /=. split; first done.
        split. 1: eapply elem_of_dom, list_to_heaplet_dom; rewrite replicate_length; lia.
        by left.
      * iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
        unshelve iDestruct ("Hsrel" $! (blk', off') _) as "[Hsrel2|%Hpriv]".
        -- by eexists. 
        -- iLeft. iIntros (sc_t Hsc_t). cbn in Hsc_t.
           rewrite Hsc Hthru in Hsc_t.
           iDestruct ("Hsrel2" $! sc_t Hsc_t) as (sc_s Hsc_s) "Hsrel3".
           iExists (sc_s). subst σ_s'. cbn. rewrite init_mem_lookup_fresh_old; last done.
           iFrame "Hsrel3". done.
        -- iRight. iPureIntro. destruct Hpriv as (tg & tk & HtagSome & HSome & Hcases).
           exists tg, tk. split_and!. 
           3: done. 2: rewrite /heaplet_lookup lookup_insert_ne //. 2: simpl; congruence.
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
    + intros it (tr&Htr&Hit). simpl. rewrite /tag_protected_for in Hc4.
      assert (trees_lookup (strs σ_t) l'.1 t it) as Hlu.
      { exists tr; split; last done. rewrite /extend_trees in Htr.
        eapply lookup_insert_Some in Htr as [(Htr1&Htr2)|(Htr1&Htr2)]; last done.
        subst tr. destruct Hit as (H1&H2). eapply init_tree_contains_only in H1. subst t.
        rewrite /tag_valid in Hc3. lia. }
      specialize (Hc4 _ Hlu). split_and!; try by eapply Hc4. done.
    + eapply tag_protected_for_mono in Hc4.
      1: destruct Hc4 as (it & Hit & Hperm).
      1: exists it; split; last done.
      2: { intros l'' it ? ? ? (tk&Htk&Hhl). exists tk.
           rewrite /heaplet_lookup !lookup_insert_ne //. all: subst nt; simpl; intros [= Heq1].
           2: by rewrite -Heq1 HNone in Htk.
           destruct Hhl as (y&(x&Hx1&Hx2)%bind_Some). rewrite /= -Heq1 in Hx1.
           rewrite HtNone in Hx1. done. }
      destruct Hit as (trr&Hit1&Hit2); eexists; split; last done.
      rewrite /extend_trees lookup_insert_ne //.
      intros Heq. rewrite -Heq in Hit1.
      eapply elem_of_dom_2 in Hit1.
      rewrite state_wf_dom // in Hit1.
      by eapply is_fresh_block_fst in Hit1.
  - (* tag interp *)
    iPureIntro. destruct Htag_interp as (Htag_interp & Hdom_t & Hdom_s & Hunq1 & Hunq2). split_and!.
    { simpl. intros tr tk. rewrite lookup_insert_Some. intros [[<- [= <-]] | [Hneq Hsome]].
      - (* new tag: local, currently poison *)
        split_and!; [ rewrite /tag_valid; lia | rewrite /tag_valid; lia | | | |].
        + intros _; split; intros bb M [([= <-]&<-)|(Hne&HM)]%lookup_insert_Some.
          1,3: intros H%list_to_heaplet_empty_length; subst vs; rewrite replicate_length in H; lia.
          1: rewrite HtNone // in HM. 1: rewrite HsNone // in HM.
        + intros l' sc_t (M&[([= He1]&<-)|(Hne&Hhl)]%lookup_insert_Some&HM)%bind_Some.
          2: by rewrite /= HtNone in Hhl. eapply list_to_heaplet_lookup_Some in HM as Hbnd. simpl in Hbnd.
          assert (l'.2 = Z.of_nat (Z.to_nat l'.2)) as Heq by lia.
          rewrite /= -(Z.add_0_l l'.2) Heq list_to_heaplet_nth in HM. fold blk α_t' l σ_t'.
          subst vs. rewrite replicate_length in Hbnd.
          enough (sc_t = ScPoison) as ->.
          * eapply loc_controlled_alloc_creates_local. 1: done. 1: done. all: done.
          * eapply lookup_replicate in HM as (->&_). done.
        + intros l' sc_t (M&[([= He1]&<-)|(Hne&Hhl)]%lookup_insert_Some&HM)%bind_Some.
          2: by rewrite /= HsNone in Hhl. eapply list_to_heaplet_lookup_Some in HM as Hbnd. simpl in Hbnd.
          assert (l'.2 = Z.of_nat (Z.to_nat l'.2)) as Heq by lia.
          rewrite /= -(Z.add_0_l l'.2) Heq list_to_heaplet_nth in HM.
          subst vs. rewrite replicate_length in Hbnd.
          assert (fresh_block (shp σ_t) = fresh_block (shp σ_s)) as Hfresh.
          1: eapply fresh_block_equiv; try done; by rewrite Hdom_eq.
          enough (sc_t = ScPoison) as ->.
          * eapply (loc_controlled_alloc_creates_local _ σ_s σ_s').
            6: symmetry; eassumption.
            1: by rewrite -Hfresh.
            1: subst nt blk; rewrite Hfresh -Hsnp_eq //.
            1: rewrite -Hfresh //.
            1: done. 1: done. 1: by subst blk. 1: lia.
          * eapply lookup_replicate in HM as (->&_). done.
        + eapply dom_agree_on_tag_update_same. 2: eapply list_to_heaplet_dom_1; congruence.
          split; intros l' [x (M&HM%mk_is_Some&HHM)%bind_Some]; simpl in HM.
          1: eapply Hdom_t in HM. 2: eapply Hdom_s in HM.
          all: rewrite HNone in HM; by destruct HM.
      - (* old tag *)
        specialize (Htag_interp _ _ Hsome) as (Hv1 & Hv2 & Hlocal & Hcontrol_t & Hcontrol_s & Hag).
        split_and!; [inversion Hv1; simplify_eq; econstructor; lia | inversion Hv1; simplify_eq; econstructor; lia | .. ].
        + intros ->. split; intros bblk MM Hbblk.
          all: specialize (Hlocal eq_refl) as (HH1&HH2).
          * eapply HH1. rewrite lookup_insert_ne in Hbblk; first exact Hbblk. congruence.
          * eapply HH2. rewrite lookup_insert_ne in Hbblk; first exact Hbblk. congruence.
        +  intros l' sc_t. rewrite /heaplet_lookup /= lookup_insert_ne; last congruence.
           intros Hcontrol%Hcontrol_t. clear Hhead_s. eapply loc_controlled_alloc_update; done.
        + intros l' sc_s. rewrite /heaplet_lookup /= lookup_insert_ne; last congruence.
          intros Hcontrol%Hcontrol_s. clear α_t' σ_t' Hhead_s. subst σ_s' α_s' l blk.
          erewrite fresh_block_det; last done.
          eapply loc_controlled_alloc_update; try done.
          by rewrite Hsnp_eq.
        + eapply dom_agree_on_tag_upd_ne; done.
    }
    { intros t l'. rewrite !lookup_insert_is_Some'. intros [H|H]; last eauto. left. congruence. }
    { intros t l'. rewrite !lookup_insert_is_Some'. intros [H|H]; last eauto. left. congruence. }
    { intros tg ??. rewrite !dom_insert_L. intros [[= ??]%elem_of_singleton|H%elem_of_dom]%elem_of_union [[= ??]%elem_of_singleton|H2%elem_of_dom]%elem_of_union.
      1: congruence. 3: eapply Hunq1; by eapply elem_of_dom.
      1: subst tg; rewrite HtNone in H2; by destruct H2.
      1: subst tg; rewrite HtNone in H ; by destruct H. }
    { intros tg ??. rewrite !dom_insert_L. intros [[= ??]%elem_of_singleton|H%elem_of_dom]%elem_of_union [[= ??]%elem_of_singleton|H2%elem_of_dom]%elem_of_union.
      1: congruence. 3: eapply Hunq2; by eapply elem_of_dom.
      1: subst tg; rewrite HsNone in H2; by destruct H2.
      1: subst tg; rewrite HsNone in H ; by destruct H. }
  - iPureIntro. by eapply base_step_wf.
  - iPureIntro. by eapply base_step_wf.
Qed.

(*

(** ** Free *)
(* local ownership makes strong assertions: we also have to deallocate the corresponding ghost state. *)
Lemma bor_interp_free_local t v_t v_s l σ_t σ_s α' n :
  memory_deallocated (sst σ_t) (scs σ_t) l (Tagged t) n = Some α' →
  memory_deallocated (sst σ_s) (scs σ_s) l (Tagged t) n = Some α' →
  length v_t = n →
  length v_s = n →
  let σ_t' := mkState (free_mem l n σ_t.(shp)) α' σ_t.(scs) σ_t.(snp) σ_t.(snc) in
  let σ_s' := mkState (free_mem l n σ_s.(shp)) α' σ_s.(scs) σ_s.(snp) σ_s.(snc) in
  state_wf σ_t' →
  state_wf σ_s' →
  t $$ tk_local -∗
  l ↦t∗[tk_local]{t} v_t -∗
  l ↦s∗[tk_local]{t} v_s -∗
  bor_interp sc_rel σ_t σ_s ==∗
  t $$ tk_local ∗
  bor_interp sc_rel σ_t' σ_s'.
Proof.
  intros Hstack_t Hstack_s Hlen_t Hlen_s σ_t' σ_s' Hwf_t' Hwf_s'.
  iIntros "Htag Ht Hs Hbor".
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hcall_auth & Htag_auth & Htag_t_auth & Htag_s_auth) & Htaint_interp & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iMod (ghost_map_array_tag_delete with "Htag_t_auth Ht") as "Htag_t_auth".
  iMod (ghost_map_array_tag_delete with "Htag_s_auth Hs") as "Htag_s_auth".
  iModIntro. iFrame "Htag".
  iExists M_call, M_tag, (M_t ∖ array_tag_map l t v_t), (M_s ∖ array_tag_map l t v_s).
  iFrame.
  iSplitL "Htaint_interp".
  { (* tainted *)
    iApply (tag_tainted_interp_preserve σ_s with "Htaint_interp"). { simpl. lia. }
    intros l' stk' Hstk' it Hit. right. right.
    specialize (for_each_dealloc_lookup_Some _ _ _ _ _ Hstack_s _ _ Hstk') as (_ & Hstk). eauto.
  }
  iSplitL.
  { (* state rel *)
    (* TODO: partially duplicated from the refl lemma. prove more general lemma? *)
    iDestruct "Hsrel" as "(%Hdom_eq & %Hsst_eq & %Hsnp_eq & %Hsnc_eq & %Hscs_eq & Hsrel)".
    iSplitR. { iPureIntro. simpl. apply free_mem_dom. done. }
    simpl. do 4 (iSplitR; first done).
    iIntros (l' (sc & Hsome)).
    destruct (free_mem_lookup_case l' l n σ_t.(shp)) as [[Hi Heq] | (i & _ & -> & ?)]; last congruence.
    rewrite Heq in Hsome. iDestruct ("Hsrel" $! l' with "[]") as "[Hpubl | (%t' & %Hprivl)]"; first by eauto.
    + iLeft. iIntros (sc_t Hsc_t). simpl in *.
      rewrite Heq in Hsc_t. rewrite Hsome in Hsc_t. injection Hsc_t as <-.
      iDestruct ("Hpubl" $! sc Hsome) as (sc_s) "[%Hsc_s Hscr]".
      iExists sc_s. iSplitR; last done.
      iPureIntro.
      destruct (free_mem_lookup_case l' l n σ_s.(shp)) as [[_ Heq'] | (i' & Hi' & -> & _)].
      2: { specialize (Hi i' Hi'). congruence. }
      rewrite Heq' Hsc_s. done.
    + iRight. iPureIntro. exists t'.
      destruct Hprivl as (tk & Htk & (s & Hs) & Hpriv). exists tk. split_and!; [done | | done].
      exists s. apply lookup_difference_Some. split; first done.
      destruct (decide (t = t')) as [<- | Hneq]; last by apply array_tag_map_lookup_None.
      apply array_tag_map_lookup_None'. intros i Hi'. rewrite Hlen_t in Hi'.
      specialize (Hi i Hi'); done.
  }
  iSplitL.
  { (* call interp *)
    (* TODO: duplicated with the refl lemma *)
    iPureIntro. iIntros (c M' Hc).
    destruct (Hcall_interp c M' Hc) as (? & HM'). split; first done.
    intros t' L Ht'. specialize (HM' t' L Ht') as (? & HL). split; first done.
    intros l' (stk & pm & Hstk & Hit & Hpm)%HL. exists stk, pm. split_and!; [ | done..].
    destruct (for_each_true_lookup_case_2 _ _ _ _ _ Hstack_t) as [EQ1 EQ2].
    (* from Hstack_s, l cannot be in the affected range because it is protected by c,
      so α' !! l = σt.(sst) !! l. *)
    destruct (block_case l l' n) as [Hneq|(i & Hi & ->)].
    + rewrite EQ2//.
    + exfalso. clear EQ2.
      specialize (EQ1 _ Hi) as (stk1 & stk' & Eqstk1 & Eqstk' & Hdealloc).
      rewrite Eqstk1 in Hstk. simplify_eq.
      move : Hdealloc. destruct (dealloc1 stk (Tagged t) σ_t.(scs)) eqn:Eqd; last done.
      intros _.
      destruct (dealloc1_Some stk (Tagged t) σ_t.(scs)) as (it & Eqit & ? & FA & GR).
      { by eexists. }
      rewrite ->Forall_forall in FA. apply (FA _ Hit).
      rewrite /is_active_protector /= /is_active bool_decide_true //.
  }
  iSplitL.
  { (* tag interp *)
    destruct Htag_interp as (Htag_interp & Hdom_t & Hdom_s).
    iPureIntro. split_and!.
    { intros t' tk Ht. simpl. specialize (Htag_interp _ _ Ht) as (? & ? & Hcontrol_t & Hcontrol_s & Hag).
      split_and!; [done | done | | | ].
      + intros l' sc_t.
        rewrite lookup_difference_Some. intros [Hsc_t%Hcontrol_t Hnotin%array_tag_map_lookup_None2].
        eapply loc_controlled_dealloc_update; [ apply Hstack_t | done | | done].
        intros [[= <-] (i & -> & Hi)].
        destruct Hnotin as [? | Hi']; first congruence.
        rewrite Hlen_t in Hi'. apply Hi' in Hi. congruence.
      + intros l' sc_s.
        rewrite lookup_difference_Some. intros [Hsc_t%Hcontrol_s Hnotin%array_tag_map_lookup_None2].
        eapply loc_controlled_dealloc_update; [ apply Hstack_s | done | | done].
        intros [[= <-] (i & -> & Hi)].
        destruct Hnotin as [? | Hi']; first congruence.
        rewrite Hlen_s in Hi'. apply Hi' in Hi. congruence.
      + apply dom_agree_on_tag_difference; first done.
        destruct (decide (t = t')) as [<- | Hneq].
        * apply dom_agree_on_tag_array_tag_map. lia.
        * apply dom_agree_on_tag_not_elem; apply array_tag_map_lookup_None; done.
    }
    all: intros t' l'; rewrite lookup_difference_is_Some; intros [? _]; eauto.
  }
  eauto.
Qed.

Lemma sim_free_local l t T v_t v_s Φ π :
  length v_t = tsize T →
  length v_s = tsize T →
  t $$ tk_local -∗
  l ↦t∗[tk_local]{t} v_t -∗
  l ↦s∗[tk_local]{t} v_s -∗
  (t $$ tk_local -∗ #[☠] ⪯{π} #[☠] [{ Φ }]) -∗
  Free (Place l (Tagged t) T) ⪯{π} Free (Place l (Tagged t) T) [{ Φ }].
Proof.
  iIntros (Hlen_t Hlen_s) "Htag Ht Hs Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hbor) %Hsafe]".
  destruct Hsafe as [Hthread Hsafe].
  specialize (pool_safe_implies Hsafe Hthread) as (Hmem_s & (α' & Hstack_s)).

  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iModIntro.
  iSplitR.
  { iPureIntro. eexists _, _, _. eapply dealloc_base_step'; first apply Hwf_t.
    - intros i. rewrite -Hmem_s. rewrite -!elem_of_dom Hdom_eq. done.
    - erewrite <-Hstack_s. rewrite Hsst_eq Hscs_eq. done.
  }
  iIntros (e_t' efs_t σ_t' Hhead_t).
  specialize (head_free_inv _ _ _ _ _ _ _ _ Hhead_t) as (α'_t & Hstack_t & Hmem_t & -> & -> & ->).
  assert (α'_t = α') as ->.
  { move : Hstack_t Hstack_s. rewrite Hsst_eq Hscs_eq => -> [= ->] //. }
  iMod (bor_interp_free_local with "Htag Ht Hs Hbor") as "[Htag Hbor]"; [done | done | done | done | ..].
  { eapply base_step_wf; done. }
  { eapply base_step_wf; [eapply (dealloc_base_step' P_s); done | done ]. }
  iModIntro. iExists _, _, _.
  iSplitR. { iPureIntro. eapply dealloc_base_step'; done. }
  iFrame. iSplitL; last done. by iApply "Hsim".
Qed.
*)


End lifting.
