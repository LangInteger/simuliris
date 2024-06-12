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

Definition filter_unq_weak lp := match lp with 
    Deallocable => Deallocable
  | EnsuringAccess Strongly => EnsuringAccess Strongly
  | EnsuringAccess WeaklyNoChildren => Deallocable end.
(*
TODO: this does not work because the invariant does not assert that no two calls can protect the same tag
Lemma sim_make_unique_public l t ac (sc_s sc_t : list scalar) π Φ e_t e_s c M L:
  l ↦t∗[tk_unq ac]{t} sc_t -∗
  l ↦s∗[tk_unq ac]{t} sc_s -∗
  t $$ tk_unq ac -∗
  c @@ M ∗ ⌜M !! t = Some L ∧ L ≠ ∅⌝ -∗ (* TODO: L ≠ ∅ is required because things are, again set up per-offset sometimes but not always *)
  value_rel sc_t sc_s -∗
  (t $$ tk_pub -∗ c @@ <[t := fmap filter_unq_weak L]> M -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }] .
Proof.
  iIntros "Ht Hs Htk (Hprot&%HL) #Hrel Hres".
  iApply sim_update_si. rewrite /update_si. iIntros (?????) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hstrs_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htk") as "%Ht_tk".
  iAssert (|==> tkmap_auth tag_name 1 (<[ t := (tk_pub, ()) ]> M_tag) ∗ t $$ tk_pub)%I with "[Htag_auth Htk]" as ">(Htag_auth&Htk)".
  { iMod (tkmap_update_strong tk_pub tt with "Htag_auth Htk") as "($&$)"; done. }
  iPoseProof (ghost_map_lookup with "Htag_t_auth Ht") as "%Hhl_t".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hhl_s".
  iMod (ghost_map_update ∅ with "Htag_t_auth Ht") as "(Htag_t_auth&_)".
  iMod (ghost_map_update ∅ with "Htag_s_auth Hs") as "(Htag_s_auth&_)".
  iPoseProof (ghost_map_lookup with "Hc Hprot") as "%Hprot".
  iMod (ghost_map_update (<[t:=filter_unq_weak <$> L]> M) with "Hc Hprot") as "(Hc&Hprot)".
  iAssert (⌜length sc_t = length sc_s⌝)%I as "%Hlen". 1: by iApply big_sepL2_length.

  iModIntro. iSplitR "Hres Htk Hprot".
  2: by iApply ("Hres" with "Htk Hprot").
  iFrame "HP_s HP_t". iExists (<[c := _ ]> M_call), _, (<[(t, l.1):=∅]> M_t), (<[(t, l.1):=∅]> M_s).
  iFrame "Hc Htag_t_auth Htag_s_auth Hpub_cid Htag_auth".
  iSplit; last (iPureIntro; split; last (split; last done)).
  - repeat (iSplit; first done). iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
    iIntros (ll Hll). iDestruct ("Hsrel" $! ll Hll) as "[Hpub|(%tt&%Hpriv)]".
    1: by iLeft.
    destruct (decide (t = tt)) as [->|Hne].
    2: { iRight. iPureIntro. exists tt.
         rewrite /priv_loc lookup_insert_ne //.
         rewrite /heaplet_lookup lookup_insert_ne //. 2: simpl; by congruence.
         destruct Hpriv as (tk&H1&H2&H3). exists tk. split; first done. split; first done.
         destruct H3 as [H3|(c'&ae'&H3A&H3B)]. 1: by left.
         right. exists c', ae'. split; first done.
         destruct H3B as (MM&HMM&H3B).
         destruct (decide (c = c')) as [->|Hne'].
         2: exists MM; split; last done; rewrite lookup_insert_ne //.
         assert (M = MM) as -> by congruence.
         eexists. rewrite lookup_insert. split; first done.
         destruct H3B as (LL&HLL&H3B). exists LL.
         rewrite lookup_insert_ne //. }
    iLeft. rewrite /pub_loc. iIntros (sc_t' Hsc_t').
    destruct Hpriv as (x&Htk'&Hheaplet&Hx). assert (x = tk_unq ac) as -> by congruence.
    destruct Htag_interp as (Ht1&Ht2&Ht3&Ht4&Ht5).
    destruct Hheaplet as (sc_ll&(hl_t'&Hheaplet_t1&Hheaplet_t2)%bind_Some).
    simpl in Hheaplet_t1.
    assert (l.1 = ll.1) as Hlleq.
    { eapply Ht4. all: by eapply elem_of_dom_2. } rewrite /= -Hlleq Hhl_t in Hheaplet_t1.
    injection Hheaplet_t1 as <-. simpl in Hheaplet_t2.
    specialize (Ht1 _ _ Htk') as (HHt1&HHt2&HHt3&HHt4&HHt5).
    ospecialize (HHt3 ll _ _).
    1: rewrite /heaplet_lookup /= -Hlleq Hhl_t /= Hheaplet_t2 //.
    assert (∃ sc_ll_s, list_to_heaplet sc_s l.2 !! ll.2 = Some sc_ll_s) as (sc_ll_s&Hsc_ll_s).
    { eapply elem_of_dom. erewrite list_to_heaplet_dom_1. 2: symmetry; eapply Hlen. eapply elem_of_dom_2. eapply Hheaplet_t2. }
    assert (∃ (i:nat), ll.2 = l.2 + i) as (i&Hoff).
    { eapply list_to_heaplet_lookup_Some in Hsc_ll_s. exists (Z.to_nat (ll.2 - l.2)). lia. }
    rewrite Hoff in Hsc_ll_s Hheaplet_t2.

    destruct HHt3 as (_&HHt3).
    { destruct Hx as [->|(c'&ae&->&Hcs)]. 1: done.
      opose proof* (call_set_interp_access) as Hacc. 1: done. 1: exact Hcs.
      destruct Hacc as (Hc&Hv&it&Hit&Hprot1&Hprot2&Hprot3&Hprot4).
      exists it. split; first done. split; first done.
      intros _ _. exists c'. split; done. }
    specialize (HHt4 ll sc_ll_s).
    destruct HHt4 as (_&HHt4).
    1: rewrite /heaplet_lookup /= -Hlleq Hhl_s /= Hoff //.
    { destruct Hx as [->|(c'&ae&->&Hcs)]. 1: done.
      opose proof* (call_set_interp_access) as Hacc. 1: done. 1: exact Hcs.
      destruct Hacc as (Hc&Hv&it&Hit&Hprot1&Hprot2&Hprot3&Hprot4).
      odestruct trees_equal_find_equal_tag_protected_initialized_not_disabled as (it2&HH1&HH2&HH3).
      1: by eapply trees_equal_sym. 2: exact Hprot4. 2: exists c'; by rewrite Hscs_eq.
      1: done.
      exists it2. split; first done. split; first done.
      intros _ _. apply HH3. }
    iExists sc_ll_s. iSplit; first done.
    assert (sc_ll = sc_t') as <- by congruence.
    rewrite !list_to_heaplet_nth in Hsc_ll_s Hheaplet_t2.
    iPoseProof (big_sepL2_lookup_acc with "Hrel") as "($&_)".
    all: done.
  - intros c' M' [(<-&<-)|(Hne&HM')]%lookup_insert_Some.
    + admit.
    + specialize (Hcall_interp _ _ HM') as (H1&H2). split; first done.
      intros tg' L' HL'. specialize (H2 _ _ HL') as (H2&H3). split; first done.
      intros l' ps Hps. specialize (H3 _ _ Hps).
      eapply tag_protected_for_mono. 2: exact H3.
      intros [blk off] it Hlu Hiscall Hinit (tkp&Htag&Hheap).
      exists tkp. Print call_set_interp. Print tag_protected_for.
      assert (itag it ≠ t) as Hne2.
      2: rewrite /heaplet_lookup !lookup_insert_ne /= //. 2: by intros [= ??].
      intros <-.
  - destruct Htag_interp as (H1&H2&H3&H4&H5). split_and!.
    + intros tg tk' [(->&[= <-])|(Hne&Hin)]%lookup_insert_Some; last first.
      * specialize (H1 _ _ Hin) as (HH1&HH2&HH3&HH4&HH5). split_and!.
        1-2: done.
        3: { rewrite /dom_agree_on_tag /heaplet_lookup /= //.
             split; intros ?; rewrite !lookup_insert_ne; try congruence.
             all: eapply HH5. }
        { intros l' sc' H. rewrite /heaplet_lookup /= !lookup_insert_ne // in H. 2: congruence. 
          by eapply HH3. }
        { intros l' sc' H. rewrite /heaplet_lookup /= !lookup_insert_ne // in H. 2: congruence. 
          by eapply HH4. }
      * specialize (H1 _ _ Ht_tk) as (HH1&HH2&HH3&HH4&HH5). split_and!.
        1-2: done.
        3: { eapply dom_agree_on_tag_update_same. all: done. }
        all: intros ??; rewrite /= /heaplet_lookup /=.
        all: intros (x&[(?&<-)|(Hne&Hin)]%lookup_insert_Some&Hy)%bind_Some;
          [rewrite lookup_empty // in Hy| ].
        all: exfalso.
        { ospecialize* H4. 1-2: eapply elem_of_dom_2. 1: exact Hin. 1: exact Hhl_t. congruence. }
        { ospecialize* H5. 1-2: eapply elem_of_dom_2. 1: exact Hin. 1: exact Hhl_s. congruence. }
    + intros t' blk H%elem_of_dom. rewrite dom_insert_lookup_L in H. 2: by eexists.
      eapply elem_of_dom. rewrite dom_insert_lookup_L. 2: by eexists.
      by eapply elem_of_dom, H2, elem_of_dom.
    + intros t' blk H%elem_of_dom. rewrite dom_insert_lookup_L in H. 2: by eexists.
      eapply elem_of_dom. rewrite dom_insert_lookup_L. 2: by eexists.
      by eapply elem_of_dom, H3, elem_of_dom.
    + intros tg blk1 blk2. rewrite !dom_insert_lookup_L. 2: by eexists.
      by eapply H4.
    + intros tg blk1 blk2. rewrite !dom_insert_lookup_L. 2: by eexists.
      by eapply H5.
Admitted.
*)

Lemma sim_make_local_public l t (sc_s sc_t : list scalar) π Φ e_t e_s:
  l ↦t∗[tk_local]{t} sc_t -∗
  l ↦s∗[tk_local]{t} sc_s -∗
  t $$ tk_local -∗
  value_rel sc_t sc_s -∗
  (t $$ tk_pub -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }] .
Proof.
  iIntros "Ht Hs Htk #Hrel Hres".
  iApply sim_update_si. rewrite /update_si. iIntros (?????) "(HP_t & HP_s & Hbor)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hsst_eq & Hstrs_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & Hbor)".
  iDestruct "Hbor" as "((Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _)".
  iPoseProof (tkmap_lookup with "Htag_auth Htk") as "%Ht_tk".
  iAssert (|==> tkmap_auth tag_name 1 (<[ t := (tk_pub, ()) ]> M_tag) ∗ t $$ tk_pub)%I with "[Htag_auth Htk]" as ">(Htag_auth&Htk)".
  { iMod (tkmap_update_strong tk_pub tt with "Htag_auth Htk") as "($&$)"; done. }
  iPoseProof (ghost_map_lookup with "Htag_t_auth Ht") as "%Hhl_t".
  iPoseProof (ghost_map_lookup with "Htag_s_auth Hs") as "%Hhl_s".
  iMod (ghost_map_update ∅ with "Htag_t_auth Ht") as "(Htag_t_auth&_)".
  iMod (ghost_map_update ∅ with "Htag_s_auth Hs") as "(Htag_s_auth&_)".
  iAssert (⌜length sc_t = length sc_s⌝)%I as "%Hlen". 1: by iApply big_sepL2_length.

  iModIntro. iSplitR "Hres Htk".
  2: by iApply "Hres".
  iFrame "HP_s HP_t". iExists M_call, _, (<[(t, l.1):=∅]> M_t), (<[(t, l.1):=∅]> M_s).
  iFrame "Hc Htag_t_auth Htag_s_auth Hpub_cid Htag_auth".
  iSplit; last (iPureIntro; split; last (split; last done)).
  - repeat (iSplit; first done). iDestruct "Hsrel" as "(_&_&_&_&_&Hsrel)".
    iIntros (ll Hll). iDestruct ("Hsrel" $! ll Hll) as "[Hpub|(%tt&%Hpriv)]".
    1: by iLeft.
    destruct (decide (t = tt)) as [->|Hne].
    2: { iRight. iPureIntro. exists tt.
         rewrite /priv_loc lookup_insert_ne //.
         rewrite /heaplet_lookup lookup_insert_ne //. simpl. by congruence. }
    iLeft. rewrite /pub_loc. iIntros (sc_t' Hsc_t').
    destruct Hpriv as (x&Htk'&Hheaplet&Hx). assert (x = tk_local) as -> by congruence.
    destruct Htag_interp as (Ht1&Ht2&Ht3&Ht4&Ht5).
    destruct Hheaplet as (sc_ll&(hl_t'&Hheaplet_t1&Hheaplet_t2)%bind_Some).
    simpl in Hheaplet_t1.
    assert (l.1 = ll.1) as Hlleq.
    { eapply Ht4. all: by eapply elem_of_dom_2. } rewrite /= -Hlleq Hhl_t in Hheaplet_t1.
    injection Hheaplet_t1 as <-. simpl in Hheaplet_t2.
    specialize (Ht1 _ _ Htk') as (HHt1&HHt2&HHt3&HHt4&HHt5).
    ospecialize (HHt3 ll _ _).
    1: rewrite /heaplet_lookup /= -Hlleq Hhl_t /= Hheaplet_t2 //.
    assert (∃ sc_ll_s, list_to_heaplet sc_s l.2 !! ll.2 = Some sc_ll_s) as (sc_ll_s&Hsc_ll_s).
    { eapply elem_of_dom. erewrite list_to_heaplet_dom_1. 2: symmetry; eapply Hlen. eapply elem_of_dom_2. eapply Hheaplet_t2. }
    assert (∃ (i:nat), ll.2 = l.2 + i) as (i&Hoff).
    { eapply list_to_heaplet_lookup_Some in Hsc_ll_s. exists (Z.to_nat (ll.2 - l.2)). lia. }
    rewrite Hoff in Hsc_ll_s Hheaplet_t2.

    destruct HHt3 as (_&HHt3).
    { destruct Hx as [|(c&ae&Heq&Hcs)]. 1: done. exfalso. congruence. }
    specialize (HHt4 ll sc_ll_s).
    destruct HHt4 as (_&HHt4).
    1: rewrite /heaplet_lookup /= -Hlleq Hhl_s /= Hoff //.
    { destruct Hx as [|(c&ae&Heq&Hcs)]. 1: done. exfalso. congruence. }
    iExists sc_ll_s. iSplit; first done.
    assert (sc_ll = sc_t') as <- by congruence.
    rewrite !list_to_heaplet_nth in Hsc_ll_s Hheaplet_t2.
    iPoseProof (big_sepL2_lookup_acc with "Hrel") as "($&_)".
    all: done.
  - intros c M' HM'. specialize (Hcall_interp _ _ HM') as (H1&H2). split; first done.
    intros tg' L HL. specialize (H2 _ _ HL) as (H2&H3). split; first done.
    intros l' ps Hps. specialize (H3 _ _ Hps).
    eapply tag_protected_for_mono. 2: exact H3.
    intros [blk off] it Hlu Hiscall Hinit (tkp&Htag&Hheap).
    exists tkp. assert (itag it ≠ t) as Hne.
    { intros <-. congruence. }
    rewrite lookup_insert_ne //. split; first done.
    rewrite /heaplet_lookup lookup_insert_ne /= //.
    intros [= ??]; done.
  - destruct Htag_interp as (H1&H2&H3&H4&H5). split_and!.
    + intros tg tk' [(->&[= <-])|(Hne&Hin)]%lookup_insert_Some; last first.
      * specialize (H1 _ _ Hin) as (HH1&HH2&HH3&HH4&HH5). split_and!.
        1-2: done.
        3: { rewrite /dom_agree_on_tag /heaplet_lookup /= //.
             split; intros ?; rewrite !lookup_insert_ne; try congruence.
             all: eapply HH5. }
        { intros l' sc' H. rewrite /heaplet_lookup /= !lookup_insert_ne // in H. 2: congruence. 
          by eapply HH3. }
        { intros l' sc' H. rewrite /heaplet_lookup /= !lookup_insert_ne // in H. 2: congruence. 
          by eapply HH4. }
      * specialize (H1 _ _ Ht_tk) as (HH1&HH2&HH3&HH4&HH5). split_and!.
        1-2: done.
        3: { eapply dom_agree_on_tag_update_same. all: done. }
        all: intros ??; rewrite /= /heaplet_lookup /=.
        all: intros (x&[(?&<-)|(Hne&Hin)]%lookup_insert_Some&Hy)%bind_Some;
          [rewrite lookup_empty // in Hy| ].
        all: exfalso.
        { ospecialize* H4. 1-2: eapply elem_of_dom_2. 1: exact Hin. 1: exact Hhl_t. congruence. }
        { ospecialize* H5. 1-2: eapply elem_of_dom_2. 1: exact Hin. 1: exact Hhl_s. congruence. }
    + intros t' blk H%elem_of_dom. rewrite dom_insert_lookup_L in H. 2: by eexists.
      eapply elem_of_dom. rewrite dom_insert_lookup_L. 2: by eexists.
      by eapply elem_of_dom, H2, elem_of_dom.
    + intros t' blk H%elem_of_dom. rewrite dom_insert_lookup_L in H. 2: by eexists.
      eapply elem_of_dom. rewrite dom_insert_lookup_L. 2: by eexists.
      by eapply elem_of_dom, H3, elem_of_dom.
    + intros tg blk1 blk2. rewrite !dom_insert_lookup_L. 2: by eexists.
      by eapply H4.
    + intros tg blk1 blk2. rewrite !dom_insert_lookup_L. 2: by eexists.
      by eapply H5.
Qed.
  

(*

Proof.
  iIntros (Hin HL) "Hc Htag Ht Hs Hrel Hsim".
  iApply (sim_protected_unprotectN M L l c t tk [sc_t] [sc_s] with "Hc Htag [Ht] [Hs] [Hrel] [Hsim]").
  - simpl. intros i Hi. replace i with O by lia. rewrite shift_loc_0_nat. done.
  - done.
  - iApply big_sepL_singleton. rewrite shift_loc_0_nat. done.
  - iApply big_sepL_singleton. rewrite shift_loc_0_nat. done.
  - iApply big_sepL2_singleton. done.
  - simpl. rewrite shift_loc_0_nat union_empty_r_L.
    rewrite /array_tag !big_sepL_singleton !shift_loc_0_nat. done.
Qed.

Lemma sim_remove_empty_calls t L M c e_t e_s π Φ :
  M !! t = Some L →
  L = ∅ →
  c @@ M -∗
  (c @@ (delete t M) -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }].
Proof.
  iIntros (Ht ->) "Hc Hsim".
  iApply sim_update_si. rewrite /update_si. iIntros (?????) "(HP_t & HP_s & Hbor)".
  set (M' := delete t M).
  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hcall_auth & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iPoseProof (ghost_map_lookup with "Hcall_auth Hc") as "%HcM".
  iMod (ghost_map_update M' with "Hcall_auth Hc") as "[Hcall_auth Hc]".
  iModIntro. iFrame "HP_t HP_s". iSplitR "Hsim Hc"; last by iApply ("Hsim" with "Hc").
  iExists (<[ c := M' ]> M_call), M_tag, M_t, M_s. iFrame.
  iSplitL "Hsrel".
  { iDestruct "Hsrel" as "(%Hdom_eq & %Hsst_eq & %Hsnp_eq & %Hsnc_eq & %Hscs_eq & Hloc)".
    do 5 (iSplitR; first done).
    iIntros (l' Hl'). iDestruct ("Hloc" $! l' with "[//]") as "[Hpub | %Hpriv]"; first by iLeft.
    iRight. iPureIntro. destruct Hpriv as (t' & tk' & Htk' & Hsome & Hpriv).
    exists t', tk'. split; first done. split; first done.
    destruct Hpriv as [-> | [-> Hpriv]]; first by left. right; split; first done.
    destruct Hpriv as (c' & M'' & Hc' & Hin').
    destruct (decide (c' = c)) as [-> | Hneq]; first last.
    { exists c', M''. rewrite lookup_insert_ne; done. }
    exists c, M'. rewrite lookup_insert. split; first done.
    destruct (decide (t' = t)) as [-> | Hneq']; first last.
    { destruct Hin' as (L'' & HL'' & Hl''). exists L''. split; last done.
      simplify_eq. rewrite lookup_delete_ne; done.
    }
    exfalso. destruct Hin' as (L'' & HL'' & Hl''). simplify_eq. done.
  }
  iSplitL; last done.
  iPureIntro. intros c' M''. rewrite lookup_insert_Some. intros [[<- <-] | [Hneq Hsome]].
  - apply Hcall_interp in HcM as [Hc HcM]. split; first done.
    intros t' L''. subst M'. rewrite lookup_delete_Some. intros [Hneq' Hsome']. naive_solver.
  - apply Hcall_interp in Hsome as [Hc' Hsome]. done.
Qed.
*)



(** operational lemmas for calls *)
Lemma target_red_call f arg body v Ψ :
  f @t (arg, body) -∗
  target_red (subst arg #v body) Ψ -∗
  target_red (Call #[ScFnPtr f] #v) Ψ. 
Proof.
  iIntros "Hf Hred". iApply target_red_lift_base_step.
  iIntros (?????) "(HP_t & HP_s & ?) !>".
  iDestruct (has_prog_has_fun_agree with "HP_t Hf") as %?.
  iSplitR. { iPureIntro. eexists _, _, _. econstructor. econstructor; first done. eauto. }
  iIntros (e_t' efs σ_t') "%"; inv_base_step.
  iModIntro. by iFrame.
Qed.

Lemma source_red_call π f arg body v Ψ :
  f @s (arg, body) -∗
  source_red (subst arg #v body) π Ψ -∗
  source_red (Call #[ScFnPtr f] #v) π Ψ.
Proof.
  iIntros "Hf Hred". iApply source_red_lift_base_step.
  iIntros (??????) "[(HP_t & HP_s & ?) [% %]] !>".
  iDestruct (has_prog_has_fun_agree with "HP_s Hf") as %?.
  iExists _, _. iSplit. { iPureIntro. econstructor. econstructor; first done. eauto. }
  iModIntro. iFrame.
Qed.

End lifting.
