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




(** ** Retags *)

Definition pointer_kind_to_tag_unprotected (pk : pointer_kind) : option tag_kind := match pk with
  Box im | MutRef im => match im with TyFrz => Some (tk_unq tk_res) | _ => None end (* can not have unprotected IM pointers around *)
| ShrRef => Some tk_pub end.
Definition pointer_kind_to_tag_protected (pk : pointer_kind) : tag_kind := match pk with
  Box _ | MutRef _ => tk_unq tk_res (* for protected, IM is not an issue *)
| ShrRef => tk_pub end.

(** *** Retags without protectors *)


(*
Lemma bor_interp_retag_default σ_t σ_s c l ot T α' mut :
  let pk : pointer_kind := RefPtr mut in
  let pm := match mut with Mutable => Unique | Immutable => SharedReadOnly end in
  let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
  retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l ot Default pk T = Some (Tagged σ_s.(snp), α', S σ_s.(snp)) →
  c ∈ σ_s.(scs) →
  (if mut is Immutable then is_freeze T else True) →
  state_wf (mkState σ_t.(shp) α' σ_t.(scs) (S σ_t.(snp)) σ_t.(snc)) →   (* could remove that assumption *)
  state_wf (mkState σ_s.(shp) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)) →   (* could remove that assumption *)
  sc_rel (ScPtr l ot) (ScPtr l ot) -∗
  bor_interp sc_rel σ_t σ_s ==∗ ∃ v_t v_s,
  ⌜length v_t = tsize T⌝ ∗
  ⌜length v_s = tsize T⌝ ∗
  value_rel v_t v_s ∗
  σ_t.(snp) $$ tk ∗
  l ↦t∗[tk]{σ_t.(snp)} v_t ∗
  l ↦s∗[tk]{σ_t.(snp)} v_s ∗
  match mut with
  | Mutable => True
  | Immutable =>
    sc_rel (ScPtr l (Tagged (σ_t.(snp)))) (ScPtr l (Tagged (σ_t.(snp))))
  end ∗
  bor_interp sc_rel (mkState σ_t.(shp) α' σ_t.(scs) (S σ_t.(snp)) σ_t.(snc)) (mkState σ_s.(shp) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)).
Proof.
  intros pk pm tk Hretag Hc_in Hfreeze Hwf'_t Hwf'_s.
  iIntros "Hscrel Hbor". iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".

  iDestruct "Hscrel" as "[_ Hrel]".
  iAssert (⌜untagged_or_public M_tag ot⌝)%I as %Hpub.
  { iDestruct "Hrel" as "[[-> _] | (%t1 & %t2 & -> & -> & <- & Hpub)]"; first done.
    iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%". done.
  }
  pose nt := (snp σ_t).

  have Hin_dom := retag_Some_dom _ _ _ _ _ _ _ pk _ _ _ _ I Hretag.
  iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom_eq".
  destruct (read_mem_is_Some l (tsize T) σ_s.(shp)) as [v_s Hv_s].
  { setoid_rewrite (state_wf_dom _ Hwf_s). done. }
  destruct (read_mem_is_Some l (tsize T) σ_t.(shp)) as [v_t Hv_t].
  { rewrite Hdom_eq. setoid_rewrite (state_wf_dom _ Hwf_s). done. }
  destruct (read_mem_values _ _ _ _ Hv_s) as [Hlen_s Hshp_s].
  destruct (read_mem_values _ _ _ _ Hv_t) as [Hlen_t Hshp_t].

  (* allocate resources *)
  assert (M_tag !! nt = None) as Htag_none.
  { destruct (M_tag !! nt) as [[tk' []] | ] eqn:Ht_some; last done.
    apply Htag_interp in Ht_some as [Hcontra _]. lia. }
  destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
  iMod (tkmap_insert tk _ tt Htag_none with "Htag_auth") as "[Htag_auth Hnt]".
  iMod (ghost_map_array_tag_insert _ _ v_t nt l with "Htag_t_auth") as "[Ht Htag_t_auth]".
  { intros i Hi. destruct (M_t !! (nt, l +ₗ i)) eqn:Hmt; last done.
    destruct (Ht_dom nt (l +ₗ i) ltac:(eauto)) as (? & ?); congruence. }
  iMod (ghost_map_array_tag_insert _ _ v_s nt l with "Htag_s_auth") as "[Hs Htag_s_auth]".
  { intros i Hi. destruct (M_s !! (nt, l +ₗ i)) eqn:Hmt; last done.
    destruct (Hs_dom nt (l +ₗ i) ltac:(eauto)) as (? & ?); congruence. }
  iMod (ghost_map_array_tag_tk _ _ _ _ tk with "Ht") as "Ht".
  iMod (ghost_map_array_tag_tk _ _ _ _ tk with "Hs") as "Hs".
  iModIntro.
  iAssert (nt $$ tk ∗ if tk is tk_pub then nt $$ tk_pub else True)%I  with "[Hnt]" as "[$ Hpubt]".
  { destruct tk; eauto. }
  iExists v_t, v_s. iSplit; first done. iSplit; first done. iFrame "Ht Hs".

  iAssert (⌜retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l ot Default pk T = Some (Tagged nt, α', S (σ_t.(snp)))⌝)%I as "%Hretag_t".
  { iPoseProof (state_rel_calls_eq with "Hsrel") as "<-".
    iPoseProof (state_rel_stacks_eq with "Hsrel") as "<-".
    subst nt. iPoseProof (state_rel_snp_eq with "Hsrel") as "<-". done. }
  (* proving the value relation *)
  iAssert (value_rel v_t v_s)%I as "#Hvrel"; last iFrame "Hvrel".
  { iApply big_sepL2_forall; iSplit; first (iPureIntro;lia).
    iIntros (i sc_t sc_s) "%Hs_t %Hs_v".
    assert (i < tsize T)%nat as Hi. { rewrite -Hlen_t. eapply lookup_lt_is_Some_1. eauto. }
    assert (Hsome_target : is_Some (σ_t.(shp) !! (l +ₗ i))).
    { rewrite Hshp_t; last done. apply lookup_lt_is_Some_2. by rewrite Hlen_t. }
    iPoseProof (state_rel_pub_if_not_priv _ _ _ _ _ _ (l +ₗ i) with "[] Hsrel [Hrel]") as "Hpub"; first done.
    { iPoseProof (state_rel_calls_eq with "Hsrel") as "%Hcall_eq".
      iPoseProof (state_rel_stacks_eq with "Hsrel") as "%Hstack_eq".
      iPureIntro. intros t Hpriv.
      eapply (priv_loc_UB_retag_access_eq σ_s σ_t); eauto; done. }
    iPoseProof (pub_loc_lookup with "[] Hpub") as "(%sc_t' & %sc_s' & %Hread_both & Hsc_rel)"; first done.
    enough (sc_t = sc_t' ∧ sc_s = sc_s') by naive_solver.
    move : Hs_t Hs_v Hread_both (Hshp_s i Hi) (Hshp_t i Hi).
    by move => -> -> [-> ->] [= ->] [= ->].
  }

  iSplitL "Hpubt".
  { destruct mut; first done. iSplitR; first done. iRight.
    iExists (σ_t.(snp)), (σ_t.(snp)). do 3 (iSplitR; first done). done. }

  (* re-establishing the interpretation *)
  iExists M_call, (<[ nt := (tk, ()) ]> M_tag), (array_tag_map l nt v_t ∪ M_t), (array_tag_map l nt v_s ∪ M_s).
  iFrame. iSplitL "Htainted".
  { (* tainted *) iApply (tag_tainted_interp_retag with "Htainted"); done. }
  iSplitL.
  { (* state relation *)
    rewrite /state_rel. simpl. iDestruct "Hsrel" as "(-> & %Hs_eq & -> & -> & -> & Hsrel)".
    do 5 (iSplitL; first done). iIntros (l' Hsl').
    iDestruct ("Hsrel" $! l' with "[//]") as "[Hpub | [%t' %Hpriv]]"; first (iLeft; iApply "Hpub").
    iRight. iPureIntro. exists t'.
    destruct Hpriv as (tk' & Hsome_tk' & Ht_l' & Htk'). exists tk'.
    assert (t' ≠ nt). { intros ->. simplify_eq. }
    rewrite lookup_insert_ne; last done.
    split; first done. split; last done.
    destruct Ht_l' as (sc0 & Ht_l'). exists sc0.
    rewrite lookup_union_r; first done.
    destruct (array_tag_map l nt v_t !! (t', l')) as [ a | ] eqn:Harr; last done.
    specialize (array_tag_map_lookup1 l nt v_t t' l' ltac:(eauto)) as [Heq _]. congruence.
  }
  iSplitL.
  { (* call interpretation. *)
    iPureIntro. intros c' M' [Hc' HM']%Hcall_interp. split; first done.
    intros t' S HS. simpl. specialize (HM' t' S HS) as (Ht' & Hprot).
    split; first lia. intros l' Hl'.
    specialize (Hprot l' Hl') as (s & pm' & Hs & Hit & Hpm').
    specialize (retag_item_active_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag_t l' s (Tagged t') c' pm' Hs Hc' Hit) as (s' & -> & Hin'). eauto.
  }
  iSplitL.
  { (* tag interpretation. *)
    iPoseProof (state_rel_get_pure with "Hsrel") as "%Hp".
    destruct Hp as (Hsst & Hsnp & Hsnc & Hscs).
    assert (∀l', M_t !! (nt, l') = None) as HMt_nt.
    { intros l'. destruct (M_t !! (nt, l')) eqn:HM_t; last done.
      specialize (Ht_dom nt l' ltac:(eauto)) as (? & ?); congruence. }
    assert (∀l', M_s !! (nt, l') = None) as HMs_nt.
    { intros l'. destruct (M_s !! (nt, l')) eqn:HM_s; last done.
      specialize (Hs_dom nt l' ltac:(eauto)) as (? & ?); congruence. }
    iPureIntro. split_and!.
    { intros t tk'. rewrite lookup_insert_Some. intros [[<- [= <-]] | [Hneq Hsome_t]].
      - cbn. split_and!; [lia | lia | | |].
        + intros l' sc_t Ha%lookup_union_Some_inv_l; last done.
          specialize (array_tag_map_lookup2 l nt v_t nt l' ltac:(eauto)) as [_ (i & Hi & ->)].
          eapply loc_controlled_retag_ref; [ done | done |  done | lia | ].
          move : Ha. rewrite array_tag_map_lookup_Some; last done. move => <-. apply Hshp_t. lia.
        + intros l' sc_s Ha%lookup_union_Some_inv_l; last done.
          specialize (array_tag_map_lookup2 l nt v_s nt l' ltac:(eauto)) as [_ (i & Hi & ->)].
          subst nt. rewrite -Hsnp. eapply loc_controlled_retag_ref; [ done | done | done | lia | ].
          move : Ha. rewrite array_tag_map_lookup_Some; last done. move => <-. apply Hshp_s. lia.
        + apply dom_agree_on_tag_union. { apply dom_agree_on_tag_array_tag_map. lia. }
          apply dom_agree_on_tag_not_elem; done.
      - cbn.
        specialize (Htag_interp t tk' Hsome_t) as (Ht_t & Ht_s & Hcontrolled_t & Hcontrolled_s & Hagree).
        split_and!; [ lia | lia | | | ].
        + intros l' sc_t Ha. rewrite lookup_union_r in Ha; last by apply array_tag_map_lookup_None.
          apply Hcontrolled_t in Ha.
          eapply loc_controlled_retag_update; [done | done | | done | done].
          intros <-. destruct tk'; [ done | | ]; move : Hsome_t Hpub; congruence.
        + intros l' sc_s Ha. rewrite lookup_union_r in Ha; last by apply array_tag_map_lookup_None.
          apply Hcontrolled_s in Ha.
          eapply loc_controlled_retag_update; [done | done | | done | done].
          intros <-. destruct tk'; [ done | | ]; move : Hsome_t Hpub; congruence.
        + apply dom_agree_on_tag_union; last done.
          apply dom_agree_on_tag_not_elem; apply array_tag_map_lookup_None; done.
    }
    { intros t l'.
      rewrite lookup_union_is_Some lookup_insert_is_Some'. intros [[-> _]%array_tag_map_lookup2 | H%Ht_dom]; eauto. }
    { intros t l'.
      rewrite lookup_union_is_Some lookup_insert_is_Some'. intros [[-> _]%array_tag_map_lookup2 | H%Hs_dom]; eauto. }
  }
  done.
Qed.
*)

Lemma sim_retag_default sz l_t l_s ot c pk tk π Φ :
  pointer_kind_to_tag_unprotected pk = Some tk → (* forbid interior mutability  *)
  sc_rel (ScPtr l_t ot) (ScPtr l_s ot) -∗
  (∀ nt v_t v_s,
    ⌜length v_t = sz⌝ -∗ ⌜length v_s = sz⌝ -∗
    value_rel v_t v_s -∗  (* as the pointers were public before *)
    nt $$ tk -∗
    l_t ↦t∗[tk]{nt} v_t -∗
    l_s ↦s∗[tk]{nt} v_s -∗
    #[ScPtr l_t nt] ⪯{π} #[ScPtr l_s nt] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] pk sz Default ⪯{π} Retag #[ScPtr l_s ot] #[ScCallId c] pk sz Default [{ Φ }].
Proof.
  intros Htk. iIntros "#Hscrel Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "((HP_t & HP_s & Hbor) & %Hthread & %Hsafe)".
  (* exploit source to gain knowledge about stacks & that c is a valid id *)
  specialize (pool_safe_implies Hsafe Hthread) as (c' & ot' & l' & trs1 & trs2 & [= <- <-] & [= <-] & Hcin & Hotin & Hntnin & Happly1_s & Happly2_s).
  iPoseProof "Hscrel" as "(-> & _ & Hotpub)". iClear "Hscrel".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  destruct Hp as (Hstrs_eq & Hsnp_eq & Hsnc_eq & Hscs_eq & Hwf_s & Hwf_t & Hdom_eq).
  odestruct (trees_equal_create_child _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstrs_eq Happly1_s) as (trs1_t&Happly1_t&Hstrs1_eq).
  1,3: eapply Hwf_s. 2: rewrite Hsnc_eq Hsnp_eq. 1,2: eapply Hwf_t. 1: by eapply Hwf_s.
  1-2: done.
  eapply retag_step_wf_inner in Hwf_s as X. 1: destruct X as (Hwf_mid_s&Hntinmid).
  2-5: done.
  eapply retag_step_wf_inner in Hwf_t as X. 1: destruct X as (Hwf_mid_t&_).
  5: by rewrite Hscs_eq Hsnp_eq in Happly1_t. 4: by rewrite -Hscs_eq. 2-3: setoid_rewrite <- trees_equal_same_tags; last done. 2: done. 2: by rewrite -Hsnp_eq.
  edestruct trees_equal_allows_same_access as (trs2_t&Happly2_t).
  1: exact Hstrs1_eq. 1: apply Hwf_mid_s. 1: apply Hwf_mid_t. 1: done. 1: by eapply mk_is_Some.
  opose proof (trees_equal_preserved_by_access _ _ Hstrs1_eq _ Happly2_s Happly2_t) as Hstrs2_eq.
  1: eapply Hwf_mid_s. 1: eapply Hwf_mid_t. 1: done.
  clear Hstrs1_eq Hwf_mid_s Hwf_mid_t Hntinmid. (* TODO refactor the above into a separate lemma, maybe? *)

  iModIntro. iSplit.
  { iPureIntro. do 3 eexists. econstructor; econstructor.
    1,3-5: repeat rewrite -?Hscs_eq -?Hsnp_eq //.
    all: setoid_rewrite <- trees_equal_same_tags; last done; done. }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  destruct (head_retag_inv _ _ _ _ _ _ _ _ _ _ _ Hhead_t) as (trsX1&trsX2&->&->&Hσ_t'&Hcin_t&Hotin_t&Hntnin_t&HX1&HX2).
  assert (trsX1 = trs1_t) as -> by congruence. clear HX1.
  assert (trsX2 = trs2_t) as -> by congruence. clear HX2.
  iModIntro. iExists _, _, _. iSplit.
  { iPureIntro. simpl. econstructor; econstructor. all: done. }

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & _ & _)".
  (*
  iDestruct 


  rewrite -Hsnp_eq.
  iFrame "HP_t HP_s". iSplitR "Hsim"; last first.
  { iSplit; last done. iApply "Hsim". *)
Admitted.
(*

(** *** Retags with protectors *)
Fixpoint seq_loc_set (l : loc) (n : nat) : gset loc :=
  match n with
  | O => ∅
  | S n => {[ l +ₗ n ]} ∪ seq_loc_set l n
  end.
Lemma seq_loc_set_elem l n l' :
  l' ∈ seq_loc_set l n ↔ (∃ (i : nat), (i < n)%nat ∧ l' = l +ₗ i).
Proof.
  induction n as [ | n IH]; simpl.
  - rewrite elem_of_empty. split; first done. intros (i & Hi & _). lia.
  - rewrite elem_of_union elem_of_singleton. split.
    + intros [-> | (i & Hi & ->)%IH]; [ exists n; naive_solver | exists i; naive_solver].
    + intros (i & Hi & ->). destruct (decide (i = n)) as [-> | Hneq]; first by left.
      right. apply IH. exists i. split; [lia | done].
Qed.

Lemma bor_interp_retag_fnentry σ_t σ_s l ot c T α' M mut :
  let pk : pointer_kind := RefPtr mut in
  let pm := match mut with Mutable => Unique | Immutable => SharedReadOnly end in
  let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
  let L := seq_loc_set l (tsize T) in   (* uses that l_t = l_s *)
  retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l ot FnEntry pk T = Some (Tagged σ_s.(snp), α', S σ_s.(snp)) →
  (if mut is Immutable then is_freeze T else True) →
  state_wf (mkState σ_t.(shp) α' σ_t.(scs) (S σ_t.(snp)) σ_t.(snc)) →   (* could remove that assumption *)
  state_wf (mkState σ_s.(shp) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)) →   (* could remove that assumption *)
  sc_rel (ScPtr l ot) (ScPtr l ot) -∗
  c @@ M -∗
  bor_interp sc_rel σ_t σ_s ==∗ ∃ v_t v_s,
  ⌜length v_t = tsize T⌝ ∗
  ⌜length v_s = tsize T⌝ ∗
  value_rel v_t v_s ∗
  c @@ <[σ_t.(snp) := L]> M ∗
  σ_t.(snp) $$ tk ∗
  l ↦t∗[tk]{σ_t.(snp)} v_t ∗
  l ↦s∗[tk]{σ_t.(snp)} v_s ∗
  match mut with
  | Mutable => True
  | Immutable =>
    sc_rel (ScPtr l (Tagged (σ_t.(snp)))) (ScPtr l (Tagged (σ_t.(snp))))
  end ∗
  bor_interp sc_rel (mkState σ_t.(shp) α' σ_t.(scs) (S σ_t.(snp)) σ_t.(snc)) (mkState σ_s.(shp) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)).
Proof.
  intros pk pm tk L Hretag Hfreeze Hwf'_t Hwf'_s.
  iIntros "Hscrel Hcid Hbor". iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".

  iDestruct "Hscrel" as "[_ Hrel]".
  iAssert (⌜untagged_or_public M_tag ot⌝)%I as %Hpub.
  { iDestruct "Hrel" as "[[-> _] | (%t1 & %t2 & -> & -> & <- & Hpub)]"; first done.
    iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%". done.
  }
  pose nt := (snp σ_t).

  have Hin_dom := retag_Some_dom _ _ _ _ _ _ _ pk _ _ _ _ I Hretag.
  iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom_eq".
  destruct (read_mem_is_Some l (tsize T) σ_s.(shp)) as [v_s Hv_s].
  { setoid_rewrite (state_wf_dom _ Hwf_s). done. }
  destruct (read_mem_is_Some l (tsize T) σ_t.(shp)) as [v_t Hv_t].
  { rewrite Hdom_eq. setoid_rewrite (state_wf_dom _ Hwf_s). done. }
  destruct (read_mem_values _ _ _ _ Hv_s) as [Hlen_s Hshp_s].
  destruct (read_mem_values _ _ _ _ Hv_t) as [Hlen_t Hshp_t].

  (* allocate resources *)
  assert (M_tag !! nt = None) as Htag_none.
  { destruct (M_tag !! nt) as [[tk' []] | ] eqn:Ht_some; last done.
    apply Htag_interp in Ht_some as [Hcontra _]. lia. }
  destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
  iMod (tkmap_insert tk _ tt Htag_none with "Htag_auth") as "[Htag_auth Hnt]".
  iMod (ghost_map_array_tag_insert _ _ v_t nt l with "Htag_t_auth") as "[Ht Htag_t_auth]".
  { intros i Hi. destruct (M_t !! (nt, l +ₗ i)) eqn:Hmt; last done.
    destruct (Ht_dom nt (l +ₗ i) ltac:(eauto)) as (? & ?); congruence. }
  iMod (ghost_map_array_tag_insert _ _ v_s nt l with "Htag_s_auth") as "[Hs Htag_s_auth]".
  { intros i Hi. destruct (M_s !! (nt, l +ₗ i)) eqn:Hmt; last done.
    destruct (Hs_dom nt (l +ₗ i) ltac:(eauto)) as (? & ?); congruence. }
  iMod (ghost_map_array_tag_tk _ _ _ _ tk with "Ht") as "Ht".
  iMod (ghost_map_array_tag_tk _ _ _ _ tk with "Hs") as "Hs".
  set (M' := <[σ_t.(snp) := L]> M).
  iPoseProof (ghost_map_lookup with "Hc Hcid") as "%HM_c".
  iMod (ghost_map_update M' with "Hc Hcid") as "[Hc Hcid]".
  iModIntro.
  (* keep the persistent part if its public *)
  iAssert (nt $$ tk ∗ if tk is tk_pub then nt $$ tk_pub else True)%I  with "[Hnt]" as "[$ Hpubt]".
  { destruct tk; eauto. }
  iExists v_t, v_s. iSplit; first done. iSplit; first done. iFrame "Ht Hs".

  iAssert (⌜retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l ot FnEntry pk T = Some (Tagged nt, α', S (σ_t.(snp)))⌝)%I as "%Hretag_t".
  { iPoseProof (state_rel_calls_eq with "Hsrel") as "<-".
    iPoseProof (state_rel_stacks_eq with "Hsrel") as "<-".
    subst nt. iPoseProof (state_rel_snp_eq with "Hsrel") as "<-". done. }
  (* proving the value relation. TODO: duplicate  *)
  iAssert (value_rel v_t v_s)%I as "#Hvrel"; last iFrame "Hvrel".
  { iApply big_sepL2_forall; iSplit; first (iPureIntro;lia).
    iIntros (i sc_t sc_s) "%Hs_t %Hs_v".
    assert (i < tsize T)%nat as Hi. { rewrite -Hlen_t. eapply lookup_lt_is_Some_1. eauto. }
    assert (Hsome_target : is_Some (σ_t.(shp) !! (l +ₗ i))).
    { rewrite Hshp_t; last done. apply lookup_lt_is_Some_2. by rewrite Hlen_t. }
    iPoseProof (state_rel_pub_if_not_priv _ _ _ _ _ _ (l +ₗ i) with "[] Hsrel [Hrel]") as "Hpub"; first done.
    { iPoseProof (state_rel_calls_eq with "Hsrel") as "%Hcall_eq".
      iPoseProof (state_rel_stacks_eq with "Hsrel") as "%Hstack_eq".
      iPureIntro. intros t Hpriv.
      eapply (priv_loc_UB_retag_access_eq σ_s σ_t); eauto; done. }
    iPoseProof (pub_loc_lookup with "[] Hpub") as "(%sc_t' & %sc_s' & %Hread_both & Hsc_rel)"; first done.
    enough (sc_t = sc_t' ∧ sc_s = sc_s') by naive_solver.
    move : Hs_t Hs_v Hread_both (Hshp_s i Hi) (Hshp_t i Hi).
    by move => -> -> [-> ->] [= ->] [= ->].
  }

  iFrame "Hcid". iSplitL "Hpubt".
  { destruct mut; first done. iSplitR; first done. iRight.
    iExists (σ_t.(snp)), (σ_t.(snp)). do 3 (iSplitR; first done). done. }

  (* re-establishing the interpretation *)
  iExists (<[c:=M']> M_call), (<[ nt := (tk, ()) ]> M_tag), (array_tag_map l nt v_t ∪ M_t), (array_tag_map l nt v_s ∪ M_s).
  iFrame. iSplitL.
  { (* tainted *) iApply (tag_tainted_interp_retag with "Htainted"); done. }
  iSplitL.
  { (* state relation *)
    rewrite /state_rel. simpl. iDestruct "Hsrel" as "(-> & %Hs_eq & -> & -> & -> & Hsrel)".
    do 5 (iSplitL; first done). iIntros (l' Hsl').
    iDestruct ("Hsrel" $! l' with "[//]") as "[Hpub | [%t' %Hpriv]]"; first (iLeft; iApply "Hpub").
    iRight. iPureIntro. exists t'.
    destruct Hpriv as (tk' & Hsome_tk' & Ht_l' & Htk'). exists tk'.
    assert (t' ≠ nt). { intros ->. simplify_eq. }
    rewrite lookup_insert_ne; last done.
    split; first done. split.
    - destruct Ht_l' as (sc0 & Ht_l'). exists sc0.
      rewrite lookup_union_r; first done.
      destruct (array_tag_map l nt v_t !! (t', l')) as [ a | ] eqn:Harr; last done.
      specialize (array_tag_map_lookup1 l nt v_t t' l' ltac:(eauto)) as [Heq _]. congruence.
    - destruct Htk' as [-> | [-> [c' Hin]]]; first by left. right. split; first done. exists c'.
      destruct (decide (c' = c)) as [-> | Hneq].
      + exists M'. rewrite lookup_insert; split; first done.
        destruct Hin as (M'' & HM'' & (L' & HL' & Hin)). simplify_eq. exists L'.
        rewrite lookup_insert_ne; done.
      + destruct Hin as (M'' & HM'' & Hin). exists M''. rewrite lookup_insert_ne; done.
  }
  iSplitL.
  { (* call interpretation. *)
    iPureIntro. intros c' M''. destruct (decide (c' = c)) as [-> | Hneq].
    - rewrite lookup_insert. intros [= <-]. simpl.
      specialize (Hcall_interp c M HM_c) as (Hc & Hinterp). split; first done.
      intros t S. subst M'. destruct (decide (t = σ_t.(snp))) as [-> | Hneq]; first last.
      { rewrite lookup_insert_ne; last done. intros [Ht Hprot]%Hinterp. split; first lia.
        intros l' Hl'. specialize (Hprot l' Hl') as (s & pm' & Hs & Hit & Hpm').
        specialize (retag_item_active_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag_t l' s (Tagged t) c pm' Hs Hc Hit) as (s' & -> & Hin'). eauto.
      }
      rewrite lookup_insert. intros [= <-]. split; first lia. subst L.
      intros l'. rewrite seq_loc_set_elem. intros (i & Hi & ->).
      eapply retag_fn_entry_item_active; done.
    - (* TODO: duplication *)
      rewrite lookup_insert_ne; last done. simpl. intros [Hc' HM']%Hcall_interp.
      split; first done.
      intros t' S HS. simpl. specialize (HM' t' S HS) as (Ht' & Hprot).
      split; first lia. intros l' Hl'.
      specialize (Hprot l' Hl') as (s & pm' & Hs & Hit & Hpm').
      specialize (retag_item_active_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag_t l' s (Tagged t') c' pm' Hs Hc' Hit) as (s' & -> & Hin'). eauto.
  }
  iSplitL.
  { (* tag interpretation. *)
    (* TODO: completely duplicated with the default lemma ... *)
    iPoseProof (state_rel_get_pure with "Hsrel") as "%Hp".
    destruct Hp as (Hsst & Hsnp & Hsnc & Hscs).
    assert (∀l', M_t !! (nt, l') = None) as HMt_nt.
    { intros l'. destruct (M_t !! (nt, l')) eqn:HM_t; last done.
      specialize (Ht_dom nt l' ltac:(eauto)) as (? & ?); congruence. }
    assert (∀l', M_s !! (nt, l') = None) as HMs_nt.
    { intros l'. destruct (M_s !! (nt, l')) eqn:HM_s; last done.
      specialize (Hs_dom nt l' ltac:(eauto)) as (? & ?); congruence. }
    iPureIntro. split_and!.
    { intros t tk'. rewrite lookup_insert_Some. intros [[<- [= <-]] | [Hneq Hsome_t]].
      - cbn. split_and!; [lia | lia | | |].
        + intros l' sc_t Ha%lookup_union_Some_inv_l; last done.
          specialize (array_tag_map_lookup2 l nt v_t nt l' ltac:(eauto)) as [_ (i & Hi & ->)].
          eapply loc_controlled_retag_ref; [ done | done | done | lia | ].
          move : Ha. rewrite array_tag_map_lookup_Some; last done. move => <-. apply Hshp_t. lia.
        + intros l' sc_s Ha%lookup_union_Some_inv_l; last done.
          specialize (array_tag_map_lookup2 l nt v_s nt l' ltac:(eauto)) as [_ (i & Hi & ->)].
          subst nt. rewrite -Hsnp. eapply loc_controlled_retag_ref; [ done | done | done | lia | ].
          move : Ha. rewrite array_tag_map_lookup_Some; last done. move => <-. apply Hshp_s. lia.
        + apply dom_agree_on_tag_union. { apply dom_agree_on_tag_array_tag_map. lia. }
          apply dom_agree_on_tag_not_elem; done.
      - cbn.
        specialize (Htag_interp t tk' Hsome_t) as (Ht_t & Ht_s & Hcontrolled_t & Hcontrolled_s & Hagree).
        split_and!; [ lia | lia | | | ].
        + intros l' sc_t Ha. rewrite lookup_union_r in Ha; last by apply array_tag_map_lookup_None.
          apply Hcontrolled_t in Ha.
          eapply loc_controlled_retag_update; [done | done | | done | done].
          intros <-. destruct tk'; [ done | | ]; move : Hsome_t Hpub; congruence.
        + intros l' sc_s Ha. rewrite lookup_union_r in Ha; last by apply array_tag_map_lookup_None.
          apply Hcontrolled_s in Ha.
          eapply loc_controlled_retag_update; [done | done | | done | done].
          intros <-. destruct tk'; [ done | | ]; move : Hsome_t Hpub; congruence.
        + apply dom_agree_on_tag_union; last done.
          apply dom_agree_on_tag_not_elem; apply array_tag_map_lookup_None; done.
    }
    { intros t l'.
      rewrite lookup_union_is_Some lookup_insert_is_Some'. intros [[-> _]%array_tag_map_lookup2 | H%Ht_dom]; eauto. }
    { intros t l'.
      rewrite lookup_union_is_Some lookup_insert_is_Some'. intros [[-> _]%array_tag_map_lookup2 | H%Hs_dom]; eauto. }
  }
  done.
Qed.

Lemma sim_retag_fnentry mut T l_t l_s c M ot π Φ :
  (0 < tsize T)%nat → (* for convenience: makes the proof easier *)
  let pk : pointer_kind := RefPtr mut in
  let pm := match mut with Mutable => Unique | Immutable => SharedReadOnly end in
  let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
  (if mut is Immutable then is_freeze T else True) →
  sc_rel (ScPtr l_t ot) (ScPtr l_s ot) -∗
  c @@ M -∗
  (∀ nt v_t v_s,
    let L := seq_loc_set l_t (tsize T) in   (* uses that l_t = l_s *)
    ⌜length v_t = tsize T⌝ -∗ ⌜length v_s = tsize T⌝ -∗
    value_rel v_t v_s -∗  (*as the pointers were public before *)
    c @@ <[nt := L]> M -∗
    nt $$ tk -∗
    l_t ↦t∗[tk]{nt} v_t -∗
    l_s ↦s∗[tk]{nt} v_s -∗
    (if mut is Immutable then sc_rel (ScPtr l_t (Tagged nt)) (ScPtr l_s (Tagged nt)) else True) -∗
    #[ScPtr l_t (Tagged nt)] ⪯{π} #[ScPtr l_s (Tagged nt)] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] pk T FnEntry ⪯{π} Retag #[ScPtr l_s ot] #[ScCallId c] pk T FnEntry [{ Φ }].
Proof.
  intros Hsize pk pm tk Hmut. iIntros "#Hscrel Hcid Hsim".
  iApply sim_lift_base_step_both. iIntros (P_t P_s σ_t σ_s ??) "((HP_t & HP_s & Hbor) & %Hthread & %Hsafe)".
  (* exploit source to gain knowledge about stacks & that c is a valid id *)
  specialize (pool_safe_implies Hsafe Hthread) as (c' & ot' & l' & [= <- <-] & [= <-] & Hc_active & Hretag_some_s).
  iPoseProof "Hscrel" as "(-> & _)".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  have Hretag_some_t : is_Some (retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l_s ot FnEntry pk T).
  { destruct Hp as (<- & <- & _ & <- & _). done. }
  iModIntro. iSplitR.
  { iPureIntro.
    destruct Hretag_some_t as ([[] ] & Hretag_some_t).
    do 3 eexists. eapply retag_base_step'; last done.
    destruct Hp as (_ & _ & _ & <- & _). done.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_retag_inv _ _ _ _ _ _ _ _ _ _ _ Hhead_t) as (nt & α' & nxtp' & Hretag_t & -> & -> & -> & Hc).
  have Hretag_s : retag σ_s.(sst) σ_s.(snp) σ_s.(scs) c l_s ot FnEntry pk T = Some (nt, α', nxtp').
  { destruct Hp as (-> & -> & _ & -> & _). done. }
  assert (Hhead_s : base_step P_s (Retag #[ScPtr l_s ot] #[ScCallId c] pk T FnEntry) σ_s #[ScPtr l_s nt]%E (mkState (shp σ_s) α' (scs σ_s) nxtp' (snc σ_s)) []).
  { eapply retag_base_step'; done. }
  specialize (retag_change_ref_NZST _ _ _ _ _ _ _ _ _ _ _ _ Hsize Hretag_s) as [-> ->].

  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %Hwf_s]".
  iMod (bor_interp_retag_fnentry _ _ _ _ _ _ _ _ _ Hretag_s with "Hscrel Hcid Hbor") as
    (v_t v_s) "(%Hlen_t & %Hlen_s & Hval & Hcid & Htag & Ht & Hs & Hpub & Hbor)"; first done.
  { destruct Hp as (_ & <- & _). eapply base_step_wf; eauto. }
  { eapply base_step_wf; eauto. }
  iModIntro.

  iExists #[ScPtr l_s (Tagged σ_s.(snp))]%E, [], (mkState σ_s.(shp) α' σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)).
  iSplitR; first done.
  destruct Hp as (_ & -> & _).
  iFrame "Hbor HP_t HP_s".
  iSplitL; last done.
  iApply ("Hsim" with "[] [] Hval Hcid Htag Ht Hs Hpub"); [done | done | ..].
Qed.

(** ** Updates for calls sets *)
(* TODO: maybe formulate that with [update_si] instead *)
Lemma sim_protected_unprotectN M L l c t tk v_t v_s  π Φ e_t e_s :
  (∀ i : nat, (i < length v_t)%nat → (l +ₗ i) ∈ L) →
  M !! t = Some L →
  c @@ M -∗
  t $$ tk -∗
  l ↦t∗[tk]{t} v_t -∗
  l ↦s∗[tk]{t} v_s -∗
  value_rel v_t v_s -∗
  (c @@ (<[t := L ∖ (seq_loc_set l (length v_t)) ]> M) -∗ t $$ tk -∗ l ↦t∗[tk]{t} v_t -∗ l ↦s∗[tk]{t} v_s -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
  e_t ⪯{π} e_s [{ Φ }].
Proof.
  iIntros (Hl HL) "Hc Htag Ht Hs #Hvrel Hsim".
  iApply sim_update_si. rewrite /update_si. iIntros (?????) "(HP_t & HP_s & Hbor)".
  set (L' := L ∖ seq_loc_set l (length v_t)). set (M' := <[ t := L' ]> M).
  iPoseProof (value_rel_length with "Hvrel") as "%Hlen".
  iPoseProof (bor_interp_readN_source_protected with "Hbor Hs Htag Hc") as "(%Hv_s & %)".
  { intros i Hi. exists L. split; first done. apply Hl. lia. }
  iPoseProof (bor_interp_readN_target_protected with "Hbor Ht Htag Hc") as "(%Hv_t & %)".
  { intros i Hi. exists L. split; first done. apply Hl. lia. }

  iDestruct "Hbor" as "(%M_call & %M_tag & %M_t & %M_s & (Hcall_auth & Htag_auth & Htag_t_auth & Htag_s_auth) & Htainted & Hpub_cid & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".
  iPoseProof (ghost_map_lookup with "Hcall_auth Hc") as "%HcM".
  iMod (ghost_map_update M' with "Hcall_auth Hc") as "[Hcall_auth Hc]".
  iModIntro. iFrame "HP_t HP_s". iSplitR "Hsim Hc Ht Htag Hs"; last by iApply ("Hsim" with "Hc Htag Ht Hs").
  iExists (<[ c := M' ]> M_call), M_tag, M_t, M_s. iFrame.
  iSplitL "Hsrel".
  { iDestruct "Hsrel" as "(%Hdom_eq & %Hsst_eq & %Hsnp_eq & %Hsnc_eq & %Hscs_eq & Hloc)".
    do 5 (iSplitR; first done).
    iIntros (l' Hl'). iDestruct ("Hloc" $! l' with "[//]") as "[Hpub | %Hpriv]"; first by iLeft.
    destruct (decide (l' ∈ seq_loc_set l (length v_t))) as [(i & Hi & ->)%seq_loc_set_elem | Hnotin].
    - (* location is made public *)
      iLeft. iIntros (sc_t' Hsc_t').
      specialize (Hv_t i Hi) as Heq. rewrite Heq in Hsc_t'.
      iExists (v_s !!! i). iSplitR.
      + iPureIntro. rewrite Hv_s; last lia. apply list_lookup_lookup_total, lookup_lt_is_Some_2. lia.
      + iPoseProof (value_rel_lookup_total v_t v_s i with "Hvrel") as "Hsc"; first lia.
        rewrite -(list_lookup_total_correct _ _ _ Hsc_t'). done.
    - (* location is still private *)
      iRight. iPureIntro. destruct Hpriv as (t' & tk' & Htk' & Hsome & Hpriv).
      exists t', tk'. split; first done. split; first done.
      destruct Hpriv as [-> | [-> Hpriv]]; first by left. right; split; first done.
      destruct Hpriv as (c' & M'' & Hc' & Hin').
      destruct (decide (c' = c)) as [-> | Hneq]; first last.
      { exists c', M''. rewrite lookup_insert_ne; done. }
      exists c, M'. rewrite lookup_insert. split; first done.
      destruct (decide (t' = t)) as [-> | Hneq']; first last.
      { destruct Hin' as (L'' & HL'' & Hl''). exists L''. split; last done.
        simplify_eq. rewrite lookup_insert_ne; done.
      }
      destruct Hin' as (L'' & HL'' & Hl''). exists L'. split; first by rewrite lookup_insert.
      simplify_eq. subst L'. apply elem_of_difference. done.
  }
  iSplitL; last done.
  iPureIntro. intros c' M''. rewrite lookup_insert_Some. intros [[<- <-] | [Hneq Hsome]].
  - apply Hcall_interp in HcM as [Hc HcM]. split; first done.
    intros t' L''. subst M'. rewrite lookup_insert_Some. intros [[<- <-] | [Hneq' Hsome']].
    + specialize (HcM t L HL) as (Ht & HsL). split; first done.
      intros l'. rewrite elem_of_difference. intros [Hl'%HsL _]. done.
    + specialize (HcM _ _ Hsome') as (Ht & HsL). done.
  - apply Hcall_interp in Hsome as [Hc' Hsome]. done.
Qed.

(** General tk_pub retag *)
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

End lifting.


