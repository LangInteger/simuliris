From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From simuliris.base_logic Require Export gen_sim_heap gen_sim_prog.
From simuliris.simulation Require Import slsls lifting.
From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.
From simuliris.simplang Require Export class_instances primitive_laws.

From iris.prelude Require Import options.

(** * Instance of the SimpLang program logic that provides a means of establishing bijections on the heap. *)

Class sbijG (Σ : gFunctors) := SBijG {
  sbijG_sheapG :> sheapG Σ;
  sbijG_bijG :> gset_bijG Σ block block;
  sbijG_bij_name : gname;
}.

Section definitions.
  Context `{sbijG Σ}.

  Definition heap_bij_auth (L : gset (block * block)) :=
    gset_bij_own_auth sbijG_bij_name (DfracOwn 1) L.
  Definition heap_bij_elem (l_t : block) (l_s : block) :=
    gset_bij_own_elem sbijG_bij_name l_t l_s.

  Definition vrel_list (val_rel : val → val → iProp Σ) (v_t v_s : list val) : iProp Σ :=
    ([∗ list] vt; vs ∈ v_t; v_s, val_rel vt vs).
  Global Instance vrel_list_persistent val_rel vs_t vs_s : (∀ v_t v_s, Persistent (val_rel v_t v_s)) → Persistent (vrel_list val_rel vs_t vs_s).
  Proof. apply _. Qed.

  Lemma vrel_list_update val_rel vs_t vs_s i v_s v_t :
    i < length vs_t →
    i < length vs_s →
    vrel_list val_rel vs_t vs_s -∗
    val_rel v_t v_s -∗
    vrel_list val_rel (<[i := v_t]> vs_t) (<[i := v_s]> vs_s).
  Proof.
    iIntros (Hs Ht) "Hl Hv". rewrite /vrel_list.
    iPoseProof (big_sepL2_insert_acc (λ _, val_rel) vs_t vs_s i with "Hl") as "[_ Hi]".
    - apply list_lookup_alt; done.
    - apply list_lookup_alt; done.
    - by iApply "Hi".
  Qed.

  (** We require the [lock_state]s to be the same, pointwise *)
  Definition alloc_rel val_rel b_t b_s : iProp Σ :=
    (∃ (n : option nat) sts vs_t vs_s,
      ⌜length vs_t = default 0 n⌝ ∗
      (Loc b_t 0) ↦t∗[sts] vs_t ∗
      (Loc b_s 0) ↦s∗[sts] vs_s ∗
      vrel_list val_rel vs_t vs_s ∗
      †Loc b_t 0 …?t n ∗
      †Loc b_s 0 …?s n).

  Lemma alloc_rel_read val_rel b_t b_s σ_s σ_t o v st:
    heap σ_s !! Loc b_s o = Some (st, v) →
    alloc_rel val_rel b_t b_s -∗
    heap_ctx sheapG_allocN_source (heap σ_s) (used_blocks σ_s) -∗
    heap_ctx sheapG_allocN_target (heap σ_t) (used_blocks σ_t) -∗
    ∃ v', ⌜heap σ_t !! Loc b_t o = Some (st, v')⌝ ∗ val_rel v' v.
  Proof.
    iIntros (?).
    iDestruct 1 as (n sts vs_t vs_s Hlen) "(Hp_t & Hp_s & Hvrel & Halloc_t & Halloc_s)".
    iIntros "Hσ_s Hσ_t".
    iDestruct (big_sepL2_length with "Hp_t") as %?.
    iDestruct (big_sepL2_length with "Hp_s") as %?.

    iDestruct (heap_freeable_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    have [st' Hst]:= lookup_lt_is_Some_2 sts n' ltac:(lia).
    iDestruct (big_sepL2_lookup_acc with "Hp_s") as "[Hl_s Hp_s]"; [done..|].
    iDestruct (big_sepL2_lookup_acc with "Hp_t") as "[Hl_t Hp_t]"; [done..|].
    iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %Hl_s.
    iDestruct (heap_read_st_1 with "Hσ_t Hl_t") as %Hl_t.
    rewrite Loc_add in Hl_s. rewrite Loc_add in Hl_t.
    simplify_eq/=.
    iExists _. iSplitR; [done|]. by iApply (big_sepL2_lookup with "Hvrel").
  Qed.

  Lemma alloc_rel_write val_rel b_t b_s σ_s σ_t o v st st' v_s' v_t':
    heap σ_s !! Loc b_s o = Some (st, v) →
    alloc_rel val_rel b_t b_s -∗
    heap_ctx sheapG_allocN_source (heap σ_s) (used_blocks σ_s) -∗
    heap_ctx sheapG_allocN_target (heap σ_t) (used_blocks σ_t) -∗
    val_rel v_t' v_s' ==∗
    alloc_rel val_rel b_t b_s ∗
    heap_ctx sheapG_allocN_source (<[Loc b_s o := (st', v_s')]> (heap σ_s)) (used_blocks σ_s) ∗
    heap_ctx sheapG_allocN_target (<[Loc b_t o := (st', v_t')]> (heap σ_t)) (used_blocks σ_t).
  Proof.
    iIntros (?).
    iDestruct 1 as (n sts vs_t vs_s Hlen) "(Hp_t & Hp_s & Hvrel & Halloc_t & Halloc_s)".
    iIntros "Hσ_s Hσ_t Hval".
    iDestruct (big_sepL2_length with "Hp_t") as %?.
    iDestruct (big_sepL2_length with "Hp_s") as %?.

    iDestruct (heap_freeable_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    have [st'' Hst]:= lookup_lt_is_Some_2 sts n' ltac:(lia).
    iDestruct (big_sepL2_insert_acc with "Hp_s") as "[Hl_s Hp_s]"; [done..|].
    iDestruct (big_sepL2_insert_acc with "Hp_t") as "[Hl_t Hp_t]"; [done..|].
    iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %Hl_s.
    iDestruct (heap_read_st_1 with "Hσ_t Hl_t") as %Hl_t.
    rewrite Loc_add in Hl_s. rewrite Loc_add in Hl_t.
    simplify_eq/=.

    iMod (heap_write with "Hσ_s Hl_s") as "[$ Hl_s]".
    iMod (heap_write with "Hσ_t Hl_t") as "[$ Hl_t]".
    rewrite !Loc_add.
    iModIntro.
    iExists _, _, _, _.
    iFrame "Halloc_t Halloc_s".
    iSplitR; last first.
    - iSplitL "Hl_t Hp_t". { by iApply "Hp_t". }
      iSplitL "Hl_s Hp_s". { by iApply "Hp_s". }
      iApply (vrel_list_update with "Hvrel"); [ lia | lia | done].
    - iPureIntro. rewrite insert_length. lia.
  Qed.

  Definition heap_bij_interp (val_rel : val → val → iProp Σ) :=
    (∃ L, heap_bij_auth L ∗
      [∗ set] p ∈ L,
        let '(b_t, b_s) := p in alloc_rel val_rel b_t b_s)%I.
End definitions.

Notation "b_t '⇔h' b_s" := (heap_bij_elem b_t b_s) (at level 30) : bi_scope.
Definition loc_rel `{sbijG Σ} l_t l_s : iProp Σ := loc_chunk l_t ⇔h loc_chunk l_s ∗ ⌜loc_idx l_t = loc_idx l_s⌝.
Notation "l_t '↔h' l_s" := (loc_rel l_t l_s) (at level 30) : bi_scope.

Section laws.
  Context `{sbijG Σ}.
  Implicit Types (b_t b_s : block) (l_t l_s : loc).

  Global Instance heap_bij_elem_persistent b_t b_s :
    Persistent (b_t ⇔h b_s).
  Proof. apply _. Qed.
  Global Instance heap_bij_elem_loc_persistent l_t l_s :
    Persistent (l_t ↔h l_s).
  Proof. apply _. Qed.

  Lemma heap_bij_agree b_t1 b_t2 b_s1 b_s2 :
    b_t1 ⇔h b_s1 -∗ b_t2 ⇔h b_s2 -∗ ⌜b_t1 = b_t2 ↔ b_s1 = b_s2⌝.
  Proof.
    iIntros "H1 H2". iApply (gset_bij_own_elem_agree with "H1 H2").
  Qed.
  Lemma heap_bij_loc_agree l_t1 l_t2 l_s1 l_s2 :
    l_t1 ↔h l_s1 -∗ l_t2 ↔h l_s2 -∗ ⌜l_t1 = l_t2 ↔ l_s1 = l_s2⌝.
  Proof.
    iIntros "[H1 %Heq1] [H3 %Heq2]".
    iPoseProof (heap_bij_agree with "H1 H3") as "%Ha". iPureIntro.
    destruct l_t1, l_t2, l_s1, l_s2; cbn in *; subst. naive_solver.
  Qed.

  Lemma heap_bij_func b_t b_s1 b_s2 :
    b_t ⇔h b_s1 -∗ b_t ⇔h b_s2 -∗ ⌜b_s1 = b_s2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heap_bij_agree with "H1 H2") as "<-"; done.
  Qed.
  Lemma heap_bij_loc_func l_t l_s1 l_s2 :
    l_t ↔h l_s1 -∗ l_t ↔h l_s2 -∗ ⌜l_s1 = l_s2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heap_bij_loc_agree with "H1 H2") as "<-"; done.
  Qed.

  Lemma heap_bij_inj b_s b_t1 b_t2 :
    b_t1 ⇔h b_s -∗ b_t2 ⇔h b_s -∗ ⌜b_t1 = b_t2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heap_bij_agree with "H1 H2") as "->"; done.
  Qed.
  Lemma heap_bij_loc_inj l_s l_t1 l_t2 :
    l_t1 ↔h l_s -∗ l_t2 ↔h l_s -∗ ⌜l_t1 = l_t2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (heap_bij_loc_agree with "H1 H2") as "->"; done.
  Qed.

  Lemma heap_bij_loc_shift l_t l_s i : l_t ↔h l_s -∗ (l_t +ₗ i) ↔h (l_s +ₗ i).
  Proof.
    iIntros "[Hi %Hj]". iSplitL "Hi"; first done. iPureIntro.
    destruct l_t, l_s; cbn in *; lia.
  Qed.

  Lemma heap_bij_access val_rel b_t b_s :
    heap_bij_interp val_rel -∗
    b_t ⇔h b_s -∗
    (alloc_rel val_rel b_t b_s) ∗
    (alloc_rel val_rel b_t b_s -∗ heap_bij_interp val_rel).
  Proof.
    iIntros "Hinv Hrel". iDestruct "Hinv" as (L) "[Hauth Hheap]".
    iPoseProof (gset_bij_elem_of with "Hauth Hrel") as "%".
    iPoseProof (big_sepS_delete with "Hheap") as "[He Hheap]"; first done.
    iFrame.
    iIntros "He". iExists L. iFrame.
    iApply big_sepS_delete; first done. iFrame.
  Qed.

  Lemma heap_bij_insertN val_rel l_t l_s v_t v_s n :
    n > 0 →
    length v_s = n →
    length v_t = n →
    heap_bij_interp val_rel -∗
    l_t ↦t∗ v_t -∗
    l_s ↦s∗ v_s -∗
    vrel_list val_rel v_t v_s -∗
    †l_t …t n -∗
    †l_s …s n ==∗
    heap_bij_interp val_rel ∗
    l_t ↔h l_s.
  Proof.
    rewrite !heap_mapsto_vec_to_st.
    iIntros (Hn Hl_s Hl_t) "Hinv Ht Hs Hrel Ha_t Ha_s".
    iDestruct (heap_freeable_idx with "Ha_t") as %?.
    iDestruct (heap_freeable_idx with "Ha_s") as %?.
    iDestruct "Hinv" as (L) "[Hauth Hheap]".
    pose (b_t := loc_chunk l_t). pose (b_s := loc_chunk l_s).
    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), b_t = b_t') L⌝)%I) as "%Hext_t".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (n' sts v_t' v_s') "(_ & _ & _ & _ & Ha_t' & _)".
      by iApply (heap_freeable_excl with "Ha_t Ha_t'").
    }
    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), b_s = b_s') L⌝)%I) as "%Hext_s".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (n' sts v_t' v_s') "(_ & _ & _ & _ & _ & Ha_s')".
      by iApply (heap_freeable_excl with "Ha_s Ha_s'").
    }
    iMod ((gset_bij_own_extend b_t b_s) with "Hauth") as "[Hinv #Helem]".
    - intros b_s' Hb_s'. apply Hext_t. by exists (b_t, b_s').
    - intros b_t' Hb_t'. apply Hext_s. by exists (b_t', b_s).
    - iModIntro.
      iSplitL; first last. { iSplitL; first done. iPureIntro; lia. }
      iExists ({[(b_t, b_s)]} ∪ L)%I. iFrame.
      iApply big_sepS_insert. { contradict Hext_t. by exists (b_t, b_s). }
      iFrame. iExists (Some n), _, v_t, v_s. iFrame.
      destruct l_t, l_s; cbn in *; subst. iFrame.
      rewrite !Hl_t. by iFrame.
  Qed.
End laws.


Section fix_heap.
  Context `{sbijG Σ} (val_rel : val → val → iProp Σ) (π : thread_id).
  Context {val_rel_pers : ∀ v_t v_s, Persistent (val_rel v_t v_s)}.

  Program Instance heap_bij_inv : sheapInv Σ := {|
    sheap_inv _ _ _ _ _:= heap_bij_interp val_rel;
  |}.
  Next Obligation. done. Qed.
  Global Instance : sheapInvConst.
  Proof. done. Qed.

  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{π, val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.
  Local Notation "et '⪯' es [{ Φ }]" := (et ⪯{π, val_rel} es [{Φ}])%I (at level 40, Φ at level 200) : bi_scope.

  Lemma sim_bij_load_sc l_t l_s Φ :
    l_t ↔h l_s -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ Val v_t ⪯ Val v_s [{ Φ }]) -∗
    (Load ScOrd (Val $ LitV $ LitLoc l_t)) ⪯ (Load ScOrd (Val $ LitV $ LitLoc l_s)) [{ Φ }].
  Proof using val_rel_pers.
    iIntros "#[Hbij %Hidx] Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %Hsafe]]".
    have [l[v[m[[<-] Hsome]]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(Halloc & Hclose)"; first last.
    iDestruct (alloc_rel_read with "Halloc Hσ_s Hσ_t") as (??) "#?"; [done|].
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id.
    iSplitR "Hsim".
    - by iApply "Hclose".
    - by iApply "Hsim".
  Qed.

  Lemma sim_bij_load_na2 l_t l_s Φ :
    l_t ↔h l_s -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ Val v_t ⪯ Val v_s [{ Φ }]) -∗
    (Load Na2Ord (Val $ LitV $ LitLoc l_t)) ⪯ (Load Na2Ord (Val $ LitV $ LitLoc l_s)) [{ Φ }].
  Proof using val_rel_pers.
    iIntros "#[Hbij %Hidx] Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %Hsafe]]".
    have [l[v[m[[<-] Hsome]]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(Halloc & Hclose)"; first last.
    iDestruct (alloc_rel_read with "Halloc Hσ_s Hσ_t") as (??) "#Hv"; [done|].
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (alloc_rel_write with "Halloc Hσ_s Hσ_t Hv") as "[Halloc [Hσ_s Hσ_t]]"; [done|].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id.
    iSplitR "Hsim".
    - by iApply "Hclose".
    - by iApply "Hsim".
  Qed.

  Lemma sim_bij_load_na1 l_t l_s Φ :
    l_t ↔h l_s -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ Val v_t ⪯ Val v_s [{ Φ }]) -∗
    (Load Na1Ord (Val $ LitV $ LitLoc l_t)) ⪯ (Load Na1Ord (Val $ LitV $ LitLoc l_s)) [{ Φ }].
  Proof using val_rel_pers.
    iIntros "#[Hbij %Hidx] Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %Hsafe]]".
    have [l[v[m[[<-] Hsome]]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(Halloc & Hclose)"; first last.
    iDestruct (alloc_rel_read with "Halloc Hσ_s Hσ_t") as (??) "#Hv"; [done|].
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (alloc_rel_write with "Halloc Hσ_s Hσ_t Hv") as "[Halloc [Hσ_s Hσ_t]]"; [done|].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id.
    iSplitR "Hsim".
    - by iApply "Hclose".
    - iApply sim_bij_load_na2; [|done]. by iSplit.
  Qed.

  Lemma sim_bij_load l_t l_s o Φ :
    l_t ↔h l_s -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ Val v_t ⪯ Val v_s [{ Φ }]) -∗
    (Load o (Val $ LitV $ LitLoc l_t)) ⪯ (Load o (Val $ LitV $ LitLoc l_s)) [{ Φ }].
  Proof using val_rel_pers. destruct o; [iApply sim_bij_load_sc | iApply sim_bij_load_na1 | iApply sim_bij_load_na2]. Qed.

  Lemma sim_bij_store_sc l_t l_s v_t v_s Φ :
    l_t ↔h l_s -∗
    val_rel v_t v_s -∗
    #() ⪯ #() [{ Φ }] -∗
    Store ScOrd (Val $ LitV (LitLoc l_t)) (Val v_t) ⪯ Store ScOrd (Val $ LitV (LitLoc l_s)) (Val v_s) [{ Φ }].
  Proof using val_rel_pers.
    iIntros "#[Hbij %Hidx] Hval Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %Hsafe]]".
    have [l[v[[<-] Hsome]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(Halloc & Hclose)"; first last.
    iDestruct (alloc_rel_read with "Halloc Hσ_s Hσ_t") as (??) "#Hv"; [done|].
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (alloc_rel_write with "Halloc Hσ_s Hσ_t Hval") as "[Halloc [Hσ_s Hσ_t]]"; [done|].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id.
    by iApply "Hclose".
  Qed.

  Lemma sim_bij_store_na2 l_t l_s v_t v_s Φ :
    l_t ↔h l_s -∗
    val_rel v_t v_s -∗
    #() ⪯ #() [{ Φ }] -∗
    Store Na2Ord (Val $ LitV (LitLoc l_t)) (Val v_t) ⪯ Store Na2Ord (Val $ LitV (LitLoc l_s)) (Val v_s) [{ Φ }].
  Proof using val_rel_pers.
    iIntros "#[Hbij %Hidx] Hval Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %Hsafe]]".
    have [l[v[[<-] Hsome]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(Halloc & Hclose)"; first last.
    iDestruct (alloc_rel_read with "Halloc Hσ_s Hσ_t") as (??) "#Hv"; [done|].
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (alloc_rel_write with "Halloc Hσ_s Hσ_t Hval") as "[Halloc [Hσ_s Hσ_t]]"; [done|].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id.
    by iApply "Hclose".
  Qed.

  Lemma sim_bij_store_na1 l_t l_s v_t v_s Φ :
    l_t ↔h l_s -∗
    val_rel v_t v_s -∗
    #() ⪯ #() [{ Φ }] -∗
    Store Na1Ord (Val $ LitV (LitLoc l_t)) (Val v_t) ⪯ Store Na1Ord (Val $ LitV (LitLoc l_s)) (Val v_s) [{ Φ }].
  Proof using val_rel_pers.
    iIntros "#[Hbij %Hidx] Hval Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %Hsafe]]".
    have [l[v[[<-] Hsome]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(Halloc & Hclose)"; first last.
    iDestruct (alloc_rel_read with "Halloc Hσ_s Hσ_t") as (??) "#Hv"; [done|].
    iModIntro; iSplit; first by eauto with head_step.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (alloc_rel_write with "Halloc Hσ_s Hσ_t Hv") as "[Halloc [Hσ_s Hσ_t]]"; [done|].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    iFrame => /=. rewrite right_id.
    iSplitR "Hsim Hval".
    - by iApply "Hclose".
    - iApply (sim_bij_store_na2 with "[] Hval Hsim"). by iSplit.
  Qed.

  Lemma sim_bij_store l_t l_s v_t v_s o Φ :
    l_t ↔h l_s -∗
    val_rel v_t v_s -∗
    #() ⪯ #() [{ Φ }] -∗
    Store o (Val $ LitV (LitLoc l_t)) (Val v_t) ⪯ Store o (Val $ LitV (LitLoc l_s)) (Val v_s) [{ Φ }].
  Proof using val_rel_pers. destruct o; [iApply sim_bij_store_sc | iApply sim_bij_store_na1 | iApply sim_bij_store_na2]. Qed.

  Lemma sim_bij_free l_t l_s Φ n :
    l_t ↔h l_s -∗
    #() ⪯ #() [{ Φ }] -∗
    FreeN (Val $ LitV $ LitInt n) (Val $ LitV $ LitLoc l_t) ⪯ FreeN (Val $ LitV $ LitInt n) (Val $ LitV $ LitLoc l_s) [{ Φ }].
  Proof using val_rel_pers.
    iIntros "#[Hbij %Hidx] Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_head_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %Hsafe]]".
    have [m[?[[<-][[<-][??]]]]]:= pool_safe_irred _ _ _ _ _ _ _ Hsafe ltac:(done) ltac:(done).
    iPoseProof (heap_bij_access with "Hinv Hbij") as "(Halloc & Hclose)"; first last.

    iDestruct "Halloc" as (p sts vs_t vs_s Hlen) "(Hl_t & Hl_s & #Hvals & Ha_t & Ha_s)".
    iDestruct (big_sepL2_length with "Hl_t") as %Hlent.
    iDestruct (big_sepL2_length with "Hl_s") as %Hlens.
    iDestruct (heap_freeable_inj with "Hσ_s Ha_s") as %[? Hl]; [done..|]. move: Hl => [?]. subst.

    iMod (heap_free with "Hσ_t Hl_t [Ha_t]") as (? Hlookup) "[Ha_t Hσ_t]"; [ by rewrite Hlen /= | by rewrite Hlen |].
    rewrite  Z2Nat.id in Hlookup; [| lia].
    iModIntro; iSplit; first by eauto with head_step lia.
    iIntros (e_t' efs σ_t') "%"; inv_head_step.
    iMod (heap_free with "Hσ_s Hl_s [Ha_s]") as (_ _) "[Ha_s Hσ_s]";
      [ done | by rewrite -Hlens Hlent Hlen |].
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with head_step.
    rewrite -Hlens Hlent Hlen !Z2Nat.id /=; [|lia]. iFrame.
    iApply "Hclose".
    iExists None, [], [], []. iFrame.
    iSplitR; [done|].
    iSplitR; [by iApply big_sepL2_nil|].
    iSplitR; [by iApply big_sepL2_nil|].
    by iApply big_sepL2_nil.
  Qed.

  Lemma sim_bij_insertN l_t l_s vs_t vs_s e_t e_s n Φ :
    n > 0 →
    length vs_t = n →
    length vs_s = n →
    †l_t …t n -∗
    †l_s …s n -∗
    l_t ↦t∗ vs_t -∗
    l_s ↦s∗ vs_s -∗
    vrel_list val_rel vs_t vs_s -∗
    (l_t ↔h l_s -∗ e_t ⪯ e_s [{ Φ }]) -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros (Hn Ht Hs) "Hs_t Hs_s Hl_t Hl_s Hval Hsim". iApply sim_update_si.
    iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
    iMod (heap_bij_insertN with "Hinv Hl_t Hl_s Hval Hs_t Hs_s") as "[Hb #Ha]"; [done .. | ].
    iModIntro. iFrame. by iApply "Hsim".
  Qed.

  Lemma sim_bij_insert l_t l_s v_t v_s e_t e_s Φ :
    †l_t …t 1 -∗
    †l_s …s 1 -∗
    l_t ↦t v_t -∗
    l_s ↦s v_s -∗
    val_rel v_t v_s -∗
    (l_t ↔h l_s -∗ e_t ⪯ e_s [{ Φ }]) -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "Hs_t Hs_s Hl_t Hl_s Hv".
    iApply (sim_bij_insertN _ _ [v_t] [v_s] with "Hs_t Hs_s [Hl_t] [Hl_s] [Hv]"); [lia | done | done | | | ].
    - by rewrite heap_mapsto_vec_singleton.
    - by rewrite heap_mapsto_vec_singleton.
    - by iApply big_sepL2_singleton.
  Qed.
End fix_heap.

(** ** Default value relation *)
Section val_rel.
  Context `{sbijG Σ}.
  Fixpoint val_rel (v_t v_s : val) {struct v_s} : iProp Σ :=
    match v_t, v_s with
    | LitV (LitLoc l_t), LitV (LitLoc l_s) =>
        l_t ↔h l_s
    | LitV l_t, LitV l_s =>
        ⌜l_t = l_s⌝
    | PairV v1_t v2_t, PairV v1_s v2_s =>
        val_rel v1_t v1_s ∧ val_rel v2_t v2_s
    | InjLV v_t, InjLV v_s =>
        val_rel v_t v_s
    | InjRV v_t, InjRV v_s =>
        val_rel v_t v_s
    | _,_ => False
    end.
  Global Instance : sheapInv Σ := heap_bij_inv val_rel.
  Global Instance val_rel_pers v_t v_s : Persistent (val_rel v_t v_s).
  Proof.
    induction v_s as [[] | | | ] in v_t |-*; destruct v_t as [ [] | | | ]; apply _.
  Qed.

  Lemma val_rel_pair_source v_t v_s1 v_s2 :
    val_rel v_t (v_s1, v_s2) -∗
    ∃ v_t1 v_t2, ⌜v_t = PairV v_t1 v_t2⌝ ∗
      val_rel v_t1 v_s1 ∗
      val_rel v_t2 v_s2.
  Proof.
    simpl. iIntros "H". destruct v_t as [[] | v_t1 v_t2 | |]; simpl; try done.
    iExists v_t1, v_t2. iDestruct "H" as "[#H1 #H2]". eauto.
  Qed.
  Lemma val_rel_injl_source v_t v_s :
    val_rel v_t (InjLV v_s) -∗ ∃ v_t', ⌜v_t = InjLV v_t'⌝ ∗ val_rel v_t' v_s.
  Proof. simpl. destruct v_t as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma val_rel_injr_source v_t v_s :
    val_rel v_t (InjRV v_s) -∗ ∃ v_t', ⌜v_t = InjRV v_t'⌝ ∗ val_rel v_t' v_s.
  Proof. simpl. destruct v_t as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.


  Lemma val_rel_litfn_source v_t fn_s :
    val_rel v_t (LitV $ LitFn $ fn_s) -∗ ⌜v_t = LitV $ LitFn $ fn_s⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litint_source v_t n :
    val_rel v_t (LitV $ LitInt n) -∗ ⌜v_t = LitV $ LitInt $ n⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litbool_source v_t b:
    val_rel v_t (LitV $ LitBool b) -∗ ⌜v_t = LitV $ LitBool b⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litunit_source v_t :
    val_rel v_t (LitV $ LitUnit) -∗ ⌜v_t = LitV $ LitUnit⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litpoison_source v_t :
    val_rel v_t (LitV $ LitPoison) -∗ ⌜v_t = LitV $ LitPoison⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_loc_source v_t l_s :
    val_rel v_t (LitV $ LitLoc l_s) -∗
    ∃ l_t, ⌜v_t = LitV $ LitLoc l_t⌝ ∗ l_t ↔h l_s.
  Proof.
    destruct v_t as [[ | | | | l_t | ] | | | ]; simpl;
        first [iIntros "%Ht"; congruence | iIntros "#Ht"; eauto].
  Qed.

  Lemma val_rel_pair_target v_s v_t1 v_t2 :
    val_rel (v_t1, v_t2) v_s -∗
    ∃ v_s1 v_s2, ⌜v_s = PairV v_s1 v_s2⌝ ∗
      val_rel v_t1 v_s1 ∗
      val_rel v_t2 v_s2.
  Proof.
    simpl. iIntros "H". destruct v_s as [[] | v_s1 v_s2 | |]; simpl; try done.
    iExists v_s1, v_s2. iDestruct "H" as "[#H1 #H2]". eauto.
  Qed.
  Lemma val_rel_injl_target v_t v_s :
    val_rel (InjLV v_t) v_s -∗ ∃ v_s', ⌜v_s = InjLV v_s'⌝ ∗ val_rel v_t v_s'.
  Proof. simpl. destruct v_s as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma val_rel_injr_target v_t v_s :
    val_rel (InjRV v_t) v_s -∗ ∃ v_s', ⌜v_s = InjRV v_s'⌝ ∗ val_rel v_t v_s'.
  Proof. simpl. destruct v_s as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma val_rel_litfn_target v_s fn_t :
    val_rel (LitV $ LitFn $ fn_t) v_s -∗ ⌜v_s = LitV $ LitFn $ fn_t⌝.
  Proof. simpl. destruct v_s as [[] | v_s1 v_s2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litint_target v_s n :
    val_rel (LitV $ LitInt n) v_s -∗ ⌜v_s = LitV $ LitInt $ n⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litbool_target v_s b:
    val_rel (LitV $ LitBool b) v_s -∗ ⌜v_s = LitV $ LitBool b⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litunit_target v_s :
    val_rel (LitV $ LitUnit) v_s -∗ ⌜v_s = LitV $ LitUnit⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litpoison_target v_s :
    val_rel (LitV $ LitPoison) v_s -∗ ⌜v_s = LitV $ LitPoison⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_loc_target v_s l_t :
    val_rel (LitV $ LitLoc l_t) v_s -∗
    ∃ l_s, ⌜v_s = LitV $ LitLoc l_s⌝ ∗ l_t ↔h l_s.
  Proof.
    destruct v_s as [[ | | | | l_s | ] | | | ]; simpl;
        first [iIntros "%Hs"; congruence | iIntros "#Hs"; eauto].
  Qed.
End val_rel.
Tactic Notation "val_discr_source" constr(H) :=
  first [iPoseProof (val_rel_litint_source with H) as "->" |
         iPoseProof (val_rel_litbool_source with H) as "->" |
         iPoseProof (val_rel_litfn_source with H) as "->" |
         iPoseProof (val_rel_litunit_source with H) as "->" |
         iPoseProof (val_rel_litpoison_source with H) as "->" |
         idtac].
Tactic Notation "val_discr_target" constr(H) :=
  first [iPoseProof (val_rel_litint_target with H) as "->" |
         iPoseProof (val_rel_litbool_target with H) as "->" |
         iPoseProof (val_rel_litfn_target with H) as "->" |
         iPoseProof (val_rel_litunit_target with H) as "->" |
         iPoseProof (val_rel_litpoison_target with H) as "->" |
         idtac].

Lemma val_rel_func `{sbijG Σ} v1 v2 v3 : val_rel v1 v2 -∗ val_rel v1 v3 -∗ ⌜v2 = v3⌝.
Proof.
  iIntros "Hv1 Hv2". iInduction v2 as [[n2 | b2 | | | l2 | f2 ] | v2_1 v2_2 | v2 | v2] "IH" forall (v1 v3); val_discr_source "Hv1"; val_discr_target "Hv2"; try done.
  - iPoseProof (val_rel_loc_source with "Hv1") as (?) "(-> & Hl1)".
    iPoseProof (val_rel_loc_target with "Hv2") as (?) "(-> & Hl2)".
    by iPoseProof (heap_bij_loc_func with "Hl1 Hl2") as "->".
  - iPoseProof (val_rel_pair_source with "Hv1") as (??) "(-> & Hv1_1 & Hv1_2)".
    iPoseProof (val_rel_pair_target with "Hv2") as (??) "(-> & Hv2_1 & Hv2_2)".
    iPoseProof ("IH" with "Hv1_1 Hv2_1") as "->".
    by iPoseProof ("IH1" with "Hv1_2 Hv2_2") as "->".
  - iPoseProof (val_rel_injl_source with "Hv1") as (?) "(-> & Hv1)".
    iPoseProof (val_rel_injl_target with "Hv2") as (?) "(-> & Hv2)".
    by iPoseProof ("IH" with "Hv1 Hv2") as "->".
  - iPoseProof (val_rel_injr_source with "Hv1") as (?) "(-> & Hv1)".
    iPoseProof (val_rel_injr_target with "Hv2") as (?) "(-> & Hv2)".
    by iPoseProof ("IH" with "Hv1 Hv2") as "->".
Qed.
Lemma val_rel_inj `{sbijG Σ} v1 v2 v3 : val_rel v2 v1 -∗ val_rel v3 v1 -∗ ⌜v2 = v3⌝.
Proof.
  iIntros "Hv1 Hv2". iInduction v2 as [[n2 | b2 | | | l2 | f2 ] | v2_1 v2_2 | v2 | v2] "IH" forall (v1 v3); val_discr_target "Hv1"; val_discr_source "Hv2"; try done.
  - iPoseProof (val_rel_loc_target with "Hv1") as (?) "(-> & Hl1)".
    iPoseProof (val_rel_loc_source with "Hv2") as (?) "(-> & Hl2)".
    by iPoseProof (heap_bij_loc_inj with "Hl1 Hl2") as "->".
  - iPoseProof (val_rel_pair_target with "Hv1") as (??) "(-> & Hv1_1 & Hv1_2)".
    iPoseProof (val_rel_pair_source with "Hv2") as (??) "(-> & Hv2_1 & Hv2_2)".
    iPoseProof ("IH" with "Hv1_1 Hv2_1") as "->".
    by iPoseProof ("IH1" with "Hv1_2 Hv2_2") as "->".
  - iPoseProof (val_rel_injl_target with "Hv1") as (?) "(-> & Hv1)".
    iPoseProof (val_rel_injl_source with "Hv2") as (?) "(-> & Hv2)".
    by iPoseProof ("IH" with "Hv1 Hv2") as "->".
  - iPoseProof (val_rel_injr_target with "Hv1") as (?) "(-> & Hv1)".
    iPoseProof (val_rel_injr_source with "Hv2") as (?) "(-> & Hv2)".
    by iPoseProof ("IH" with "Hv1 Hv2") as "->".
Qed.

(** ** Extension of the proofmode *)
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.bi Require Import bi.
Import bi.
From iris.bi Require Import derived_laws.
Import bi.
From simuliris.simplang Require Export proofmode.


(** New lemmas for the new tactics *)
Section sim.
  Context `{sbijG Σ} (val_rel : val → val → iProp Σ) (π : thread_id).
  Context {val_rel_pers : ∀ v_t v_s, Persistent (val_rel v_t v_s)}.
  Instance : sheapInv Σ := heap_bij_inv val_rel.

  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{π, val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

  Implicit Types
    (K_t K_s : ectx)
    (l_t l_s : loc)
    (v_t v_s : val)
    (e_t e_s : expr).

  Instance maybe_persistent b (P : iProp Σ) : Persistent P → Persistent (□?b P).
  Proof.
    intros Hp. destruct b; simpl; last by eauto.
    rewrite /Persistent. iIntros "#H"; eauto.
  Qed.

  Lemma tac_bij_load Δ i j b K_t K_s l_t l_s o Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    (∀ v_t v_s,
      match envs_app true (Esnoc Enil j (val_rel v_t v_s)) Δ with
      | Some Δ' =>
          envs_entails Δ' (sim_expr val_rel Φ π (fill K_t (Val v_t)) (fill K_s (Val v_s)))
      | None => False
      end) →
    envs_entails Δ (sim_expr val_rel Φ π (fill K_t (Load o (LitV l_t))) (fill K_s (Load o (LitV l_s))))%I.
  Proof using val_rel_pers.
    rewrite envs_entails_eq=> ? Hi.
    rewrite -sim_expr_bind. eapply wand_apply; first exact: sim_bij_load.
    rewrite envs_lookup_split //; simpl.
    iIntros "[#Ha He]". iSpecialize ("He" with "Ha").
    rewrite intuitionistically_if_elim. iSplitR; first done.
    iIntros (v_t' v_s') "#Hv". specialize (Hi v_t' v_s').
    destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction].
    iApply sim_expr_base.
    iApply Hi. rewrite envs_app_sound //; simpl. iApply "He"; eauto.
  Qed.

  Lemma tac_bij_store Δ i K_t K_s b l_t l_s v_t' v_s' o Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    envs_entails Δ (val_rel v_t' v_s') →
    envs_entails Δ (sim_expr val_rel Φ π (fill K_t (Val $ LitV LitUnit)) (fill K_s (Val $ LitV LitUnit))) →
    envs_entails Δ (sim_expr val_rel Φ π (fill K_t (Store o (LitV l_t) (Val v_t'))) (fill K_s (Store o (LitV l_s) (Val v_s')))).
  Proof using val_rel_pers.
    rewrite envs_entails_eq => HΔ.
    rewrite (persistent_persistently_2 (val_rel _ _)).
    intros Hv%persistently_entails_r Hi.
    rewrite -sim_expr_bind.
    iIntros "He". iPoseProof (Hv with "He") as "[He #Hv]".
    rewrite (envs_lookup_split Δ i b _ HΔ). iDestruct "He" as "[#Hbij He]".
    iSpecialize ("He" with "Hbij").
    iApply sim_bij_store; [ | done | ]. { by rewrite intuitionistically_if_elim. }
    iApply sim_expr_base. by iApply Hi.
  Qed.

  (* NOTE: we may want to actually keep the bijection assertion in context for some examples,
    where we need to use source stuckness for some runs of the target that access a deallocated location?
    In that case, change this lemma to not remove the fractional bijection assertion from the context.
    *)
  Lemma tac_bij_freeN Δ i K_t K_s b l_t l_s n Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    envs_entails (envs_delete true i b Δ) (sim_expr val_rel Φ π (fill K_t (Val $ LitV LitUnit)) (fill K_s (Val $ LitV LitUnit))) →
    envs_entails Δ (sim_expr val_rel Φ π (fill K_t (FreeN (Val $ LitV $ LitInt n) (LitV l_t))) (fill K_s (FreeN (Val $ LitV $ LitInt n) (LitV l_s)))).
  Proof using val_rel_pers.
    rewrite envs_entails_eq => Hl HΔ.
    rewrite -sim_expr_bind. rewrite (envs_lookup_sound _ _ _ _ Hl).
    iIntros "[#bij He]". iPoseProof (HΔ with "He") as "He". rewrite intuitionistically_if_elim.
    iApply sim_bij_free; first done.
    iApply sim_expr_base. by iApply "He".
  Qed.
End sim.

Tactic Notation "sim_load" ident(v_t) ident(v_s) "as" constr(H) :=
  to_sim;
  let solve_bij _ :=
    match goal with |- _ = Some (_, (?l_t ↔h ?l_s)%I) =>
      iAssumptionCore || fail "sim_load: cannot find" l_t "↔h" l_s
    end in
  let finish _ :=
    first [intros v_t v_s | fail 1 "sim_load: " v_t " or " v_s " not fresh"];
    pm_reduce; sim_finish in
  sim_pures_int;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?vrel ?Φ ?π ?e_t ?e_s) =>
    first
      [reshape_expr e_t ltac:(fun K_t e_t' =>
        reshape_expr e_s ltac:(fun K_s e_s' =>
          eapply (tac_bij_load _ _ _ _ H _ K_t K_s _ _ _)))
      |fail 1 "sim_load: cannot find 'Load' in" e_t " or " e_s];
    [ solve_bij ()
    | finish () ]
  | _ => fail "sim_load: not a 'sim'"
  end.
Tactic Notation "sim_load" ident(v_t) ident(v_s) :=
  sim_load v_t v_s as "?".

Tactic Notation "sim_store" :=
  to_sim;
  let Htmp := iFresh in
  let solve_bij _ :=
    match goal with |- _ = Some (_, (?l_t ↔h ?l_s)%I) =>
    iAssumptionCore || fail "sim_store: cannot find" l_t "↔h" l_s end in
  sim_pures_int;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?vrel ?Φ ?π ?e_t ?e_s) =>
    first
      [reshape_expr e_t ltac:(fun K_t e_t' =>
        reshape_expr e_s ltac:(fun K_s e_s' =>
          eapply (tac_bij_store _ _ _ _ K_t K_s _ _ _ _ _)))
      |fail 1 "sim_store: cannot find 'Store' in" e_t " or " e_s];
    [solve_bij ()
    | pm_reduce
    |pm_reduce; sim_finish]
  | _ => fail "sim_store: not a 'sim'"
  end.

Tactic Notation "sim_free" :=
  to_sim;
  let solve_bij _ :=
    match goal with |- _ = Some (_, (?l_t ↔h ?l_s)%I) =>
    iAssumptionCore || fail "sim_free: cannot find" l_t "↔h" l_s end in
  sim_pures_int;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?vrel ?Φ ?π ?e_t ?e_s) =>
    first
      [reshape_expr e_t ltac:(fun K_t e_t' =>
        reshape_expr e_s ltac:(fun K_s e_s' =>
          eapply (tac_bij_freeN _ _ _ _ K_t K_s _ _ _ _ _)))
      |fail 1 "sim_free: cannot find 'FreeN' in" e_t " or " e_s];
    [solve_bij ()
    |pm_reduce; sim_finish]
  | _ => fail "sim_free: not a 'sim'"
  end.
