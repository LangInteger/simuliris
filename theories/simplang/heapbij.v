From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional .
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_heap gen_sim_prog.
From simuliris.simulation Require Import slsls lifting.
From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.
From simuliris.simplang Require Export class_instances primitive_laws val_rel.

From iris.prelude Require Import options.

Lemma take_lookup_Some {A} n k (l : list A) x:
  take n l !! k = Some x ↔ l !! k = Some x ∧ k < n.
Proof.
  split.
  - destruct (decide (k < n)).
    + rewrite lookup_take; naive_solver.
    + rewrite lookup_take_ge //. lia.
  - move => [??]. by rewrite lookup_take.
Qed.


Class heapbijG (Σ : gFunctors) := HeapBijG {
  heapbijG_sheapG :> sheapGS Σ;
  heapbijG_bijG :> gset_bijG Σ block block;
  heapbijG_bij_name : gname;
}.

Section definitions.
  Context `{heapbijG Σ}.

  Definition heap_bij_auth (L : gset (block * block)) :=
    gset_bij_own_auth heapbijG_bij_name (DfracOwn 1) L.
  Definition heap_bij_elem (l_t : block) (l_s : block) :=
    gset_bij_own_elem heapbijG_bij_name l_t l_s.
End definitions.

Notation "b_t '⇔h' b_s" := (heap_bij_elem b_t b_s) (at level 30) : bi_scope.
Definition loc_rel `{heapbijG Σ} l_t l_s : iProp Σ := loc_chunk l_t ⇔h loc_chunk l_s ∗ ⌜loc_idx l_t = loc_idx l_s⌝.
Notation "l_t '↔h' l_s" := (loc_rel l_t l_s) (at level 30) : bi_scope.
Definition val_rel `{heapbijG Σ} := struct_val_rel loc_rel.

Section laws.
  Context `{heapbijG Σ}.
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

  Lemma val_rel_func v1 v2 v3 : val_rel v1 v2 -∗ val_rel v1 v3 -∗ ⌜v2 = v3⌝.
  Proof.
    iIntros "Hv1 Hv2". iInduction v2 as [[n2 | b2 | | | l2 | f2 ] | v2_1 v2_2 | v2 | v2] "IH" forall (v1 v3); val_discr_source "Hv1"; val_discr_target "Hv2"; try done.
    - iPoseProof (struct_val_rel_loc_source with "Hv1") as (?) "(-> & Hl1)".
      iPoseProof (struct_val_rel_loc_target with "Hv2") as (?) "(-> & Hl2)".
      by iPoseProof (heap_bij_loc_func with "Hl1 Hl2") as "->".
    - iPoseProof (struct_val_rel_pair_source with "Hv1") as (??) "(-> & Hv1_1 & Hv1_2)".
      iPoseProof (struct_val_rel_pair_target with "Hv2") as (??) "(-> & Hv2_1 & Hv2_2)".
      iPoseProof ("IH" with "Hv1_1 Hv2_1") as "->".
      by iPoseProof ("IH1" with "Hv1_2 Hv2_2") as "->".
    - iPoseProof (struct_val_rel_injl_source with "Hv1") as (?) "(-> & Hv1)".
      iPoseProof (struct_val_rel_injl_target with "Hv2") as (?) "(-> & Hv2)".
      by iPoseProof ("IH" with "Hv1 Hv2") as "->".
    - iPoseProof (struct_val_rel_injr_source with "Hv1") as (?) "(-> & Hv1)".
      iPoseProof (struct_val_rel_injr_target with "Hv2") as (?) "(-> & Hv2)".
      by iPoseProof ("IH" with "Hv1 Hv2") as "->".
  Qed.
  Lemma val_rel_inj v1 v2 v3 : val_rel v2 v1 -∗ val_rel v3 v1 -∗ ⌜v2 = v3⌝.
  Proof.
    iIntros "Hv1 Hv2". iInduction v2 as [[n2 | b2 | | | l2 | f2 ] | v2_1 v2_2 | v2 | v2] "IH" forall (v1 v3); val_discr_target "Hv1"; val_discr_source "Hv2"; try done.
    - iPoseProof (struct_val_rel_loc_target with "Hv1") as (?) "(-> & Hl1)".
      iPoseProof (struct_val_rel_loc_source with "Hv2") as (?) "(-> & Hl2)".
      by iPoseProof (heap_bij_loc_inj with "Hl1 Hl2") as "->".
    - iPoseProof (struct_val_rel_pair_target with "Hv1") as (??) "(-> & Hv1_1 & Hv1_2)".
      iPoseProof (struct_val_rel_pair_source with "Hv2") as (??) "(-> & Hv2_1 & Hv2_2)".
      iPoseProof ("IH" with "Hv1_1 Hv2_1") as "->".
      by iPoseProof ("IH1" with "Hv1_2 Hv2_2") as "->".
    - iPoseProof (struct_val_rel_injl_target with "Hv1") as (?) "(-> & Hv1)".
      iPoseProof (struct_val_rel_injl_source with "Hv2") as (?) "(-> & Hv2)".
      by iPoseProof ("IH" with "Hv1 Hv2") as "->".
    - iPoseProof (struct_val_rel_injr_target with "Hv1") as (?) "(-> & Hv1)".
      iPoseProof (struct_val_rel_injr_source with "Hv2") as (?) "(-> & Hv2)".
      by iPoseProof ("IH" with "Hv1 Hv2") as "->".
  Qed.
End laws.


Section definitions.
  Context `{heapbijG Σ}.

  (** We require the [lock_state]s to be the same, pointwise *)
  Definition alloc_rel b_t b_s P : iProp Σ :=
    (∃ (n : option nat) vs_t vs_s,
        ⌜length vs_t = default 0 n⌝ ∗
      ([∗ list] i↦v_t;v_s∈vs_t;vs_s,
          (∃ st q, ⌜P (Loc b_t i) (Loc b_s i) q⌝ ∗ val_rel v_t v_s ∗
                    if q is Some q' then
                      (Loc b_t i)↦t[st]{#q'} v_t ∗ (Loc b_s i)↦s[st]{#q'} v_s
                    else
                      True)) ∗
      †Loc b_t 0 …?t n ∗
      †Loc b_s 0 …?s n).

  Lemma alloc_rel_mono (P' P : _ → _ → _ → Prop) b_t b_s:
    (∀ q o, P (Loc b_t o) (Loc b_s o) q → P' (Loc b_t o) (Loc b_s o) q) →
    alloc_rel b_t b_s P -∗
    alloc_rel b_t b_s P'.
  Proof.
    iIntros (HP) "(%n&%vs_s&%vs_t&%&Hvs&?)".
    iExists _, _, _. iFrame. iSplit; [done|].
    iApply (big_sepL2_impl with "Hvs").
    iIntros "!>" (?????) "(%st&%q&%&?&?)".
    iExists _, q. iFrame. iPureIntro. by apply: HP.
  Qed.

  Lemma alloc_rel_read (b : bool) b_t b_s σ_s σ_t o v n (P : _ → _ → _ → Prop):
    heap σ_s !! Loc b_s o = Some (RSt n, v) →
    (∀ q, P (Loc b_t o) (Loc b_s o) q → ∃ q', q = Some q' ∧ if b then q' = 1%Qp else True) →
    alloc_rel b_t b_s P -∗
    heap_ctx sheapG_allocN_source (heap σ_s) (used_blocks σ_s) -∗
    heap_ctx sheapG_allocN_target (heap σ_t) (used_blocks σ_t) -∗
    ∃ n' v', ⌜heap σ_t !! Loc b_t o = Some (RSt n', v')⌝ ∗ ⌜if b then n' = n else True⌝ ∗ val_rel v' v.
  Proof.
    iIntros (? HP).
    iDestruct 1 as (? vs_t vs_s Hlen) "(Hl_s & Halloc_t & Halloc_s)".
    iIntros "Hσ_s Hσ_t".
    iDestruct (big_sepL2_length with "Hl_s") as %?.

    iDestruct (heap_freeable_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    iDestruct (big_sepL2_insert_acc with "Hl_s") as "[(%st''&%q'&%HP'&Hv&Hl_s) Hclose]"; [done..|].
    have [?[??]] := HP _ HP'. subst.
    iDestruct "Hl_s" as "[Hl_t Hl_s]".
    case_match; subst.
    - iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %Hl_s.
      iDestruct (heap_read_st_1 with "Hσ_t Hl_t") as %Hl_t.
      simplify_eq/=.
      iExists _, _. by repeat (iSplitR; [done|]).
    - iDestruct (heap_read_st with "Hσ_s Hl_s") as %[? Hl_s].
      iDestruct (heap_read_st with "Hσ_t Hl_t") as %[? Hl_t].
      destruct st''; simplify_eq/=.
      iExists _, _. by repeat (iSplitR; [done|]).
  Qed.

  Lemma alloc_rel_write b_t b_s σ_s σ_t o v st st' v_s' v_t' (P : _ → _ → _ → Prop):
    heap σ_s !! Loc b_s o = Some (st, v) →
    (∀ q, P (Loc b_t o) (Loc b_s o) q → q = Some 1%Qp) →
    alloc_rel b_t b_s P -∗
    heap_ctx sheapG_allocN_source (heap σ_s) (used_blocks σ_s) -∗
    heap_ctx sheapG_allocN_target (heap σ_t) (used_blocks σ_t) -∗
    val_rel v_t' v_s' ==∗
    alloc_rel b_t b_s P ∗
    heap_ctx sheapG_allocN_source (<[Loc b_s o := (st', v_s')]> (heap σ_s)) (used_blocks σ_s) ∗
    heap_ctx sheapG_allocN_target (<[Loc b_t o := (st', v_t')]> (heap σ_t)) (used_blocks σ_t).
  Proof.
    iIntros (? HP).
    iDestruct 1 as (n vs_t vs_s Hlen) "(Hl_s & Halloc_t & Halloc_s)".
    iIntros "Hσ_s Hσ_t Hval".
    iDestruct (big_sepL2_length with "Hl_s") as %?.

    iDestruct (heap_freeable_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    iDestruct (big_sepL2_insert_acc with "Hl_s") as "[(%st''&%q'&%HP'&Hv'&Hl_s) Hclose]"; [done..|].
    have ? := HP _ HP'. subst.
    iDestruct "Hl_s" as "[Hl_t Hl_s]".
    iDestruct (heap_read_st_1 with "Hσ_s Hl_s") as %Hl_s.
    iDestruct (heap_read_st_1 with "Hσ_t Hl_t") as %Hl_t.
    simplify_eq/=.

    iMod (heap_write with "Hσ_s Hl_s") as "[$ Hl_s]".
    iMod (heap_write with "Hσ_t Hl_t") as "[$ Hl_t]".
    iModIntro.
    iExists _, _, _.
    iFrame "Halloc_t Halloc_s".
    iSplitR; last first.
    - iApply "Hclose". iExists _, (Some _). by iFrame.
    - iPureIntro. rewrite insert_length. lia.
  Qed.

  Lemma alloc_rel_P_holds (P : _ → _ → _ → Prop) b_t b_s σ_s o s:
    heap σ_s !! Loc b_s o = Some s →
    alloc_rel b_t b_s P -∗
    heap_ctx sheapG_allocN_source (heap σ_s) (used_blocks σ_s) -∗
    ⌜∃ q, P (Loc b_t o) (Loc b_s o) q⌝%Qp.
  Proof.
    iIntros (?).
    iDestruct 1 as (? vs_t vs_s Hlen) "(Hl_s & Halloc_t & Halloc_s)".
    iIntros "Hσ_s".
    iDestruct (big_sepL2_length with "Hl_s") as %?.

    iDestruct (heap_freeable_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    iDestruct (big_sepL2_insert_acc with "Hl_s") as "[(%st''&%q'&%HP'&Hl_s) _]"; [done..|].
    iPureIntro. naive_solver.
  Qed.

  Lemma alloc_rel_remove_frac (P' P : _ → _ → _ → Prop) q1 q2 qd b_t b_s σ_s o v_s st:
    heap σ_s !! Loc b_s o = Some (RSt st, v_s) →
    (∀ q, P (Loc b_t o) (Loc b_s o) q → q = Some q1) →
    P' (Loc b_t o) (Loc b_s o) q2 →
    (∀ q o', o ≠ o' → P (Loc b_t o') (Loc b_s o') q → P' (Loc b_t o') (Loc b_s o') q) →
    (if q2 is Some q2' then q1 = qd + q2' else q1 = qd)%Qp →
    (q2 = None → st = 0) →
    alloc_rel b_t b_s P -∗
    heap_ctx sheapG_allocN_source (heap σ_s) (used_blocks σ_s)
    ==∗
    ∃ v_t,
      (Loc b_t o)↦t{#qd}v_t ∗
      (Loc b_s o)↦s{#qd}v_s ∗
      val_rel v_t v_s ∗
      alloc_rel b_t b_s P' ∗
      heap_ctx sheapG_allocN_source (heap σ_s) (used_blocks σ_s).
  Proof.
    iIntros (? Hq1 Hq2 Hsame Hdiff Hst0).
    iDestruct 1 as (n vs_t vs_s Hlen) "(Hvs & Halloc_t & Halloc_s)".
    iIntros "Hσ_s".
    iDestruct (big_sepL2_length with "Hvs") as %?.

    iDestruct (heap_freeable_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s' Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    have Hv_s':= take_drop_middle _ _ _ Hv_s.
    have Hv_t':= take_drop_middle _ _ _ Hv_t.
    rewrite -{1}Hv_s' -{1}Hv_t' big_sepL2_app_same_length /= ?take_length_le ?Nat.add_0_r; [|lia..].
    iDestruct "Hvs" as "(Hvs_1&Hl&Hvs_2)".
    iDestruct "Hl" as (st' q ?%Hq1) "[#Hv Hp]". subst.
    iDestruct "Hp" as "[Hl_t Hl_s]".
    iDestruct (heap_read_st with "Hσ_s Hl_s") as %[??]; destruct st' as [|n'']; simplify_eq/=.

    destruct q2; subst.
    - iDestruct (heap_mapsto_split _ _ _ _ 0 with "Hl_t") as "[Hl_t1 Hl_t2]"; [done..|].
      iDestruct (heap_mapsto_split _ _ _ _ 0 with "Hl_s") as "[Hl_s1 Hl_s2]"; [done..|].
      iModIntro.
      iExists _. iFrame "∗Hv".
      iExists _, vs_t, vs_s. iFrame. iSplit; [done|].
      rewrite -{3}Hv_s' -{3}Hv_t' big_sepL2_app_same_length /= ?take_length_le ?Nat.add_0_r; [|lia..].
      iSplitL "Hvs_1"; [|iSplitR "Hvs_2"].
      + iApply (big_sepL2_impl with "Hvs_1").
        iIntros "!>" (??? ?%take_lookup_Some ?%take_lookup_Some) "[%s [%q' [% Hp]]]".
        iExists s, q'. iFrame. iPureIntro.
        apply: Hsame; [lia| done].
      + iExists _, _. iSplit; [done|]. by iFrame.
      + iApply (big_sepL2_impl with "Hvs_2").
        iIntros "!>" (??? ??) "[%s [%q' [% Hp]]]".
        iExists s, q'. iFrame. iPureIntro.
        apply: Hsame; [lia |done].
    - have ->: n'' = 0 by naive_solver lia.
      iModIntro.
      iExists _. iFrame "∗Hv".
      iExists _, vs_t, vs_s. iFrame. iSplit; [done|].
      rewrite -{3}Hv_s' -{3}Hv_t' big_sepL2_app_same_length /= ?take_length_le ?Nat.add_0_r; [|lia..].
      iSplitL "Hvs_1"; [|iSplitR "Hvs_2"].
      + iApply (big_sepL2_impl with "Hvs_1").
        iIntros "!>" (??? ?%take_lookup_Some ?%take_lookup_Some) "[%s [%q' [% Hp]]]".
        iExists s, q'. iFrame. iPureIntro.
        apply: Hsame; [lia|done].
      + iExists _, _. iSplit; [done|] => /=. iFrame "Hv".
      + iApply (big_sepL2_impl with "Hvs_2").
        iIntros "!>" (??? ??) "[%s [%q' [% Hp]]]".
        iExists s, q'. iFrame. iPureIntro.
        apply: Hsame; [lia|done].
        Unshelve.
        apply: WSt.
  Qed.

  Lemma alloc_rel_add_frac (P' P : _ → _ → _ → Prop) q b_t b_s σ_s o v_s v_t:
    (∀ q', P (Loc b_t o) (Loc b_s o) q' → P' (Loc b_t o) (Loc b_s o) (Some (if q' is Some q'' then (q + q'')%Qp else q))) →
    (∀ q o', o ≠ o' → P (Loc b_t o') (Loc b_s o') q → P' (Loc b_t o') (Loc b_s o') q) →
    alloc_rel b_t b_s P -∗
    (Loc b_t o)↦t{#q}v_t -∗
    (Loc b_s o)↦s{#q}v_s -∗
    val_rel v_t v_s -∗
    heap_ctx sheapG_allocN_source (heap σ_s) (used_blocks σ_s)
    ==∗
      alloc_rel b_t b_s P' ∗
      heap_ctx sheapG_allocN_source (heap σ_s) (used_blocks σ_s).
  Proof.
    iIntros (Hq Hsame).
    iDestruct 1 as (n vs_t vs_s Hlen) "(Hvs & Halloc_t & Halloc_s)".
    iIntros "Hl_t Hl_s Hv Hσ_s".
    iDestruct (big_sepL2_length with "Hvs") as %?.

    iDestruct (heap_read with "Hσ_s Hl_s") as %[??].
    iDestruct (heap_freeable_lookup with "Hσ_s Halloc_s") as %[n' [? Hl]]; [done..|].
    rewrite Loc_add in Hl. move: Hl => [] ?; simplify_eq/=.
    have [v_s' Hv_s]:= lookup_lt_is_Some_2 vs_s n' ltac:(lia).
    have [v_t' Hv_t]:= lookup_lt_is_Some_2 vs_t n' ltac:(lia).
    have Hv_s':= take_drop_middle _ _ _ Hv_s.
    have Hv_t':= take_drop_middle _ _ _ Hv_t.
    rewrite -{1}Hv_s' -{1}Hv_t' big_sepL2_app_same_length /= ?take_length_le ?Nat.add_0_r; [|lia..].
    iDestruct "Hvs" as "(Hvs_1&Hl&Hvs_2)".
    iDestruct "Hl" as (st' q' ?) "[Hv' Hp]". subst.

    iModIntro. iFrame.
    iExists n, (<[n' := v_t]>vs_t), (<[n' := v_s]>vs_s).
    iSplit. { by rewrite insert_length. } iFrame.
    rewrite !insert_take_drop; [|by apply: lookup_lt_Some..].
    rewrite big_sepL2_app_same_length /= ?take_length_le ?Nat.add_0_r; [|lia..]. iFrame.
    iSplitL "Hvs_1"; [|iSplitR "Hvs_2"].
    - iApply (big_sepL2_impl with "Hvs_1").
      iIntros "!>" (??? ?%take_lookup_Some ?%take_lookup_Some) "[%s [%q'' [% Hp]]]".
      iExists s, q''. iFrame. iPureIntro.
      apply: Hsame; [lia| done].
    - iExists (if q' then st' else RSt 0), (Some (if q' is Some q'' then q + q'' else q))%Qp.
      iSplit; first by eauto.
      destruct q'; iFrame.
      iDestruct "Hp" as "[Hp1 Hp2]".
      iDestruct (heap_mapsto_agree with "[$Hp1 $Hl_t]") as %->.
      iDestruct (heap_mapsto_agree with "[$Hp2 $Hl_s]") as %->.
      iDestruct (heap_mapsto_combine_0 with "Hl_t Hp1") as "$".
      iDestruct (heap_mapsto_combine_0 with "Hl_s Hp2") as "$".
    - iApply (big_sepL2_impl with "Hvs_2").
      iIntros "!>" (??? ??) "[%s [%q'' [% Hp]]]".
      iExists s, q''. iFrame. iPureIntro.
      apply: Hsame; [lia |done].
  Qed.

  Definition heap_bij_interp (L : gset (block * block)) (P : loc → loc → option Qp → Prop)  :=
    (heap_bij_auth L ∗ [∗ set] p ∈ L, let '(b_t, b_s) := p in alloc_rel b_t b_s P)%I.
End definitions.

Section laws.
  Context `{heapbijG Σ}.
  Implicit Types (b_t b_s : block) (l_t l_s : loc).

  Lemma heap_bij_access L P b_t b_s:
    heap_bij_interp L P -∗
    b_t ⇔h b_s -∗
    ⌜(b_t, b_s) ∈ L⌝ ∗
    alloc_rel b_t b_s P ∗
    (∀ P' : _ → _ → _  → Prop,
        ⌜∀ b_t' b_s' o q, b_t' ≠ b_t → b_s' ≠ b_s → P (Loc b_t' o) (Loc b_s' o) q →
                           P' (Loc b_t' o) (Loc b_s' o) q⌝ -∗
        (* ⌜∀ π col l_s w, cols' !! π = Some col → col !! l_s = Some w → loc_chunk l_s = b_s ∨ ∃ col' w', cols !! π = Some col' ∧ col' !! l_s = Some  w'⌝ -∗ *)
        (* ⌜∀ b' o' q, b' ≠ b_s → alloc_rel_pred cols (Loc b' o') q → alloc_rel_pred cols' (Loc b' o') q⌝ -∗ *)
        alloc_rel b_t b_s P' -∗ heap_bij_interp L P').
  Proof.
    iIntros "Hinv Hrel". iDestruct "Hinv" as "(Hauth & Hheap)".
    iDestruct (gset_bij_elem_of with "Hauth Hrel") as %Hin.
    iPoseProof (big_sepS_delete with "Hheap") as "[He Hheap]"; first done.
    iDestruct (gset_bij_own_valid with "Hauth") as %[_ Hbij].
    iFrame. iSplit; [done|].
    iIntros (P' HP) "Halloc". iFrame.
    iApply big_sepS_delete; first done. iFrame.
    iApply (big_sepS_impl with "Hheap").
    iIntros "!>" ([??] ?) "Halloc".
    iApply (alloc_rel_mono with "Halloc") => ?? /=.
    set_unfold. destruct H0 as [Hin2 Hneq].
    have ?:= gset_bijective_eq_iff _ _ _ _ _ _ Hin Hin2.
    apply: HP => b'; naive_solver.
  Qed.

  Lemma heap_bij_insertN L l_t l_s v_t v_s n (P : _ → _ → _ → Prop):
    n > 0 →
    length v_s = n →
    length v_t = n →
    (∀ o, (∀ b_s, (loc_chunk l_t, b_s) ∉ L) →
          (∀ b_t, (b_t, loc_chunk l_s) ∉ L) → P (l_t +ₗ o) (l_s +ₗ o) (Some 1%Qp)) →
    heap_bij_interp L P -∗
    l_t ↦t∗ v_t -∗
    l_s ↦s∗ v_s -∗
    ([∗ list] vt;vs∈v_t;v_s, val_rel vt vs) -∗
    †l_t …t n -∗
    †l_s …s n ==∗
    heap_bij_interp ({[(loc_chunk l_t, loc_chunk l_s)]} ∪ L) P ∗
    l_t ↔h l_s.
  Proof.
    iIntros (Hn Hl_s Hl_t HP) "Hinv Ht Hs Hrel Ha_t Ha_s".
    iDestruct (heap_freeable_idx with "Ha_t") as %?.
    iDestruct (heap_freeable_idx with "Ha_s") as %?.
    iDestruct "Hinv" as "(Hauth & Hheap)".
    pose (b_t := loc_chunk l_t). pose (b_s := loc_chunk l_s).
    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), b_t = b_t') L⌝)%I) as "%Hext_t".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (n' v_t' v_s') "(_ & _ & Ha_t' & _)".
      by iApply (heap_freeable_excl with "Ha_t Ha_t'").
    }
    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), b_s = b_s') L⌝)%I) as "%Hext_s".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (n' v_t' v_s') "(_ & _ & _ & Ha_s')".
      by iApply (heap_freeable_excl with "Ha_s Ha_s'").
    }
    iMod ((gset_bij_own_extend b_t b_s) with "Hauth") as "[Hinv #Helem]".
    - intros b_s' Hb_s'. apply Hext_t. by exists (b_t, b_s').
    - intros b_t' Hb_t'. apply Hext_s. by exists (b_t', b_s).
    - iModIntro.
      iSplitL; first last. { iSplitL; first done. iPureIntro; lia. }
      iFrame. iApply big_sepS_insert. { contradict Hext_t. by exists (b_t, b_s). }
      iFrame. iExists (Some n), v_t, v_s. iFrame.
      destruct l_t, l_s; cbn in *; subst. iFrame.
      iSplit; [done|].
      iDestruct (big_sepL2_sepL_2 with "Ht Hs") as "Hvs"; [done|].
      iCombine "Hrel" "Hvs" as "Hvs". rewrite -big_sepL2_sep.
      iApply (big_sepL2_impl with "Hvs").
      iIntros "!>" (?????) "(Hv&Ht&Hs)". iExists _, (Some 1%Qp). iFrame.
      iPureIntro. apply HP => ??.
      + apply: Hext_t. eexists _. naive_solver.
      + apply: Hext_s. eexists _. naive_solver.
  Qed.
End laws.
