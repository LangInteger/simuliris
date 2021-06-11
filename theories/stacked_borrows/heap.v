(** This file provides the basic heap and ghost state support for the BorIngLang program logic. *)
From iris.proofmode Require Export tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From iris.prelude Require Import options.
From simuliris.stacked_borrows Require Import tkmap_view.
From simuliris.stacked_borrows Require Export defs.
From simuliris.stacked_borrows Require Import steps_progress steps_retag.

Fixpoint heap_array (l : loc) (scs : list scalar) : gmap loc scalar :=
  match scs with
  | [] => ∅
  | sc :: scs' => {[l := sc]} ∪ heap_array (l +ₗ 1) scs'
  end.

Lemma heap_array_singleton l sc : heap_array l [sc] = {[l := sc]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l scs sc k :
  heap_array l scs !! k = Some sc ↔
  ∃ j, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ scs !! (Z.to_nat j) = Some sc.
Proof.
  revert k l; induction scs as [|sc' scs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ->] | (Hl & j & ? & -> & ?)].
    { eexists 0. rewrite shift_loc_0. naive_solver lia. }
    eexists (1 + j)%Z. rewrite shift_loc_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite shift_loc_0; eauto. }
    right. split.
    { rewrite -{1}(shift_loc_0 l). intros ?%(inj (shift_loc _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z. rewrite shift_loc_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc scalar) (l : loc) (scs : list scalar) :
  (∀ i, (0 ≤ i)%Z → (i < length scs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l scs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&?&->&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

Lemma lookup_free_mem_1 l l' n σ :
  l.1 ≠ l'.1 → (free_mem l n σ) !! l' = σ !! l'.
Proof.
  induction n as [ | n IH] in l |-*; cbn; first done.
  intros Hneq. rewrite lookup_delete_ne; last by congruence.
  by apply IH.
Qed.
Lemma lookup_free_mem_2 l l' (n : nat) σ :
  l.1 = l'.1 → (l.2 ≤ l'.2 < l.2 + n)%Z → (free_mem l n σ) !! l' = None.
Proof.
  induction n as [ | n IH] in l |-*; cbn; first lia.
  intros Hchunk Hi.
  destruct (decide (l.2 = l'.2)) as [Heq | Hneq].
  - rewrite lookup_delete_None; left. destruct l, l'; simpl in *; congruence.
  - rewrite lookup_delete_ne; last congruence. apply IH; first done. destruct l, l'; simpl in *; lia.
Qed.
Lemma lookup_free_mem_3 l l' (n : nat) σ :
  l.1 = l'.1 → (l'.2 < l.2)%Z → (free_mem l n σ) !! l' = σ !! l'.
Proof.
  induction n as [ | n IH] in l |-*; cbn; first done.
  intros Hchunk Hi. rewrite lookup_delete_ne.
  - apply IH; first done. destruct l, l'; cbn in *; lia.
  - destruct l, l'; cbn in *; intros [=]. lia.
Qed.
Lemma lookup_free_mem_4 l l' (n : nat) σ :
  l.1 = l'.1 → (l'.2 >= l.2 + n)%Z → (free_mem l n σ) !! l' = σ !! l'.
Proof.
  induction n as [ | n IH] in l |-*; cbn; first done.
  intros Hchunk Hi. rewrite lookup_delete_ne.
  - apply IH; first done. destruct l, l'; cbn in *; lia.
  - destruct l, l'; cbn in *; intros [=]. lia.
Qed.

Lemma delete_free_mem σ l n o:
  (o > 0)%Z →
  delete l (free_mem (l +ₗ o) n σ) = free_mem (l +ₗ o) n (delete l σ).
Proof.
  intros HO.
  induction n as [|n IH] in o, HO|-* => //=. rewrite delete_commute. f_equal.
  rewrite shift_loc_assoc IH; [done | lia].
Qed.

(* maintain for each tag: the permissions (public or unique) and, optionally, the
    regions of memory maintained by it: base locations for target and source, and the length of the maintained allocation.
*)
Class bor_stateG Σ := {
  (* Maintaining the stack & scalar for each location *)
  (*heap_inG :> ghost_mapG Σ loc (scalar * stack);*)
  (*heap_source_name : gname;*)
  (*heap_target_name : gname;*)

  (* Maintaining the locations protected by each call id *)
  call_inG :> ghost_mapG Σ call_id (gmap ptr_id (gset loc));
  call_name : gname;

  (* tag ownership *)
  tag_inG :> tkmapG Σ ptr_id unit;
  tag_name : gname;

  (* A view of parts of the heap, conditional on the ptr_id *)
  heap_view_inG :> ghost_mapG Σ (ptr_id * loc) scalar;
  heap_view_source_name : gname;
  heap_view_target_name : gname;
}.

Section mem_bijection.
  Context {Σ} `{bor_stateG Σ}.

  (* The bijection serves the following purpose:
      * the blocks are of the same size
      * the stacks for the locations are pointwise the same
      * every location is either a private location or a public location, which is tied to the tag ghost state
  *)
  Context (sc_rel : scalar → scalar → iProp Σ).

  Section defs.
  (* We need all the maps from the tag interpretation here....
     TODO: can we make that more beautiful? all the different invariants are interleaved in subtle ways, which makes modular reasoning really hard... *)
    Context (M_tag : gmap ptr_id (tag_kind * unit)) (M_t M_s : gmap (ptr_id * loc) scalar) (Mcall_t : gmap call_id (gmap ptr_id (gset loc))).


    Definition call_set_in (M : gmap ptr_id (gset loc)) t l :=
      ∃ L, M !! t = Some L ∧ l ∈ L.
    Definition call_set_in' (M : gmap call_id (gmap ptr_id (gset loc))) c t l :=
      ∃ M', M !! c = Some M' ∧ call_set_in M' t l.
    Definition pub_loc σ_t σ_s (l : loc) : iProp Σ :=
      ∀ sc_t, ⌜σ_t.(shp) !! l = Some sc_t⌝ → ∃ sc_s, ⌜σ_s.(shp) !! l = Some sc_s⌝ ∗ sc_rel sc_t sc_s.
    Definition priv_loc t (l : loc) : Prop :=
      ∃ tk, M_tag !! t = Some (tk, tt) ∧ is_Some (M_t !! (t, l)) ∧
        (* local *)
        (tk = tk_local ∨
        (* unique with protector *)
        (tk = tk_unq ∧ ∃ c, call_set_in' Mcall_t c t l)).

    (* This definition enforces quite strict requirements on the state:
      - the domains of the heaps shp are the same
      - the stacks are the same
      - the call counter is the same
      - the tag counter is the same
      - the set of ongoing calls is the same
      - there's a relation on the scalars stored at locations ([pub_loc]), except when the location is currently controlled by a tag ([priv_loc]).

      Note that, while the definition may appear asymmetric in source and target, due to the well-formedness on states [state_wf] and the relation of the tag maps enforced below, it really is symmetric in practice.
    *)
    Definition state_rel σ_t σ_s : iProp Σ :=
        ⌜dom (gset loc) σ_s.(shp) = dom (gset loc) σ_t.(shp)⌝ ∗
        ⌜σ_s.(sst) = σ_t.(sst)⌝ ∗
        ⌜σ_s.(snp) = σ_t.(snp)⌝ ∗
        ⌜σ_s.(snc) = σ_t.(snc)⌝ ∗
        ⌜σ_s.(scs) = σ_t.(scs)⌝ ∗
        (* private / public locations of the target *)
        ∀ l, ⌜is_Some (σ_t.(shp) !! l)⌝ → pub_loc σ_t σ_s l ∨ ⌜∃ t, priv_loc t l⌝.

    Global Instance state_rel_persistent σ_t σ_s `{∀ sc_t sc_s, Persistent (sc_rel sc_t sc_s)} :
      Persistent (state_rel σ_t σ_s).
    Proof. intros. apply _. Qed.

  End defs.
End mem_bijection.

Section bijection_lemmas.
  Context {Σ} `{bor_stateG Σ}.
  Context (sc_rel : scalar → scalar → iProp Σ).
  Local Notation state_rel := (state_rel sc_rel).

  Lemma state_rel_get_pure Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜σ_s.(sst) = σ_t.(sst) ∧ σ_s.(snp) = σ_t.(snp) ∧ σ_s.(snc) = σ_t.(snc) ∧ σ_s.(scs) = σ_t.(scs)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
  Lemma state_rel_stacks_eq Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜σ_s.(sst) = σ_t.(sst)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
  Lemma state_rel_snp_eq Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜σ_s.(snp) = σ_t.(snp)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
  Lemma state_rel_snc_eq Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜σ_s.(snc) = σ_t.(snc)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
  Lemma state_rel_calls_eq Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜σ_s.(scs) = σ_t.(scs)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.
  Lemma state_rel_dom_eq Mtag Mt Mcall σ_t σ_s :
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜dom (gset loc) σ_t.(shp) = dom (gset loc) σ_s.(shp)⌝.
  Proof. iIntros "(% & % & % & % & % & ?)". eauto. Qed.

  (*Lemma heap_bij_interp_alloc L t : *)
    (*(∀ b_s, (b_t, b_s) ∉ L) →*)
    (*heap_bij_interp sc_rel M_tag M_t Mcall_t L σ_t σ_s -∗*)
    (*heap_bij_interp sc_rel M_tag (Minit_mem ) Mcall_t L (state_upd_mem (init_mem (b_t, 0) n) σ_t)*)

  Lemma state_rel_upd_pub_both M_tag M_t Mcall_t σ_t σ_s l sc_t sc_s :
    sc_rel sc_t sc_s -∗
    state_rel M_tag M_t Mcall_t σ_t σ_s -∗
    state_rel M_tag M_t Mcall_t (state_upd_mem (<[l := sc_t]>) σ_t) (state_upd_mem (<[l := sc_s]>) σ_s).
  Proof.
    iIntros "Hs (%Hshp & % & % & % & % & Hrel)". rewrite /state_rel /=.
    iSplitR. { iPureIntro. by rewrite !dom_insert_L Hshp. }
    do 4 (iSplitR; first done).
    iIntros (l') "%Hsome". destruct (decide (l = l')) as [<- | Hneq].
    - iLeft. iIntros (sc_t') "%Hsc_t'". iExists sc_s.
      iSplitR. { iPureIntro. by rewrite lookup_insert. }
      move :Hsc_t'; rewrite lookup_insert => [= <-] //.
    - rewrite lookup_insert_ne in Hsome; last done.
      iDestruct ("Hrel" $! l' with "[//]") as "[Hpub | Hpriv]".
      + iLeft. iIntros (sc_t'). rewrite !lookup_insert_ne; [ | done | done]. iApply "Hpub".
      + iRight. done.
  Qed.

  Lemma priv_loc_upd_insert Mtag Mt Mcall t l t' l' sc :
    priv_loc Mtag Mt Mcall t l →
    priv_loc Mtag (<[(t',l') := sc]> Mt) Mcall t l.
  Proof.
    rewrite /priv_loc. intros (tk & Ht & Hs & Hinv). exists tk.
    split_and!; [ done | | done].
    apply lookup_insert_is_Some. destruct (decide ((t', l') = (t, l))); eauto.
  Qed.

  Lemma state_rel_upd_priv_target M_tag M_t Mcall σ_t σ_s l t sc :
    is_Some (σ_t.(shp) !! l) →
    priv_loc M_tag M_t Mcall t l →
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    state_rel M_tag (<[(t, l) := sc]> M_t) Mcall (state_upd_mem (<[l := sc]>) σ_t) σ_s.
  Proof.
    iIntros (Hs Hpriv) "(%Hshp & % & % & % & % & Hrel)". rewrite /state_rel /=.
    iSplitR. { iPureIntro. rewrite dom_insert_lookup_L; done. }
    do 4 (iSplitR; first done).
    iIntros (l') "%Hsome". destruct (decide (l = l')) as [<- | Hneq].
    - iRight. iExists t. iPureIntro. apply priv_loc_upd_insert. done.
    - rewrite lookup_insert_ne in Hsome; last done.
      iDestruct ("Hrel" $! l' with "[//]") as "[Hpub | %Hpriv']".
      + iLeft. iIntros (sc_t'). rewrite !lookup_insert_ne; [ | done ]. iApply "Hpub".
      + iRight. iPureIntro. destruct Hpriv' as (t' & Hpriv'). exists t'.
        by eapply priv_loc_upd_insert.
  Qed.

  Lemma state_rel_upd_priv_source M_tag M_t Mcall σ_t σ_s l t sc :
    ⌜is_Some (σ_t.(shp) !! l)⌝ -∗
    ⌜priv_loc M_tag M_t Mcall t l⌝ -∗
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    state_rel M_tag M_t Mcall σ_t (state_upd_mem (<[l := sc]>) σ_s).
  Proof.
    iIntros (Hs Hpriv) "(%Hshp & % & % & % & % & Hrel)". rewrite /state_rel /=.
    iSplitR. { iPureIntro. rewrite dom_insert_lookup_L; [ by rewrite Hshp| ].
      rewrite lookup_lookup_total_dom; first by eauto.
      rewrite Hshp. by apply elem_of_dom.
    }
    do 4 (iSplitR; first done).
    iIntros (l') "%Hsome". destruct (decide (l = l')) as [<- | Hneq].
    - iRight. iExists t. done.
    - iDestruct ("Hrel" $! l' with "[//]") as "[Hpub | %Hpriv']".
      + iLeft. iIntros (sc_t'). rewrite !lookup_insert_ne; [ | done ]. iApply "Hpub".
      + iRight. iPureIntro. destruct Hpriv' as (t' & Hpriv'). exists t'. done.
  Qed.

  Lemma state_rel_pub_if_not_priv M_tag M_t Mcall σ_t σ_s l :
    ⌜is_Some (σ_t.(shp) !! l)⌝ -∗
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    ⌜∀ t, ¬ priv_loc M_tag M_t Mcall t l⌝ -∗
    pub_loc sc_rel σ_t σ_s l.
  Proof.
    iIntros (Hs) "(%& % & % & % & % & Hrel) %Hnpriv".
    iPoseProof ("Hrel" $! l with "[//]") as "[Hpub | %Hpriv]"; first done.
    destruct Hpriv as (t & Hpriv). exfalso; by eapply Hnpriv.
  Qed.

  Lemma state_rel_heap_lookup_Some M_tag M_t Mcall σ_t σ_s :
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    ∀ l, ⌜is_Some (σ_t.(shp) !! l)⌝ ↔ ⌜is_Some (σ_s.(shp) !! l)⌝.
  Proof.
    iIntros "(%Hshp & _)". iPureIntro. move => l. cbn. by rewrite -!elem_of_dom Hshp.
  Qed.

  Lemma state_rel_pub_or_priv M_tag M_t Mcall σ_t σ_s l :
    ⌜is_Some (σ_t.(shp) !! l)⌝ -∗
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    pub_loc sc_rel σ_t σ_s l ∨ ⌜∃ t, priv_loc M_tag M_t Mcall t l⌝.
  Proof.
    iIntros "Hsome Hstate". iDestruct "Hstate" as "(_ & _ & _ & _ & _ & Hl)".
    by iApply "Hl".
  Qed.

  Lemma pub_loc_lookup σ_t σ_s l :
    ⌜is_Some (σ_t.(shp) !! l)⌝ -∗
    pub_loc sc_rel σ_t σ_s l -∗
    ∃ sc_t sc_s, ⌜σ_t.(shp) !! l = Some sc_t ∧ σ_s.(shp) !! l = Some sc_s⌝ ∗ sc_rel sc_t sc_s.
  Proof.
    iIntros (Hs) "Hpub". destruct Hs as (sc_t & Ht).
    iDestruct ("Hpub" $! sc_t with "[//]") as (sc_s) "[%Hs Hsc]".
    iExists sc_t, sc_s. eauto.
  Qed.

End bijection_lemmas.

(* Interpretation for call ids *)
Section call_defs.
  Context {Σ} (call_gname : gname) {call_inG : ghost_mapG Σ (call_id) (gmap ptr_id (gset loc))}.

  Implicit Types (c : call_id) (pid : ptr_id) (pm : permission).

  Definition call_set_is (c : call_id) (M : gmap ptr_id (gset loc)) :=
    ghost_map_elem call_gname c (DfracOwn 1) M.

  (* This does not assert ownership of the authoritative part. Instead, this is owned by bor_interp below. *)
  Definition call_set_interp (M : gmap call_id (gmap ptr_id (gset loc))) (σ : state) : Prop :=
    ∀ c (M' : gmap ptr_id (gset loc)), M !! c = Some M' →
      c ∈ σ.(scs) ∧
      (* for every ptr_id *)
      ∀ pid (S : gset loc), M' !! pid = Some S →
        (pid < σ.(snp))%nat ∧
        (* for every protected location [l], there needs to be a protector in the stack *)
        ∀ (l : loc), l ∈ S → ∃ s pm, σ.(sst) !! l = Some s ∧
          mkItem pm (Tagged pid) (Some c) ∈ s ∧ pm ≠ Disabled.

  Definition loc_protected_by σ t l c :=
    c ∈ σ.(scs) ∧ (t < σ.(snp))%nat ∧ ∃ stk pm, σ.(sst) !! l = Some stk ∧
      mkItem pm (Tagged t) (Some c) ∈ stk ∧ pm ≠ Disabled.
  Lemma call_set_interp_access M σ c t l :
    call_set_interp M σ →
    call_set_in' M c t l →
    loc_protected_by σ t l c.
  Proof.
    intros Hinterp (M' & HM_some & L & HM'_some & Hin).
    specialize (Hinterp _ _ HM_some) as (? & Hinterp).
    specialize (Hinterp _ _ HM'_some) as (? & Hinterp).
    specialize (Hinterp _ Hin). done.
  Qed.

  Lemma call_set_interp_remove c M σ :
    call_set_interp M σ →
    call_set_interp (delete c M) (state_upd_calls (.∖ {[c]}) σ).
  Proof.
    intros Hinterp c' M' Hsome. destruct (decide (c' = c)) as [-> | Hneq].
    { rewrite lookup_delete in Hsome. done. }
    rewrite lookup_delete_ne in Hsome; last done.
    apply Hinterp in Hsome as (Hin & Hpid).
    split.
    { destruct σ; cbn in *. apply elem_of_difference; split; first done. by apply not_elem_of_singleton. }
    intros t S HS.
    apply Hpid in HS as (Ht & Hlookup). split; first by destruct σ.
    intros l Hl. apply Hlookup in Hl as (s & pm & Hsst & Hs & Hpm).
    exists s, pm. split_and!; [ | done..]. by destruct σ.
  Qed.

End call_defs.

Notation "c '@@' M" := (call_set_is call_name c M) (at level 50).


(* Interpretation for heap assertions under control of tags
    The interpretation of the tag map and the "heap view" fragments are interlinked.
 *)
Section heap_defs.
  (** The assumption on the location still being valid for tag [t], i.e., [t] not being disabled. *)
  (* Note: That the stack is still there needs to be part of the precondition [bor_state_pre].
        Otherwise, we will not be able to prove reflexivity for deallocation:
          that needs to be able to remove stacks from the state without updating all the ghost state that may still make assumptions about it.
  *)

  Definition bor_state_pre (l : loc) (t : ptr_id) (tk : tag_kind) (σ : state) :=
    match tk with
    | tk_local => True
    | _ => ∃ st pm pro, σ.(sst) !! l = Some st ∧
        mkItem pm (Tagged t) pro ∈ st ∧ pm ≠ Disabled
    end.

  Lemma loc_protected_bor_state_pre l t c σ tk :
    loc_protected_by σ t l c → bor_state_pre l t tk σ.
  Proof.
    intros (_ & _ & (stk & pm & ?)). destruct tk; [| | done]; rewrite /bor_state_pre; eauto.
  Qed.

  Definition bor_state_own (l : loc) (t : ptr_id) (tk : tag_kind) (σ : state) :=
    match tk with
    | tk_local => σ.(sst) !! l = Some ([mkItem Unique (Tagged t) None])
    | tk_unq => ∃ st, σ.(sst) !! l = Some st ∧ ∃ opro st',
        st = mkItem Unique (Tagged t) opro :: st'
    | tk_pub => ∃ st, σ.(sst) !! l = Some st ∧ t ∈ active_SRO st
    end.

  Lemma bor_state_own_some_stack l t tk σ :
    bor_state_own l t tk σ → ∃ stk, σ.(sst) !! l = Some stk.
  Proof. rewrite /bor_state_own. destruct tk; naive_solver. Qed.

  Definition loc_controlled (l : loc) (t : ptr_id) (tk : tag_kind) (sc : scalar) (σ : state) :=
    (bor_state_pre l t tk σ → bor_state_own l t tk σ ∧ σ.(shp) !! l = Some sc).

  Lemma loc_controlled_local l t sc σ :
    loc_controlled l t tk_local sc σ →
    σ.(sst) !! l = Some [mkItem Unique (Tagged t) None] ∧
    σ.(shp) !! l = Some sc.
  Proof. intros Him. specialize (Him I) as (Hbor & Hmem). split;done. Qed.

  Lemma loc_controlled_unq l t sc s σ :
    loc_controlled l t tk_unq sc σ →
    σ.(sst) !! l = Some s →
    (∃ pm opro, mkItem pm (Tagged t) opro ∈ s ∧ pm ≠ Disabled) →
    (∃ s' op, s = (mkItem Unique (Tagged t) op) :: s') ∧
    σ.(shp) !! l = Some sc.
  Proof.
    intros Him Hstk (pm & opro & Hpm).
    edestruct Him as (Hown & ?). { rewrite /bor_state_pre. eauto. }
    split; last done.
    destruct Hown as (st' & opro' & st'' & Hst' & ->). simplify_eq. eauto.
  Qed.

  Lemma loc_controlled_pub l t sc σ s :
    loc_controlled l t tk_pub sc σ →
    σ.(sst) !! l = Some s →
    (∃ pm opro, mkItem pm (Tagged t) opro ∈ s ∧ pm ≠ Disabled) →
    t ∈ active_SRO s ∧
    σ.(shp) !! l = Some sc.
  Proof.
    intros Him Hst (pm & opro & Hin & Hpm).
    edestruct Him as (Hown & ?). { rewrite /bor_state_pre; eauto 8. }
    split; last done. destruct Hown as (st' & Hst' & Hsro).
    simplify_eq. eauto.
  Qed.

  Lemma loc_controlled_mem_insert_ne l l' t tk sc sc' σ :
    l ≠ l' →
    loc_controlled l t tk sc σ →
    loc_controlled l t tk sc (state_upd_mem <[l' := sc']> σ).
  Proof.
    intros Hneq Him Hpre.
    apply Him in Hpre as [Hown Hmem]. split; first done.
    rewrite lookup_insert_ne; done.
  Qed.
  Lemma loc_controlled_mem_insert l t tk sc sc' σ :
    loc_controlled l t tk sc σ →
    loc_controlled l t tk sc' (state_upd_mem <[l := sc']> σ).
  Proof.
    intros Him Hpre. apply Him in Hpre as [Hown Hmem]. split; first done.
    rewrite lookup_insert; done.
  Qed.

  Section local.
  (** Facts about local tags  *)
  Lemma loc_controlled_local_unique l t t' sc sc' σ :
    loc_controlled l t tk_local sc σ →
    loc_controlled l t' tk_local sc' σ →
    t' = t ∧ sc' = sc.
  Proof.
    intros Hcontrol Hcontrol'. specialize (Hcontrol I) as [Hown Hmem].
    specialize (Hcontrol' I) as [Hown' Hmem'].
    split; last by simplify_eq.
    move : Hown Hown'. rewrite /bor_state_own // => -> [=] //.
  Qed.

  Lemma loc_controlled_local_pre l t t' tk' sc σ :
    loc_controlled l t tk_local sc σ →
    bor_state_pre l t' tk' σ →
    tk' = tk_local ∨ t' = t.
  Proof.
    intros [Heq _]%loc_controlled_local.
    destruct tk'; last by eauto.
    - intros (st' &  pm & opro &  Hst & Hin & Hpm).
      move : Hst Hin. rewrite Heq.
      move => [= <-] /elem_of_list_singleton [=]; eauto.
    - intros (st' &  pm & opro &  Hst & Hin & Hpm).
      move : Hst Hin. rewrite Heq.
      move => [= <-] /elem_of_list_singleton [=]; eauto.
  Qed.
  Lemma loc_controlled_local_own l t t' tk' sc σ :
    loc_controlled l t tk_local sc σ →
    bor_state_own l t' tk' σ →
    (tk' = tk_unq ∨ tk' = tk_local) ∧ t = t'.
  Proof.
    intros [Heq _]%loc_controlled_local. destruct tk'.
    - move => [st' []]. rewrite Heq => [= <-] //.
    - move => [st' [Heq' [opro [st'' ]]]]. move : Heq'. rewrite Heq => [= <-] [= ->] //; eauto.
    - rewrite /bor_state_own Heq => [=]; eauto.
  Qed.

  (* having local ownership of a location is authoritative, in the sense that we can update memory without hurting other tags that control this location. *)
  Lemma loc_controlled_local_authoritative l t t' tk' sc sc' σ f :
    loc_controlled l t tk_local sc (state_upd_mem f σ) →
    loc_controlled l t' tk' sc' σ →
    t ≠ t' →
    loc_controlled l t' tk' sc' (state_upd_mem f σ).
  Proof.
    intros Hcontrol Hcontrol' Hneq [Hown Hmem]%Hcontrol'. split; first done.
    by edestruct (loc_controlled_local_own l t t' tk' sc (state_upd_mem f σ)) as [_ <-].
  Qed.
  End local.

  Definition dom_agree_on_tag (M_t M_s : gmap (ptr_id * loc) scalar) (t : ptr_id) :=
    (∀ l, is_Some (M_t !! (t, l)) → is_Some (M_s !! (t, l))) ∧
    (∀ l, is_Some (M_s !! (t, l)) → is_Some (M_t !! (t, l))).

  Lemma dom_agree_on_tag_upd_ne_target M_t M_s t t' l sc :
    t ≠ t' →
    dom_agree_on_tag M_t M_s t' →
    dom_agree_on_tag (<[(t, l) := sc]> M_t) M_s t'.
  Proof.
    intros Hneq [Htgt Hsrc]. split => l'' Hsome.
    - apply Htgt. move : Hsome. rewrite lookup_insert_is_Some. by intros [[= -> <-] | [_ ?]].
    - apply lookup_insert_is_Some. right. split; first congruence. by apply Hsrc.
  Qed.
  Lemma dom_agree_on_tag_upd_ne_source M_t M_s t t' l sc :
    t ≠ t' →
    dom_agree_on_tag M_t M_s t' →
    dom_agree_on_tag M_t (<[(t, l) := sc]> M_s) t'.
  Proof.
    intros Hneq [Htgt Hsrc]. split => l'' Hsome.
    - apply lookup_insert_is_Some. right. split; first congruence. by apply Htgt.
    - apply Hsrc. move : Hsome. rewrite lookup_insert_is_Some. by intros [[= -> <-] | [_ ?]].
  Qed.
  Lemma dom_agree_on_tag_upd_target M_t M_s t l sc :
    is_Some (M_t !! (t, l)) →
    dom_agree_on_tag M_t M_s t →
    dom_agree_on_tag (<[(t, l) := sc]> M_t) M_s t.
  Proof.
    intros Hs [Htgt Hsrc]. split => l''.
    - rewrite lookup_insert_is_Some. intros [[= <-] | [_ ?]]; by apply Htgt.
    - intros Hsome. rewrite lookup_insert_is_Some'. right; by apply Hsrc.
  Qed.
  Lemma dom_agree_on_tag_upd_source M_t M_s t l sc :
    is_Some (M_s !! (t, l)) →
    dom_agree_on_tag M_t M_s t →
    dom_agree_on_tag M_t (<[(t, l) := sc]> M_s) t.
  Proof.
    intros Hs [Htgt Hsrc]. split => l''.
    - intros Hsome. rewrite lookup_insert_is_Some'. right; by apply Htgt.
    - rewrite lookup_insert_is_Some. intros [[= <-] | [_ ?]]; by apply Hsrc.
  Qed.
  Lemma dom_agree_on_tag_lookup_target M_t M_s t l :
    dom_agree_on_tag M_t M_s t → is_Some (M_t !! (t, l)) → is_Some (M_s !! (t, l)).
  Proof. intros Hag Hsome. apply Hag, Hsome. Qed.
  Lemma dom_agree_on_tag_lookup_source M_t M_s t l :
    dom_agree_on_tag M_t M_s t → is_Some (M_s !! (t, l)) → is_Some (M_t !! (t, l)).
  Proof. intros Hag Hsome. apply Hag, Hsome. Qed.

  Definition tag_interp (M : gmap ptr_id (tag_kind * unit)) (M_t M_s : gmap (ptr_id * loc) scalar) σ_t σ_s : Prop :=
    (∀ (t : ptr_id) tk, M !! t = Some (tk, ()) →
      (* tags are valid *)
      (t < σ_t.(snp))%nat ∧ (t < σ_s.(snp))%nat ∧
      (* at all locations, the values agree, and match the physical state assuming the tag currently has control over the location *)
      (∀ l sc_t, M_t !! (t, l) = Some sc_t → loc_controlled l t tk sc_t σ_t) ∧
      (∀ l sc_s, M_s !! (t, l) = Some sc_s → loc_controlled l t tk sc_s σ_s) ∧
      dom_agree_on_tag M_t M_s t) ∧
    (∀ (t : ptr_id) (l : loc), is_Some (M_t !! (t, l)) → is_Some (M !! t)) ∧
    (∀ (t : ptr_id) (l : loc), is_Some (M_s !! (t, l)) → is_Some (M !! t)).
End heap_defs.


Notation "p '$$' tk" := (tkmap_elem tag_name p tk ()) (at level 50).

Definition tk_to_frac (tk : tag_kind) :=
  match tk with
  | tk_pub => DfracDiscarded
  | _ => DfracOwn 1
  end.
Notation "l '↦t[' tk ']{' t } sc" := (ghost_map_elem heap_view_target_name (t, l) (tk_to_frac tk) sc)
  (at level 20, format "l  ↦t[ tk ]{ t }  sc") : bi_scope.
Notation "l '↦s[' tk ']{' t } sc" := (ghost_map_elem heap_view_source_name (t, l) (tk_to_frac tk) sc)
  (at level 20, format "l  ↦s[ tk ]{ t }  sc") : bi_scope.


Section state_interp.
  Context `{bor_stateG Σ} (sc_rel : scalar → scalar → iProp Σ).

  (* We generally do not enforce that stacks for all locations are equal: that would make non-determinism in choosing locations slightly clunky.
    Rather, we should again force equality in bijections.
  *)
  Definition bor_auth (M_call : gmap call_id (gmap ptr_id (gset loc))) (M_tag : gmap ptr_id (tag_kind * unit)) (M_t M_s : gmap (ptr_id * loc) scalar) : iProp Σ :=
    ghost_map_auth call_name 1 M_call ∗
    tkmap_auth tag_name 1 M_tag ∗
    ghost_map_auth heap_view_target_name 1 M_t ∗
    ghost_map_auth heap_view_source_name 1 M_s.
  Definition bor_interp (σ_t : state) (σ_s : state) : iProp Σ :=
  (* since multiple parts of the interpretation need access to these maps, we own the authoritative parts here and not in the interpretations below *)
   ∃ (M_call : gmap call_id (gmap ptr_id (gset loc)))
     (M_tag : gmap ptr_id (tag_kind * unit))
     (M_t M_s : gmap (ptr_id * loc) scalar),
    bor_auth M_call M_tag M_t M_s ∗

    state_rel sc_rel M_tag M_t M_call σ_t σ_s ∗
    (* due to the [state_rel], enforcing this on [σ_t] also does the same for [σ_s] *)
    ⌜call_set_interp M_call σ_t⌝ ∗
    ⌜tag_interp M_tag M_t M_s σ_t σ_s⌝ ∗

    ⌜state_wf σ_s⌝ ∗
    ⌜state_wf σ_t⌝.

  Lemma bor_interp_get_pure σ_t σ_s :
    bor_interp σ_t σ_s -∗ ⌜σ_s.(sst) = σ_t.(sst) ∧ σ_s.(snp) = σ_t.(snp) ∧ σ_s.(snc) = σ_t.(snc) ∧ σ_s.(scs) = σ_t.(scs) ∧ state_wf σ_s ∧ state_wf σ_t ∧ dom (gset loc) σ_s.(shp) = dom (gset loc) σ_t.(shp)⌝.
  Proof.
    iIntros "(% & % & % & % & ? & Hstate & _ & _ & % & %)".
    iPoseProof (state_rel_get_pure with "Hstate") as "%".
    iPoseProof (state_rel_dom_eq with "Hstate") as "<-".
    iPureIntro. tauto.
  Qed.

  Lemma bor_interp_get_state_wf σ_t σ_s :
    bor_interp σ_t σ_s -∗
    ⌜state_wf σ_t⌝ ∗ ⌜state_wf σ_s⌝.
  Proof. iIntros "(% & % & % & % & ? & Hstate & _ & _ & % & %)". eauto. Qed.

End state_interp.


(** Array generalizes pointsto connectives to lists of scalars *)
Definition array_tag `{!bor_stateG Σ} γh (t : ptr_id) (l : loc) (dq : dfrac) (scs : list scalar) : iProp Σ :=
  ([∗ list] i ↦ sc ∈ scs, ghost_map_elem γh (t, l +ₗ i) dq sc)%I.
Notation "l '↦t∗[' tk ']{' t } scs" := (array_tag heap_view_target_name t l (tk_to_frac tk) scs)
  (at level 20, format "l  ↦t∗[ tk ]{ t }  scs") : bi_scope.
Notation "l '↦s∗[' tk ']{' t } scs" := (array_tag heap_view_source_name t l (tk_to_frac tk) scs)
  (at level 20, format "l  ↦s∗[ tk ]{ t }  scs") : bi_scope.

Lemma ghost_map_array_tag_lookup `{!bor_stateG Σ} (γh : gname) (q : Qp) (M : gmap (ptr_id * loc) scalar) (scs : list scalar) (t : ptr_id) (l : loc) dq :
  ghost_map_auth γh q M -∗
  ([∗ list] i ↦ sc ∈ scs, ghost_map_elem γh (t, l +ₗ i) dq sc) -∗
  ⌜∀ i : nat, (i < length scs)%nat → M !! (t, l +ₗ i) = scs !! i⌝.
Proof.
  iIntros "Hauth Helem". iInduction scs as [ |sc scs ] "IH" forall (l) "Hauth Helem".
  - iPureIntro; cbn. lia.
  - rewrite big_sepL_cons. iDestruct "Helem" as "[Hsc Hscs]".
    iPoseProof (ghost_map_lookup with "Hauth Hsc") as "%Hl".
    iDestruct ("IH" $! (l +ₗ 1) with "Hauth [Hscs]") as "%IH".
    { iApply (big_sepL_mono with "Hscs"). intros i sc' Hs. cbn. rewrite shift_loc_assoc.
      replace (Z.of_nat $ S i) with (1 + i)%Z by lia. done. }
    iPureIntro. intros i Hle. destruct i; first done.
    replace (Z.of_nat $ S i) with (1 + i)%Z by lia. cbn in *. rewrite -(IH i); last lia.
    by rewrite shift_loc_assoc.
Qed.

Fixpoint array_tag_map (l : loc) (t : ptr_id) (v : list scalar) : gmap (ptr_id * loc) scalar :=
  match v with
  | [] => ∅
  | sc :: v' => <[(t, l) := sc]> (array_tag_map (l +ₗ 1) t v')
  end.
Lemma array_tag_map_lookup1 l t v t' l' :
  is_Some (array_tag_map l t v !! (t', l')) →
  t' = t ∧ l.1 = l'.1 ∧ l.2 ≤ l'.2 < l.2 + length v.
Proof.
  induction v as [ | sc v IH] in l |-*.
  - simpl. rewrite lookup_empty. intros [? [=]].
  - simpl. move => [sc0 ]. rewrite lookup_insert_Some. move => [[[= <- <-] Heq] | [Hneq Ht]]; first lia.
    move : (IH (l +ₗ 1) ltac:(eauto)). destruct l. simpl. lia.
Qed.
Lemma array_tag_map_lookup2 l t v t' l' :
  is_Some (array_tag_map l t v !! (t', l')) →
  t' = t ∧ ∃ i, (i < length v)%nat ∧ l' = l +ₗ i.
Proof.
  intros (-> & H1 & H2)%array_tag_map_lookup1.
  split; first done. exists (Z.to_nat (l'.2 - l.2)).
  destruct l, l';  rewrite /shift_loc; simpl in *. split.
  - lia.
  - apply pair_equal_spec. split; lia.
Qed.

Lemma array_tag_map_lookup_Some l t v (i : nat) :
  (i < length v)%nat →
  array_tag_map l t v !! (t, l +ₗ i) = v !! i.
Proof.
  induction v as [ | sc v IH] in l, i |-*.
  - simpl. lia.
  - simpl. intros Hi. destruct i as [ | i].
    + rewrite shift_loc_0_nat. rewrite lookup_insert. done.
    + rewrite lookup_insert_ne; first last. { destruct l; simpl; intros [= ?]; lia. }
      move : (IH (l +ₗ 1) i ltac:(lia)). rewrite shift_loc_assoc.
      by replace (Z.of_nat (S i)) with (1 + i) by lia.
Qed.

Lemma ghost_map_array_tag_update `{!bor_stateG Σ} (γh : gname) (M : gmap (ptr_id * loc) scalar) (v v' : list scalar) (t : ptr_id) (l : loc) :
  ghost_map_auth γh 1 M -∗
  ([∗ list] i ↦ sc ∈ v, ghost_map_elem γh (t, l +ₗ i) (DfracOwn 1) sc) ==∗
  ([∗ list] i ↦ sc' ∈ v', ghost_map_elem γh (t, l +ₗ i) (DfracOwn 1) sc') ∗
  ghost_map_auth γh 1 (array_tag_map l t v' ∪ M).
Proof.
Admitted.

Lemma ghost_map_array_tag_insert `{!bor_stateG Σ} (γh : gname) (M : gmap (ptr_id * loc) scalar) (v : list scalar) (t : ptr_id) (l : loc) :
  (∀ i : nat, (i < length v)%nat → M !! (t, l +ₗ i) = None) →
  ghost_map_auth γh 1 M  ==∗
  ([∗ list] i ↦ sc ∈ v, ghost_map_elem γh (t, l +ₗ i) (DfracOwn 1) sc) ∗
  ghost_map_auth γh 1 (array_tag_map l t v ∪ M).
Proof.
Admitted.

Lemma ghost_map_array_tag_tk `{!bor_stateG Σ} (γh : gname) (v : list scalar) (t : ptr_id) (l : loc) tk :
  ([∗ list] i ↦ sc ∈ v, ghost_map_elem γh (t, l +ₗ i) (DfracOwn 1) sc) ==∗
  ([∗ list] i ↦ sc ∈ v, ghost_map_elem γh (t, l +ₗ i) (tk_to_frac tk) sc).
Proof.
  destruct tk; cbn; [ | by eauto | by eauto].
  iInduction v as [| sc v] "IH" forall (l); first by eauto.
  rewrite !big_sepL_cons. iIntros "[Hh Hr]".
  iMod (ghost_map_elem_persist with "Hh") as "$".
  iMod ("IH" $! (l +ₗ 1) with "[Hr]") as "Hr".
  - iApply (big_sepL_mono with "Hr"). intros i sc' Hs. simpl. rewrite shift_loc_assoc.
    by replace (Z.of_nat (S i)) with (1 + i) by lia.
  - iModIntro.
    iApply (big_sepL_mono with "Hr"). intros i sc' Hs. simpl. rewrite shift_loc_assoc.
    by replace (Z.of_nat (S i)) with (1 + i) by lia.
Qed.


(** Lemmas / Accessors *)
Add Printing Constructor state item.
Section lemmas.
  Context `{bor_stateG Σ} (sc_rel : scalar → scalar → iProp Σ)
    (sc_rel_pers : ∀ sc_t sc_s, Persistent (sc_rel sc_t sc_s)).
  Local Notation bor_interp := (bor_interp sc_rel).

  Implicit Types
    (l : loc) (sc : scalar).

  Lemma heap_local_alloc σ_t σ_s T :
    bor_interp σ_t σ_s ==∗
    let l_t := (fresh_block σ_t.(shp), 0) in
    let l_s := (fresh_block σ_s.(shp), 0) in
    let t := σ_t.(snp) in
    bor_interp
      (mkState (init_mem l_t (tsize T) σ_t.(shp)) (init_stacks σ_t.(sst) l_t (tsize T) (Tagged σ_t.(snp))) σ_t.(scs) (S σ_t.(snp)) σ_t.(snc))
      (mkState (init_mem l_s (tsize T) σ_s.(shp)) (init_stacks σ_s.(sst) l_s (tsize T) (Tagged σ_s.(snp))) σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)) ∗
      t $$ tk_local ∗
      l_t ↦t∗[tk_local]{t} repeat ScPoison (tsize T) ∗
      l_s ↦s∗[tk_local]{t} repeat ScPoison (tsize T).
  Proof.
    iIntros "(% & % & % & % & ? & Hstate & ? & Htag & %Hwf_s & %Hwf_t)".
    (* 1. allocate new local locations
       2. profit
    *)
    (*iDestruct "Hheap_s" as (Mheap_s) "(Hheap_s_auth & %Hheap_s)".*)
    (*iDestruct "Hheap_t" as (Mheap_t) "(Hheap_t_auth & %Hheap_t)".*)

    (* TODO: need notion of array maps, see HeapLang *)
    (*iMod (ghost_map_insert_big with "Hheap_s_auth") as "(Hheap_s_auth & Hloc_s)".*)
  Admitted.

  Lemma state_wf_upd_mem σ l sc :
    is_Some (σ.(shp) !! l) →
    wf_scalar σ.(snp) sc →
    state_wf σ →
    state_wf (state_upd_mem (<[l := sc]>) σ).
  Proof.
    intros Hs Hwf []. constructor; try done.
    - rewrite dom_insert //.
      have ->: {[l]} ∪ dom (gset loc) (shp σ) ≡ dom (gset loc) (shp σ); last done.
      split; rewrite elem_of_union; last by eauto.
      intros [ ->%elem_of_singleton_1 | ]; last done.
      by apply elem_of_dom.
    - intros l' l'' pid Hsome.
      destruct (decide (l = l')) as [<- | Hne].
      + move : Hsome. rewrite lookup_insert => [= Heq].
        subst sc. specialize (Hwf _ _ eq_refl). apply Hwf.
      + rewrite lookup_insert_ne in Hsome; last done.
        eapply state_wf_mem_tag; done.
    Qed.

  Lemma heap_local_write_target σ_t σ_s (t : ptr_id) l sc sc' :
    bor_interp σ_t σ_s -∗
    l ↦t[tk_local]{t} sc -∗
    t $$ tk_local -∗
    ⌜wf_scalar σ_t.(snp) sc'⌝ ==∗
    bor_interp (state_upd_mem (<[l := sc']>) σ_t) σ_s ∗
    l ↦t[tk_local]{t} sc' ∗
    t $$ tk_local.
  Proof.
    iIntros "(% & % & % & % & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hsrel & ? & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag %Hwf_sc".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & Ht_dom & Hs_dom).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    specialize (Ht _ _ Ht_lookup) as Hcontrol.
    specialize (loc_controlled_local _ _ _ _ Hcontrol) as (Hstack & Hmem).

    iMod (ghost_map_update sc' with "Htag_t_auth Hp") as "[Htag_t_auth $]".
    iModIntro. iFrame "Htag". rewrite /bor_interp.
    iExists M_call, M_tag, (<[(t, l):=sc']> M_t), M_s.
    iFrame. cbn. iSplitL "Hsrel".
    { iApply (state_rel_upd_priv_target with "Hsrel").
      - eauto.
      - exists tk_local. split_and!; [done | by eauto | by left ].
    }
    iSplitL; first last.
    { repeat iSplitL; [ done.. | ].
      iPureIntro. apply state_wf_upd_mem; [by eauto | done | done].
    }

    iPureIntro.
    split_and!.
    - intros t' tk' (? & ? & H')%Htag_interp. do 2 (split; first done).
      destruct H' as (Ha_t & Ha_s & Hagree').
      split_and!; [ | done | ].
      + intros l' sc_t.
        destruct (decide (t = t')) as [<- | Hneq]; first last.
        { rewrite lookup_insert_ne; last congruence. intros Hsc_t.
          destruct (decide (l' = l)) as [-> | Hneq_loc].
          { (* this is fine as tag t has local ownership: t' doesn't have any control *)
            eapply loc_controlled_local_authoritative; [ | by apply Ha_t | done].
            eapply loc_controlled_mem_insert. done.
          }
          apply loc_controlled_mem_insert_ne; [done | by apply Ha_t].
        }
        revert Ha_t.
        destruct (decide (l' = l)) as [-> | Hneq_loc] => Ha_t.
        * rewrite lookup_insert => [= ->]. by eapply loc_controlled_mem_insert, Ha_t.
        * rewrite lookup_insert_ne; last congruence. intros ?.
          eapply loc_controlled_mem_insert_ne; [done | by apply Ha_t].
      + destruct (decide (t = t')) as [<- | Hneq].
        * eapply dom_agree_on_tag_upd_target; eauto.
        * eapply dom_agree_on_tag_upd_ne_target; eauto.
    - intros t' l'. rewrite lookup_insert_is_Some. intros [[= <- <-] | [_ ?%Ht_dom]]; last done. eauto.
    - done.
  Qed.


  Lemma tag_values_included_iff v t :
    tag_values_included v t ↔ (∀ i, (i < length v)%nat → wf_scalar t (v !!! i)).
  Proof.
    rewrite /tag_values_included /wf_scalar. split.
    - intros Hin i Hi t' l Hvi. eapply (Hin l). rewrite -Hvi. by apply elem_of_list_lookup_total_2.
    - intros Hs l tg (i & Hi & Hl)%elem_of_list_lookup_total_1. by eapply Hs.
  Qed.
  Lemma heap_local_readN_target σ_t σ_s (t : ptr_id) l scs :
    bor_interp σ_t σ_s -∗
    l ↦t∗[tk_local]{t} scs -∗
    t $$ tk_local -∗
    ⌜∀ i : nat, (i < length scs)%nat → σ_t.(shp) !! (l +ₗ i) = scs !! i⌝ ∗
    ⌜∀ i:nat, (i < length scs)%nat → bor_state_own (l +ₗ i) t tk_local σ_t⌝ ∗
    ⌜scs <<t σ_t.(snp)⌝.
  Proof.
    iIntros "(% & % & % & % & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hsrel & ? & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _ & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_array_tag_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    iPureIntro.
    enough (∀ i: nat, (i < length scs)%nat → σ_t.(shp) !! (l +ₗ i) = scs !! i ∧ σ_t.(sst) !! (l +ₗ i) = Some [mkItem Unique (Tagged t) None] ∧ wf_scalar σ_t.(snp) (scs !!! i)) as Hsingle.
    { split_and!; [ apply Hsingle.. | apply tag_values_included_iff; apply Hsingle]. }
    intros i Hi.
    specialize (Ht_lookup i Hi). rewrite list_lookup_lookup_total in Ht_lookup; first last.
    { by apply lookup_lt_is_Some_2. }
    specialize (Ht _ _ Ht_lookup) as Hcontrol.
    specialize (loc_controlled_local _ _ _ _ Hcontrol) as (Hstack & Hmem).
    split_and!.
    - rewrite Hmem. rewrite list_lookup_lookup_total; [done | by apply lookup_lt_is_Some_2].
    - done.
    - intros tg l' Hl.
      destruct tg as [tg | ]; last done.
      eapply state_wf_mem_tag; first done.
      erewrite Hmem, Hl. done.
  Qed.

  Lemma heap_protected_readN_target σ_t σ_s (t : ptr_id) tk l v_t c M :
    (∀ i: nat, (i < length v_t)%nat → call_set_in M t (l +ₗ i)) →
    bor_interp σ_t σ_s -∗
    l ↦t∗[tk]{t} v_t -∗
    t $$ tk -∗
    c @@ M -∗
    ⌜∀ i : nat, (i < length v_t)%nat → σ_t.(shp) !! (l +ₗ i) = v_t !! i⌝ ∗
    ⌜∀ i:nat, (i < length v_t)%nat → bor_state_own (l +ₗ i) t tk σ_t⌝ ∗
    ⌜v_t <<t σ_t.(snp)⌝.
  Proof.
    iIntros (Hprot) "(% & % & % & % & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hsrel & %Hcall & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag Hcall".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct Htag_interp as (Htag_interp & _ & _).
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_array_tag_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    iPoseProof (ghost_map_lookup with "Hc Hcall") as "%Hc_lookup".
    iPureIntro.
    enough (∀ i: nat, (i < length v_t)%nat → σ_t.(shp) !! (l +ₗ i) = v_t !! i ∧ bor_state_own (l +ₗ i) t tk σ_t ∧ wf_scalar σ_t.(snp) (v_t !!! i)) as Hsingle.
    { split_and!; [ apply Hsingle.. | apply tag_values_included_iff; apply Hsingle]. }
    intros i Hi.
    specialize (Ht_lookup i Hi). rewrite list_lookup_lookup_total in Ht_lookup; first last.
    { by apply lookup_lt_is_Some_2. }
    specialize (Ht _ _ Ht_lookup) as Hcontrol.
    assert (bor_state_pre (l +ₗ i) t tk σ_t) as Hpre.
    { specialize (Hprot i Hi).
      specialize (call_set_interp_access _ _ _ _ _ Hcall ltac:(exists M; done)). apply loc_protected_bor_state_pre.
    }
    specialize (Hcontrol Hpre) as [Hown Hmem].
    split_and!; [| done | ].
    - rewrite Hmem. rewrite list_lookup_lookup_total; [done | ]. by apply lookup_lt_is_Some_2.
    - intros tg l' Hl.
      destruct tg as [tg | ]; last done.
      eapply state_wf_mem_tag; first done.
      erewrite Hmem, Hl. done.
  Qed.

  Lemma heap_protected_readN_source σ_t σ_s (t : ptr_id) tk l v_t c M :
    (∀ i: nat, (i < length v_t)%nat → call_set_in M t (l +ₗ i)) →
    bor_interp σ_t σ_s -∗
    l ↦s∗[tk]{t} v_t -∗
    t $$ tk -∗
    c @@ M -∗
    ⌜∀ i : nat, (i < length v_t)%nat → σ_s.(shp) !! (l +ₗ i) = v_t !! i⌝ ∗
    ⌜∀ i:nat, (i < length v_t)%nat → bor_state_own (l +ₗ i) t tk σ_s⌝ ∗
    ⌜v_t <<t σ_s.(snp)⌝.
  Proof.
  Admitted.

  Lemma state_upd_mem_compose f g σ :
    state_upd_mem f (state_upd_mem g σ) = state_upd_mem (f ∘ g) σ.
  Proof. destruct σ. done. Qed.

  Lemma write_mem_insert_commute_1 l l' v sc M :
    l.2 < l'.2 →
    <[ l := sc ]> (write_mem l' v M) = write_mem l' v (<[ l := sc ]> M).
  Proof.
    induction v in l, l', sc, M |-*; cbn; first done.
    intros Hl. rewrite (IHv l (l' +ₗ 1)); first last.
    { destruct l', l; cbn in *; lia. }
    rewrite insert_commute; first done. intros ->; lia.
  Qed.
  Lemma write_mem_head l sc v M :
    <[ l := sc ]> (write_mem (l +ₗ 1) v M) = write_mem l (sc :: v) M.
  Proof. rewrite write_mem_insert_commute_1; last by destruct l; cbn; lia. done. Qed.

  Global Instance state_upd_mem_proper : Proper ((eq ==> eq) ==> eq ==> eq) state_upd_mem.
  Proof.
    intros f g Heq ? σ ->. destruct σ as [ mem ]. by rewrite /state_upd_mem (Heq mem mem eq_refl).
  Qed.
  Lemma state_upd_write_mem_head sc v l σ :
    state_upd_mem (<[ l := sc ]> ∘ write_mem (l +ₗ 1) v) σ = state_upd_mem (write_mem l (sc :: v)) σ.
  Proof. destruct σ. rewrite /state_upd_mem. cbn. by rewrite write_mem_head. Qed.

  Lemma heap_local_writeN_target σ_t σ_s (t : ptr_id) l scs scs' :
    bor_interp σ_t σ_s -∗
    l ↦t∗[tk_local]{t} scs -∗
    t $$ tk_local -∗
    ⌜length scs' = length scs⌝ -∗
    ⌜scs' <<t σ_t.(snp) ⌝ ==∗
    bor_interp (state_upd_mem (write_mem l scs') σ_t) σ_s ∗
    l ↦t∗[tk_local]{t} scs' ∗
    t $$ tk_local.
  Proof.
    iInduction scs' as [ | sc' scs'] "IH" forall (l scs).
    - iIntros "Hbor Hp Ht %Hlen _". destruct scs; last done. iFrame "Ht Hp". iModIntro. destruct σ_t; eauto.
    - iIntros "Hbor Hp Ht %Hlen %Hwf". destruct scs as [ | sc scs]; first done.
      iPoseProof (big_sepL_cons with "Hp") as "[Hh Hp]".
      iMod  ("IH" $! (l +ₗ 1) scs with "Hbor [Hp] Ht [] []") as "(Hbor & Hp & Ht)".
      { iApply (big_sepL_mono with "Hp"). intros i sc0 Hsc0. cbn.
        rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done. }
      { cbn in Hlen. iPureIntro. lia. }
      { iPureIntro. intros l' tg Hin. eapply Hwf. right. apply Hin. }
      iMod (heap_local_write_target  _ _ _ _ _ sc' with "Hbor Hh Ht []") as "(Hbor & Hh & Ht)".
      { iPureIntro. cbn. specialize (proj1 (tag_values_included_iff _ _) Hwf) as Hi. apply (Hi O). cbn; lia. }
      iModIntro. iFrame "Ht". iSplitL "Hbor".
      { rewrite state_upd_mem_compose. rewrite shift_loc_0_nat. by rewrite state_upd_write_mem_head. }
      iApply big_sepL_cons. iFrame "Hh". iApply (big_sepL_mono with "Hp").
      intros i sc0 Hsc0. cbn.
      rewrite shift_loc_assoc. replace (1 + i)%Z with (Z.of_nat $ S i) by lia. done.
  Qed.

  Lemma heap_local_readN_source σ_t σ_s (t : ptr_id) l scs :
    bor_interp σ_t σ_s -∗
    l ↦s∗[tk_local]{t} scs -∗
    t $$ tk_local -∗
    ⌜∀ i : nat, (i < length scs)%nat → σ_s.(shp) !! (l +ₗ i) = scs !! i⌝ ∗
    ⌜∀ i:nat, (i < length scs)%nat → bor_state_own (l +ₗ i) t tk_local σ_s⌝ ∗
    ⌜scs <<t σ_s.(snp)⌝.
  Proof.
  Admitted.

  Lemma heap_local_writeN_source σ_t σ_s (t : ptr_id) l scs scs' :
    bor_interp σ_t σ_s -∗
    l ↦s∗[tk_local]{t} scs -∗
    t $$ tk_local -∗
    ⌜length scs' = length scs⌝ -∗
    ⌜scs' <<t σ_s.(snp) ⌝ ==∗
    bor_interp σ_t (state_upd_mem (write_mem l scs') σ_s) ∗
    l ↦s∗[tk_local]{t} scs' ∗
    t $$ tk_local.
  Proof.
  Admitted.

End lemmas.

(* accessing a local location is only possible with the same tag, retaining the same stack for the access *)
Lemma local_access_eq l t t' stk n stk' kind σ_s σ_t M_tag M_t M_s :
  σ_t.(sst) !! l = Some stk →
  access1 stk kind t' σ_t.(scs) = Some (n, stk') →
  M_tag !! t = Some (tk_local, ()) →
  is_Some (M_t !! (t, l)) →
  tag_interp M_tag M_t M_s σ_t σ_s →
  t' = Tagged t ∧ stk' = stk.
Proof.
  intros Hst Haccess Htag Ht Htag_interp.
  specialize (access1_in_stack _ _ _ _ _ _ Haccess) as (it & Hin_stack & <- & Henabled).
  destruct Htag_interp as (Htag_interp & _ & _).
  specialize (Htag_interp _ _ Htag) as (_ & _ & Htl & Hsl & Hdom).
  destruct Ht as (sc_t & Ht).
  specialize (Htl _ _ Ht) as Hcontrol.
  apply loc_controlled_local in Hcontrol as (Hcontrol & _).
  destruct (tag_unique_head_access σ_t.(scs) _ (Tagged t) None kind ltac:(by exists [])) as (n' & Hn).
  move : Hst Hin_stack Haccess .
  rewrite Hcontrol => [= <-]. rewrite elem_of_list_singleton => ->.
  rewrite Hn => [= _ <-]. done.
Qed.

Lemma protector_access_eq l t t' stk n stk' kind σ_s σ_t M_tag Mcall M_t M_s :
  σ_t.(sst) !! l = Some stk →
  access1 stk kind t' σ_t.(scs) = Some (n, stk') →
  M_tag !! t = Some (tk_unq, ()) →
  is_Some (M_t !! (t, l)) →
  (∃ (c: call_id), call_set_in' Mcall c t l) →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  t' = Tagged t.
Proof.
  intros Hst Haccess Htag Ht (c & Hcall) Htag_interp Hcall_interp Hwf.
  specialize (call_set_interp_access _ _ _ _ _ Hcall_interp Hcall) as (Hc_in & _ & (stk'' & pm & Hstk'' & Hin & Hpm)).
  destruct Htag_interp as (Htag_interp & _ & _).
  specialize (Htag_interp _ _ Htag) as (_ & _ & Htl & Hsl & Hdom).
  destruct Ht as (sc_t & Ht).
  specialize (Htl _ _ Ht) as Hcontrol.
  specialize (loc_controlled_unq _ _ _ _ _ Hcontrol Hstk'' ltac:(eauto)) as ((stk''' & opro & ->) & Hmem).
  move : Hstk'' Hin Haccess. rewrite Hst => [= Heq]. move : Hst. rewrite Heq => Hst Hi.
  have ->: opro = Some c.
  { destruct (state_wf_stack_item _ Hwf _ _ Hst) as [_ ND].
    have [=] := stack_item_tagged_NoDup_eq _ _ _ t ND Hi ltac:(by left) eq_refl eq_refl.
    done.
  }
  eapply access1_incompatible_head_protector; [by (eexists; eauto) | done].
Qed.

(* successfully accesses with a private location are only possible when the tag is equal *)
Lemma priv_loc_UB_access_eq l kind σ_s σ_t t t' stk M_tag M_t M_s Mcall :
  σ_t.(sst) !! l = Some stk →
  is_Some (access1 stk kind t' σ_t.(scs)) →
  priv_loc M_tag M_t Mcall t l →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  t' = Tagged t.
Proof.
  intros Hs ([? ?] & Haccess) Hpriv Htag_interp Hcall_interp Hwf.
  destruct Hpriv as (tk & Htag & Ht & [-> | [-> Hc]]).
  - by eapply local_access_eq.
  - eapply protector_access_eq; done.
Qed.

Definition untagged_or_public (M_tag : gmap ptr_id (tag_kind * unit)) t :=
  match t with
  | Tagged t2 => M_tag !! t2 = Some (tk_pub, ())
  | Untagged => True
  end.
Lemma priv_pub_access_UB l kind σ_s σ_t t t' stk M_tag Mcall M_t M_s :
  σ_t.(sst) !! l = Some stk →
  is_Some (access1 stk kind t' σ_t.(scs)) →
  priv_loc M_tag M_t Mcall t l →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  untagged_or_public M_tag t' →
  False.
Proof.
  intros Hs Haccess Hpriv Htag_interp Hcall_interp Hwf.
  rewrite (priv_loc_UB_access_eq _ _ _ _ _ _ _ _ _ _ _ Hs Haccess Hpriv Htag_interp Hcall_interp Hwf).
  destruct Hpriv as (tk & Hl & _ & [-> | [-> _]]); cbn; intros; simplify_eq.
Qed.

Lemma priv_loc_UB_retag_access_eq σ_s σ_t c l old new mut T kind α' nxtp' M_tag M_t M_s Mcall
  (FRZ: if mut is Immutable then is_freeze T else True)
  (N2P: kind ≠ TwoPhase) :
  retag σ_t.(sst) σ_t.(snp) σ_t.(scs) c l old kind (RefPtr mut) T = Some (new, α', nxtp') →
  ∀ i t, (i < tsize T)%nat →
  priv_loc M_tag M_t Mcall t (l +ₗ i) →
  tag_interp M_tag M_t M_s σ_t σ_s →
  call_set_interp Mcall σ_t →
  state_wf σ_t →
  untagged_or_public M_tag old →
  False.
Proof.
  intros Hrt i t Hi.
  have NZST: (0 < tsize T)%nat by lia.
  destruct (retag_change_ref_NZST _ _ _ _ _ _ _ _ _ _ _ _ NZST Hrt);
    subst new nxtp'.
  destruct (retag_Some_Ref _ _ _ _ _ _ _ _ _ _ _ _ NZST FRZ N2P Hrt _ Hi)
    as (stk & stk' & Eqstk & Eqstk' & GR).
  apply grant_access1 in GR; [|by destruct mut].
  revert Eqstk GR. by apply priv_pub_access_UB.
Qed.


(* NOTE: might need to generalize that with the bijection a bit when we want to do cool things, e.g., pass parts of an object to a function (but for just obtaining a reflexivity thm, it should be fine) *)
Section val_rel.
  Context {Σ} `{bor_stateG Σ}.
  Definition sc_rel (sc1 sc2 : scalar) : iProp Σ :=
    match sc1, sc2 with
    | ScInt z1, ScInt z2 => ⌜z1 = z2⌝
    | ScFnPtr f1, ScFnPtr f2 => ⌜f1  = f2⌝
    | ScPtr l1 p1, ScPtr l2 p2 =>
        (* through srel: the stacks are the same, the allocation size is the same, and the locations are related (i.e.: if tagged, then it is public) *)
        ⌜l1 = l2⌝ ∗
        (⌜p1 = Untagged⌝ ∗ ⌜p2 = Untagged⌝ ∨
        (∃ t1 t2, ⌜p1 = Tagged t1⌝ ∗ ⌜p2 = Tagged t2⌝ ∗
        (* may want to generalize that properly when we have a proper bijection on tags*)
        ⌜t1 = t2⌝ ∗
        t1 $$ tk_pub))
        (* note: we do not have any assertion about the value as viewed by the tag here -- we don't really care about it, we need to do a retag anyways. what the tk_pub gives us is that the locations store related values *)
    | ScCallId c, ScCallId c' => ⌜c = c'⌝
    (* TODO: poison cannot be refined by ScPtr: this would break the public write lemma,
        as we cannot ensure that the well-taggedness is still fulfilled.
        Either, we should make sure here that values are well-tagged (through some persistent ghost state giving a lower-bound on the allowed tag) or relax the well-taggedness requirement for the heap.
     *)
    | ScInt z, ScPoison => True
    | ScPoison, ScPoison => True
    | ScFnPtr fn, ScPoison => True
    | _, _ => False
    end.

  Definition value_rel (v1 v2 : value) : iProp Σ := [∗ list] sc_t; sc_s ∈ v1; v2, sc_rel sc_t sc_s.

  Definition rrel (r1 r2 : result) : iProp Σ :=
    match r1, r2 with
    | ValR v1, ValR v2 => value_rel v1 v2
    | PlaceR l1 bor1 T1, PlaceR l2 bor2 T2 =>
      (* places must be related in a similar way as pointers: either untagged or public. Types should be equal. *)
      sc_rel (ScPtr l1 bor1) (ScPtr l2 bor2) ∧ ⌜T1 = T2⌝
    | _, _ => False
    end.

  Global Instance sc_rel_persistent sc_t sc_s : Persistent (sc_rel sc_t sc_s).
  Proof. destruct sc_t, sc_s; apply _. Qed.
  Global Instance value_rel_persistent v_t v_s : Persistent (value_rel v_t v_s).
  Proof. apply _. Qed.
  Global Instance rrel_persistent r_t r_s : Persistent (rrel r_t r_s).
  Proof. destruct r_t, r_s; apply _. Qed.

  Lemma sc_rel_public_ptr_inv σ_t σ_s t1 t2 l1 l2 :
    bor_interp sc_rel σ_t σ_s -∗
    sc_rel (ScPtr l1 (Tagged t1)) (ScPtr l2 (Tagged t2)) -∗
    ⌜l1 = l2 ∧ t1 = t2⌝ ∗
    ∀ sc_s, ⌜σ_s.(shp) !! l1 = Some sc_s⌝ → ∃ sc_t, ⌜σ_t.(shp) !! l2 = Some sc_t⌝ ∗ sc_rel sc_t sc_s.
  Proof.
  Abort.

  (* Inversion lemmas *)
  Lemma sc_rel_ptr_source sc_t l_s t_s :
    sc_rel sc_t (ScPtr l_s t_s) -∗ ⌜sc_t = ScPtr l_s t_s⌝ ∗ (if t_s is Tagged t then t $$ tk_pub else True).
  Proof.
    iIntros "Hrel". destruct sc_t; [done | done | | done | done ].
    iDestruct "Hrel" as "(-> & [[-> ->] | (% & %t & -> & -> & -> & ?)])"; iFrame; done.
  Qed.
  Lemma sc_rel_fnptr_source sc_t fn :
    sc_rel sc_t (ScFnPtr fn) -∗ ⌜sc_t = ScFnPtr fn⌝.
  Proof.
    iIntros "Hrel". destruct sc_t; [done | done | done | | done].
    by iDestruct "Hrel" as "->".
  Qed.
  Lemma sc_rel_int_source sc_t z :
    sc_rel sc_t (ScInt z) -∗ ⌜sc_t = ScInt z⌝.
  Proof.
    iIntros "Hrel". destruct sc_t; [ done | | done..].
    by iDestruct "Hrel" as "->".
  Qed.
  Lemma sc_rel_cid_source sc_t c :
    sc_rel sc_t (ScCallId c) -∗ ⌜sc_t = ScCallId c⌝.
  Proof. iIntros "Hrel"; destruct sc_t; [done.. | ]. by iDestruct "Hrel" as "->". Qed.

  Lemma sc_rel_poison_target sc_s :
    sc_rel (ScPoison) sc_s -∗ ⌜sc_s = ScPoison⌝.
  Proof. iIntros "Hrel". destruct sc_s; done. Qed.

  Lemma sc_rel_wf_scalar_iff sc_t sc_s t :
    sc_rel sc_t sc_s -∗ ⌜wf_scalar t sc_t ↔ wf_scalar t sc_s⌝.
  Proof.
    iIntros "Hsc".
    destruct sc_s as [ | n | l tg | | ].
    - destruct sc_t; done.
    - iPoseProof (sc_rel_int_source with "Hsc") as "->". done.
    - iPoseProof (sc_rel_ptr_source with "Hsc") as "[-> _]". done.
    - iPoseProof (sc_rel_fnptr_source with "Hsc") as "->"; done.
    - iPoseProof (sc_rel_cid_source with "Hsc") as "->"; done.
  Qed.

  Lemma rrel_place_source r_t l_s t_s T :
    rrel r_t (PlaceR l_s t_s T) -∗
    ∃ l_t, ⌜r_t = PlaceR l_t t_s T⌝ ∗ (if t_s is Tagged t then t $$ tk_pub else True).
  Proof.
    iIntros "Hrel".
    destruct r_t as [ | l_t t' T']; first done. iDestruct "Hrel" as "(#H & ->)".
    iDestruct (sc_rel_ptr_source with "H") as "[%Heq Htag]".
    injection Heq as [= -> ->]. iExists l_s. eauto.
  Qed.
  Lemma rrel_value_source r_t v_s :
    rrel r_t (ValR v_s) -∗
    ∃ v_t, ⌜r_t = ValR v_t⌝ ∗ value_rel v_t v_s.
  Proof.
    iIntros "Hrel". destruct r_t as [ v_t | ]; last done.
    iExists v_t. iFrame "Hrel". done.
  Qed.

  Lemma value_rel_length v_t v_s :
    value_rel v_t v_s -∗ ⌜length v_t = length v_s⌝.
  Proof. iApply big_sepL2_length. Qed.
  Lemma value_rel_empty :
    ⊢ value_rel [] [].
  Proof. by iApply big_sepL2_nil. Qed.

  Lemma value_rel_singleton_source v_t sc_s :
    value_rel v_t [sc_s] -∗ ∃ sc_t, ⌜v_t = [sc_t]⌝ ∗ sc_rel sc_t sc_s.
  Proof.
    iIntros "Hv". iPoseProof (value_rel_length with "Hv") as "%Hlen".
    destruct v_t as [ | sc_t []]; [done | | done ].
    iExists sc_t. iSplitR "Hv"; first done. iRevert "Hv". rewrite /value_rel big_sepL2_singleton. eauto.
  Qed.


  Lemma value_rel_lookup v_t v_s (i : nat) :
    i < length v_t →
    value_rel v_t v_s -∗
    ∃ sc_t sc_s, ⌜v_t !! i = Some sc_t⌝ ∗ ⌜v_s !! i = Some sc_s⌝ ∗ sc_rel sc_t sc_s.
  Proof.
    iIntros (Hi) "Hvrel". rewrite /value_rel big_sepL2_forall.
    iDestruct "Hvrel" as "[%Hlen Hvrel]".
    iSpecialize ("Hvrel" $! i (v_t !!! i) (v_s !!! i)). iExists (v_t !!! i), (v_s !!! i).
    assert (v_t !! i = Some (v_t !!! i)) as Heq.
    { apply list_lookup_lookup_total. apply lookup_lt_is_Some_2. lia. }
    assert (v_s !! i = Some (v_s !!! i)) as Heq'.
    { apply list_lookup_lookup_total. apply lookup_lt_is_Some_2. lia. }
    iSplit; first done. iSplit; first done. iApply "Hvrel"; done.
  Qed.

  Lemma value_rel_lookup_total (v_t v_s : list scalar) (i : nat) :
    i < length v_t → value_rel v_t v_s -∗ sc_rel (v_t !!! i) (v_s !!! i).
  Proof.
    iIntros (Hi) "Hvrel". rewrite /value_rel big_sepL2_forall.
    iDestruct "Hvrel" as "[%Hlen Hvrel]".
    iApply ("Hvrel" $! i (v_t !!! i) (v_s !!! i)).
    all: iPureIntro; apply list_lookup_lookup_total; apply lookup_lt_is_Some_2; lia.
  Qed.

  Lemma tag_values_included_cons sc v t :
    tag_values_included (sc :: v) t ↔ wf_scalar t sc ∧ tag_values_included v t.
  Proof.
    rewrite !tag_values_included_iff. split.
    - intros Ha. split.
      + apply (Ha O). cbn. lia.
      + intros i Hi. apply (Ha (S i)). cbn. lia.
    - intros [Hwf Ha]. intros [ | i] Hi; first done. apply Ha. cbn in Hi. lia.
  Qed.

  Lemma value_rel_tag_values_included_iff v_t v_s t :
    value_rel v_t v_s -∗ ⌜v_t <<t t ↔ v_s <<t t⌝.
  Proof.
    iInduction v_t as [ | sc_t v_t] "IH" forall (v_s); destruct v_s as [ | sc_s v_s].
    - iIntros "_". iPureIntro. done.
    - rewrite value_rel_length. done.
    - iClear "IH". rewrite value_rel_length. done.
    - rewrite /value_rel big_sepL2_cons. iIntros "[Hscrel Hvrel]".
      iPoseProof ("IH" with "Hvrel") as "%IH".
      iPoseProof (sc_rel_wf_scalar_iff _ _ t with "Hscrel") as "%Hsc".
      iPureIntro. rewrite !tag_values_included_cons. naive_solver.
  Qed.
End val_rel.

Class sborG (Σ: gFunctors) := SBorG {
  sborG_gen_progG :> gen_sim_progGS string ectx ectx Σ;
  sborG_stateG :> bor_stateG Σ;
}.

Global Program Instance sborG_simulirisG `{!sborG Σ} : simulirisG (iPropI Σ) bor_lang := {
  state_interp P_t σ_t P_s σ_s T_s :=
    (gen_prog_interp (hG := gen_prog_inG_target) P_t ∗
     gen_prog_interp (hG := gen_prog_inG_source) P_s ∗
     bor_interp sc_rel σ_t σ_s
    )%I;
}.
Next Obligation.
Admitted.

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

Lemma fresh_block_det σ_s σ_t :
  dom (gset loc) σ_s.(shp) = dom (gset loc) σ_t.(shp) →
  fresh_block σ_s.(shp) = fresh_block σ_t.(shp).
Proof. rewrite /fresh_block. intros ->. done. Qed.

(** TODO: these lemmas need a new home *)
Section lemmas.
Context `{!sborG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

Context (Ω : result → result → iProp Σ).

Lemma bor_state_own_access1_read l t tk stk σ :
  bor_state_own l t tk σ →
  σ.(sst) !! l = Some stk →
  ∃ n, access1 stk AccessRead (Tagged t) σ.(scs) = Some (n, stk).
Proof.
  intros Hown. destruct tk; cbn in *.
  - destruct Hown as (st & -> & Hsro). move => [= <-]. by apply tag_SRO_top_access.
  - destruct Hown as (st & Hsst & (opro & st' & H)). simplify_eq. rewrite Hsst => [= <-].
    eapply tag_unique_head_access. eexists; eauto.
  - rewrite Hown => [= <-].
    eapply tag_unique_head_access. eexists; eauto.
Qed.

Lemma memory_read_access1 (stks : stacks) l n t calls :
  (∀ i: nat, (i < n)%nat → ∃ stk, stks !! (l +ₗ i) = Some stk ∧ ∃ m, access1 stk AccessRead (Tagged t) calls = Some (m, stk)) →
  memory_read stks calls l (Tagged t) n = Some stks.
Proof.
  induction n as [ | n IH]; cbn; first done.
  intros Hacc1. destruct (Hacc1 n ltac:(lia)) as (stkn & Hl & (m & Hacc1_n)). rewrite Hl.
  cbn. rewrite Hacc1_n. cbn.
  rewrite insert_id; last done. apply IH. intros i Hi. apply Hacc1. lia.
Qed.


Lemma lookup_union_Some_l' `{EqDecision K} `{Countable K} V (M1 M2 : gmap K V) (k : K) (v : V) :
  (M1 ∪ M2) !! k = Some v → M2 !! k = None → M1 !! k = Some v.
Proof.
  destruct (M1 !! k) as [ v' | ] eqn:Hv'.
  - specialize (lookup_union_Some_l M1 M2 _ _ Hv') as ->. move => [= ->]. done.
  - rewrite lookup_union_r; last done. congruence.
Qed.
Lemma lookup_union_is_Some `{EqDecision K} `{Countable K} V (M1 M2 : gmap K V) (k : K) :
  is_Some ((M1 ∪ M2) !! k) ↔ is_Some (M1 !! k) ∨ is_Some (M2 !! k).
Proof.
  split.
  - intros (v & Hv). destruct (M1 !! k) eqn:HM1; first by eauto.
    right. erewrite <-lookup_union_r; eauto.
  - intros [(v & HM1) | (v & HM2)].
    + rewrite (lookup_union_Some_l _ _ _ _ HM1); eauto.
    + destruct (M1 !! k) eqn:HM1. { rewrite (lookup_union_Some_l _ _ _ _ HM1); eauto. }
      rewrite lookup_union_r; eauto.
Qed.

Lemma dom_agree_on_tag_union M1_t M1_s M2_t M2_s t :
  dom_agree_on_tag M1_t M1_s t → dom_agree_on_tag M2_t M2_s t →
  dom_agree_on_tag (M1_t ∪ M2_t) (M1_s ∪ M2_s) t.
Proof.
  intros [H1a H1b] [H2a H2b]. split; intros l; rewrite !lookup_union_is_Some; naive_solver.
Qed.

Lemma dom_agree_on_tag_array_tag_map l t v_t v_s :
  length v_t = length v_s →
  dom_agree_on_tag (array_tag_map l t v_t) (array_tag_map l t v_s) t.
Proof.
  intros Hlen. split; intros l'.
  - intros (_ & (i & Hi & ->))%array_tag_map_lookup2. rewrite array_tag_map_lookup_Some; last lia.
    apply lookup_lt_is_Some_2. lia.
  - intros (_ & (i & Hi & ->))%array_tag_map_lookup2. rewrite array_tag_map_lookup_Some; last lia.
    apply lookup_lt_is_Some_2. lia.
Qed.

Lemma array_tag_map_lookup_None t t' l v :
  t ≠ t' → ∀ l', array_tag_map l t v !! (t', l') = None.
Proof.
  intros Hneq l'. destruct (array_tag_map l t v !! (t', l')) eqn:Harr; last done.
  specialize (array_tag_map_lookup1 l t v t' l' ltac:(eauto)) as [Heq _]; congruence.
Qed.

Lemma dom_agree_on_tag_not_elem M_t M_s t :
  (∀ l, M_t !! (t, l) = None) → (∀ l, M_s !! (t, l) = None) →
  dom_agree_on_tag M_t M_s t.
Proof. intros Ht Hs. split; intros l; rewrite Ht Hs; congruence. Qed.

Lemma retag_mut_loc_controlled σ c l ot T mut α' rk i sc :
  let nt := σ.(snp) in
  let pk := RefPtr mut in
  let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
  (if mut is Immutable then is_freeze T else True) →
  retag σ.(sst) σ.(snp) σ.(scs) c l ot rk pk T = Some (Tagged nt, α', S σ.(snp)) →
  (is_two_phase rk = false) →
  (i < tsize T)%nat →
  σ.(shp) !! (l +ₗ i) = Some sc →
  loc_controlled (l +ₗ i) nt tk sc (mkState σ.(shp) α' σ.(scs) (S σ.(snp)) σ.(snc)).
Proof.
  intros nt pk tk Hfreeze Hretag Hrk Hi Hsc Hpre. split; last done.
  destruct mut.
  * (* unique *)
    destruct Hpre as (st & pm' & opro & Hst & Hit & Hpm'). exists st. split; first done.
    rewrite /retag Hrk in Hretag.
    have EqRT':
      retag_ref σ.(sst) σ.(scs) σ.(snp) l ot T (UniqueRef false) (adding_protector rk c) =
        Some (Tagged nt, α', S nt) by done.
    destruct (tag_on_top_retag_ref_uniq _ _ _ _ _ _ _ _ _ _ EqRT' i ltac:(lia))
      as [pro1 Eqstk1]. rewrite Hst /= in Eqstk1.
    clear -Eqstk1. destruct st as [|? stk1]; [done|].
    simpl in Eqstk1. simplify_eq. by exists pro1, stk1.
  * (* shared *)
    destruct Hpre as (stk' & pm' & pro & Eqstk' & In' & NDIS). simpl in Eqstk'.
    exists stk'. split; [done|].
    have EqRT':
      retag_ref σ.(sst) σ.(scs) σ.(snp) l ot T SharedRef (adding_protector rk c) = Some (Tagged nt, α', S nt) by done.
    have HTOP := (tag_on_top_retag_ref_shr _ _ _ _ _ _ _ _ _ _ Hfreeze EqRT' i ltac:(lia)).
    clear -HTOP Eqstk'.
    apply tag_on_top_shr_active_SRO in HTOP as (?&?&?). by simplify_eq.
Qed.

Lemma retag_loc_controlled_preserved σ c l l' t tk' ot T pk rk α' nt nxtp' sc :
  state_wf σ →
  retag σ.(sst) σ.(snp) σ.(scs) c l ot rk pk T = Some (nt, α', nxtp') →
  (Tagged t = ot → tk' = tk_pub) →
  (t < σ.(snp))%nat →
  loc_controlled l' t tk' sc σ →
  loc_controlled l' t tk' sc (mkState σ.(shp) α' σ.(scs) nxtp' σ.(snc)).
Proof.
  intros Hwf Hretag Hneq Hlt Hcontrolled.
  intros Hpre. destruct tk'.
  * destruct Hpre as (stk' & pm' & pro & Eqstk' & In' & ND).
    destruct (retag_item_in _ _ _ _ _ _ _ _ _ _ _ _ Hretag _ _ t _ Eqstk' In')
      as (stk & Eqstk & In); [done..|].

    destruct Hcontrolled as (Hown & Hl'). { simpl; naive_solver. }
    cbn. split; last done.
    exists stk'. split; [done|].
    destruct Hown as (stk1 & Eqstk1 & HTOP).
    rewrite Eqstk1 in Eqstk. simplify_eq.
    move : HTOP.
    have ND2 := proj2 (state_wf_stack_item _ Hwf _ _ Eqstk1).
    by apply (retag_item_active_SRO_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag _ _ _ _ _ ND2 Eqstk1 Eqstk' In In').
  * destruct Hpre as (stk' & pm' & pro & Eqstk' & In' & ND).
    destruct (retag_item_in _ _ _ _ _ _ _ _ _ _ _ _ Hretag _ _ t _ Eqstk' In')
      as (stk & Eqstk & In); [done..|].
    destruct Hcontrolled as (Hown & Hl'); [simpl; naive_solver|].
    split; last done. cbn.
    exists stk'. split; [done|].
    destruct Hown as (stk1 & Eqstk1 & opro1 & HTOP).
    rewrite Eqstk1 in Eqstk. simplify_eq.
    have ND2 := proj2 (state_wf_stack_item _ Hwf _ _ Eqstk1).
    assert (opro1 = pro ∧ pm' = Unique) as [].
    { have In1 : mkItem Unique (Tagged t) opro1 ∈ stk.
      { destruct HTOP as [? HTOP]. rewrite HTOP. by left. }
      have EQ := stack_item_tagged_NoDup_eq _ _ _ t ND2 In1 In eq_refl eq_refl.
      by simplify_eq. } subst opro1 pm'. exists pro.
    have NEq: Tagged t ≠ ot.
    { intros <-. specialize (Hneq eq_refl). congruence. }
    move : HTOP.
    by apply (retag_item_head_preserving _ _ _ _ _ _ _ _ _ _ _ _ Hretag
                _ _ _ _ _ ND2 Eqstk1 Eqstk' NEq In').
  * clear Hpre. specialize (Hcontrolled I) as (Hown & Hl'). split; last done.
    move : Hown. cbn.
    have NEq: ot ≠ Tagged t.
    { intros ->. specialize (Hneq eq_refl). congruence. }
    move : NEq. by eapply retag_Some_local.
Qed.
End lemmas.

