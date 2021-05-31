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

Definition state_upd_mem (f : mem → mem) σ :=
  mkState (f σ.(shp)) σ.(sst) σ.(scs) σ.(snp) σ.(snc).
Definition state_upd_stacks (f : stacks → stacks) σ :=
  mkState σ.(shp) (f σ.(sst)) σ.(scs) σ.(snp) σ.(snc).



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

    Definition pub_loc σ_t σ_s (l : loc) : iProp Σ :=
      ∀ sc_t, ⌜σ_t.(shp) !! l = Some sc_t⌝ → ∃ sc_s, ⌜σ_s.(shp) !! l = Some sc_s⌝ ∗ sc_rel sc_t sc_s.
    Definition priv_loc t (l : loc) : Prop :=
      ∃ tk, M_tag !! t = Some (tk, tt) ∧ is_Some (M_t !! (t, l)) ∧
        (* local *)
        (tk = tk_local ∨
        (* unique with protector *)
        (tk = tk_unq ∧ ∃ c M' L, Mcall_t !! c = Some M' ∧ M' !! t = Some L ∧ l ∈ L)).

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
    state_rel Mtag Mt Mcall σ_t σ_s -∗ ⌜σ_s.(snp) = σ_t.(snp) ∧ σ_s.(snc) = σ_t.(snc) ∧ σ_s.(scs) = σ_t.(scs)⌝.
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
        pid < σ.(snp) ∧
        (* for every protected location [l], there needs to be a protector in the stack *)
        ∀ (l : loc), l ∈ S → ∃ s pm, σ.(sst) !! l = Some s ∧
          mkItem pm (Tagged pid) (Some c) ∈ s ∧ pm ≠ Disabled.

  Definition call_set_in' (M : gmap call_id (gmap ptr_id (gset loc))) c t l :=
    ∃ M' L, M !! c = Some M' ∧ M' !! t = Some L ∧ l ∈ L.
  Definition call_set_in (M : gmap ptr_id (gset loc)) t l :=
    ∃ L, M !! t = Some L ∧ l ∈ L.
  Lemma call_set_interp_access M σ c t l :
    call_set_interp M σ →
    call_set_in' M c t l →
    c ∈ σ.(scs) ∧ t < σ.(snp) ∧ ∃ stk pm, σ.(sst) !! l = Some stk ∧
      mkItem pm (Tagged t) (Some c) ∈ stk ∧ pm ≠ Disabled.
  Proof.
    intros Hinterp (M' & L & HM_some & HM'_some & Hin).
    specialize (Hinterp _ _ HM_some) as (? & Hinterp).
    specialize (Hinterp _ _ HM'_some) as (? & Hinterp).
    specialize (Hinterp _ Hin). done.
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

  Definition bor_state_own (l : loc) (t : ptr_id) (tk : tag_kind) (σ : state) :=
    match tk with
    | tk_local => σ.(sst) !! l = Some ([mkItem Unique (Tagged t) None])
    | tk_unq => ∃ st, σ.(sst) !! l = Some st ∧ ∃ opro st',
        st = mkItem Unique (Tagged t) opro :: st'
    | tk_pub => ∃ st, σ.(sst) !! l = Some st ∧ t ∈ active_SRO st
    end.

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
  (*Lemma loc_controlled_mem_insert_unowned l t tk sc sc' σ : *)
    (*¬ bor_state_pre l t tk *)
    (*loc_controlled l t tk sc σ →*)
    (*loc_controlled l t tk sc (state_upd_mem <[l := sc']> σ).*)
  (*Proof.*)
    (*intros (s & Hsome & Him). exists s; split; first done. *)
    (*intros [Hownw Hmem]%Him. split; first done. *)
    (*rewrite lookup_insert; done. *)
  (*Qed.*)

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
    ∀ (t : ptr_id) tk, M !! t = Some (tk, ()) →
      (* tags are valid *)
      (t < σ_t.(snp))%nat ∧ (t < σ_s.(snp))%nat ∧
      (* at all locations, the values agree, and match the physical state assuming the tag currently has control over the location *)
      (∀ l sc_t, M_t !! (t, l) = Some sc_t → loc_controlled l t tk sc_t σ_t) ∧
      (∀ l sc_s, M_s !! (t, l) = Some sc_s → loc_controlled l t tk sc_s σ_s) ∧
      dom_agree_on_tag M_t M_s t.
End heap_defs.


Notation "p '$$' tk" := (tkmap_elem tag_name p tk ()) (at level 50).

Notation "l '↦t[unq]{' t } sc" := (ghost_map_elem heap_view_target_name (t, l) (DfracOwn 1) sc)
  (at level 20, format "l  ↦t[unq]{ t }  sc") : bi_scope.
Notation "l '↦s[unq]{' t } sc" := (ghost_map_elem heap_view_source_name (t, l) (DfracOwn 1) sc)
  (at level 20, format "l  ↦s[unq]{ t }  sc") : bi_scope.
Notation "l '↦t[local]{' t } sc" := (ghost_map_elem heap_view_target_name (t, l) (DfracOwn 1) sc)
  (at level 20, format "l  ↦t[local]{ t }  sc") : bi_scope.
Notation "l '↦s[local]{' t } sc" := (ghost_map_elem heap_view_source_name (t, l) (DfracOwn 1) sc)
  (at level 20, format "l  ↦s[local]{ t }  sc") : bi_scope.
Notation "l '↦t[pub]{' t } sc" := (ghost_map_elem heap_view_target_name (t, l) (DfracDiscarded) sc)
  (at level 20, format "l  ↦t[pub]{ t }  sc") : bi_scope.
Notation "l '↦s[pub]{' t } sc" := (ghost_map_elem heap_view_source_name (t, l) (DfracDiscarded) sc)
  (at level 20, format "l  ↦s[pub]{ t }  sc") : bi_scope.


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
    bor_interp σ_t σ_s -∗ ⌜σ_s.(snp) = σ_t.(snp) ∧ σ_s.(snc) = σ_t.(snc) ∧ σ_s.(scs) = σ_t.(scs) ∧ state_wf σ_s ∧ state_wf σ_t⌝.
  Proof.
    iIntros "(% & % & % & % & ? & Hstate & _ & _ & % & %)".
    iPoseProof (state_rel_get_pure with "Hstate") as "%".
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

Definition tk_to_frac (tk : tag_kind) :=
  match tk with
  | tk_pub => DfracDiscarded
  | _ => DfracOwn 1
  end.
Notation "l '↦t∗[' tk ']{' t } scs" := (array_tag heap_view_target_name t l (tk_to_frac tk) scs)
  (at level 20, format "l  ↦t∗[ tk ]{ t }  scs") : bi_scope.
Notation "l '↦s∗[' tk ']{' t } scs" := (array_tag heap_view_source_name t l (tk_to_frac tk) scs)
  (at level 20, format "l  ↦s∗[ tk ]{ t }  scs") : bi_scope.

Notation "l '↦t∗[unq]{' t } scs" := (array_tag heap_view_target_name t l (DfracOwn 1) scs)
  (at level 20, format "l  ↦t∗[unq]{ t }  scs") : bi_scope.
Notation "l '↦s∗[unq]{' t } scs" := (array_tag heap_view_source_name t l (DfracOwn 1) scs)
  (at level 20, format "l  ↦s∗[unq]{ t }  scs") : bi_scope.
Notation "l '↦t∗[local]{' t } scs" := (array_tag heap_view_target_name t l (DfracOwn 1) scs)
  (at level 20, format "l  ↦t∗[local]{ t }  scs") : bi_scope.
Notation "l '↦s∗[local]{' t } scs" := (array_tag heap_view_source_name t l (DfracOwn 1) scs)
  (at level 20, format "l  ↦s∗[local]{ t }  scs") : bi_scope.
Notation "l '↦t∗[pub]{' t } scs" := (array_tag heap_view_target_name t l (DfracDiscarded) scs)
  (at level 20, format "l  ↦t∗[pub]{ t }  scs") : bi_scope.
Notation "l '↦s∗[pub]{' t } scs" := (array_tag heap_view_source_name t l (DfracDiscarded) scs)
  (at level 20, format "l  ↦s∗[pub]{ t }  scs") : bi_scope.

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
      l_t ↦t∗[local]{t} repeat ScPoison (tsize T) ∗
      l_s ↦s∗[local]{t} repeat ScPoison (tsize T).
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
    wf_scalar σ sc →
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

  Lemma heap_local_access_target σ_t σ_s (t : ptr_id) l  sc :
    bor_interp σ_t σ_s -∗
    l ↦t[local]{t} sc -∗
    t $$ tk_local -∗
    ⌜σ_t.(shp) !! l = Some sc⌝ ∗
    ⌜σ_t.(sst) !! l = Some [mkItem Unique (Tagged t) None]⌝ ∗
    ⌜wf_scalar σ_t sc⌝ ∗
    (∀ sc',
      ⌜wf_scalar σ_t sc'⌝ -∗
      (*stack_wf st' σ_t -∗ *)
      |==>
      bor_interp (state_upd_mem (<[l := sc']>) σ_t) σ_s ∗
      l ↦t[local]{t} sc').
  Proof.
    iIntros "(% & % & % & % & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & Hsrel & ? & %Htag_interp & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ht & Hs & Hagree).
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    specialize (Ht _ _ Ht_lookup) as Hcontrol.
    specialize (loc_controlled_local _ _ _ _ Hcontrol) as (Hstack & Hmem).
    iSplitR; first done. iSplitR; first done.
    iSplitR. { iPureIntro. intros tg l' ->.
      destruct tg as [tg | ]; last done.
      eapply state_wf_mem_tag; done.
    }

    iIntros (sc') "%Hwf_sc".
    iMod (ghost_map_update sc' with "Htag_t_auth Hp") as "[Htag_t_auth $]".
    iModIntro. rewrite /bor_interp.
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
    intros t' tk' (? & ? & H')%Htag_interp. do 2 (split; first done).
    destruct H' as (Ha_t & Ha_s & Hagree').
    split_and!; [ | done | ].
    - intros l' sc_t.
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
      + rewrite lookup_insert => [= ->]. by eapply loc_controlled_mem_insert, Ha_t.
      + rewrite lookup_insert_ne; last congruence. intros ?.
        eapply loc_controlled_mem_insert_ne; [done | by apply Ha_t].
    - destruct (decide (t = t')) as [<- | Hneq].
      + eapply dom_agree_on_tag_upd_target; eauto.
      + eapply dom_agree_on_tag_upd_ne_target; eauto.
  Qed.

  Lemma heap_local_accessN_target' σ_t σ_s (t : ptr_id) l scs :
    bor_interp σ_t σ_s -∗
    l ↦t∗[local]{t} scs -∗
    t $$ tk_local -∗
    ⌜∀ i : nat, (i < length scs)%nat → σ_t.(shp) !! (l +ₗ i) = scs !! i ⌝ ∗
    ⌜∀ i:nat, (i < length scs)%nat → σ_t.(sst) !! (l +ₗ i) = Some [mkItem Unique (Tagged t) None]⌝ ∗
    (∀ scs',
      ⌜length scs' = length scs⌝ -∗
      ⌜Forall (wf_scalar σ_t) scs'⌝ -∗
      (*stack_wf st' σ_t -∗ *)
      |==>
      bor_interp (state_upd_mem (λ m, heap_array l scs' ∪ m) σ_t) σ_s ∗
      l ↦t∗[local]{t} scs').
  Proof.
  Admitted.

  Lemma heap_local_accessN_target σ_t σ_s (t : ptr_id) l scs :
    bor_interp σ_t σ_s -∗
    l ↦t∗[local]{t} scs -∗
    t $$ tk_local -∗
    ⌜read_mem l (length scs) σ_t.(shp) = Some scs⌝ ∗
    ⌜∀ i:nat, (i < length scs)%nat → σ_t.(sst) !! (l +ₗ i) = Some [mkItem Unique (Tagged t) None]⌝ ∗
    ⌜scs <<t σ_t.(snp)⌝ ∗
    (∀ scs',
      ⌜length scs' = length scs⌝ -∗
      ⌜scs' <<t σ_t.(snp) ⌝ -∗
      (*stack_wf st' σ_t -∗ *)
      |==>
      bor_interp (state_upd_mem (write_mem l scs') σ_t) σ_s ∗
      l ↦t∗[local]{t} scs').
  Proof.
  Admitted.

  Lemma heap_local_readN_target σ_t σ_s (t : ptr_id) l scs :
    bor_interp σ_t σ_s -∗
    l ↦t∗[local]{t} scs -∗
    t $$ tk_local -∗
    ⌜read_mem l (length scs) σ_t.(shp) = Some scs⌝ ∗
    ⌜∀ i:nat, (i < length scs)%nat → σ_t.(sst) !! (l +ₗ i) = Some [mkItem Unique (Tagged t) None]⌝ ∗
    ⌜scs <<t σ_t.(snp)⌝.
  Proof.
  Admitted.

  Lemma heap_local_access_source σ_t σ_s (t : ptr_id) l sc :
    bor_interp σ_t σ_s -∗
    l ↦s[local]{t} sc -∗
    t $$ tk_local -∗
    ⌜σ_s.(shp) !! l = Some sc⌝ ∗
    ⌜σ_s.(sst) !! l = Some [mkItem Unique (Tagged t) None]⌝ ∗
    ⌜wf_scalar σ_s sc⌝ ∗
    (∀ sc',
      ⌜wf_scalar σ_s sc' ⌝ -∗
      (*stack_wf st' σ_t -∗ *)
      |==>
      bor_interp σ_t (state_upd_mem (<[l := sc']>) σ_s) ∗
      l ↦s[local]{t} sc').
  Proof.
  Admitted.

  Lemma heap_local_accessN_source σ_t σ_s (t : ptr_id) l scs :
    bor_interp σ_t σ_s -∗
    l ↦s∗[local]{t} scs -∗
    t $$ tk_local -∗
    ⌜read_mem l (length scs) σ_s.(shp) = Some scs⌝ ∗
    ⌜∀ i:nat, (i < length scs)%nat → σ_s.(sst) !! (l +ₗ i) = Some [mkItem Unique (Tagged t) None]⌝ ∗
    ⌜scs <<t σ_s.(snp)⌝ ∗
    (∀ scs',
      ⌜length scs' = length scs⌝ -∗
      ⌜scs' <<t σ_s.(snp)⌝ -∗
      (*stack_wf st' σ_t -∗ *)
      |==>
      bor_interp σ_t (state_upd_mem (write_mem l scs') σ_s) ∗
      l ↦s∗[local]{t} scs').
  Proof.
  Admitted.

  Lemma heap_local_readN_source σ_t σ_s (t : ptr_id) l scs :
    bor_interp σ_t σ_s -∗
    l ↦s∗[local]{t} scs -∗
    t $$ tk_local -∗
    ⌜read_mem l (length scs) σ_s.(shp) = Some scs⌝ ∗
    ⌜∀ i:nat, (i < length scs)%nat → σ_s.(sst) !! (l +ₗ i) = Some [mkItem Unique (Tagged t) None]⌝ ∗
    ⌜scs <<t σ_s.(snp)⌝.
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
  - by eapply protector_access_eq.
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
  Admitted.

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
  Lemma sc_rel_poison_source sc_t :
    sc_rel sc_t (ScPoison) -∗ False.
  Proof. iIntros "Hrel". destruct sc_t; done. Qed.
  Lemma sc_rel_cid_source sc_t c :
    sc_rel sc_t (ScCallId c) -∗ ⌜sc_t = ScCallId c⌝.
  Proof. iIntros "Hrel"; destruct sc_t; [done.. | ]. by iDestruct "Hrel" as "->". Qed.

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
End val_rel.

Class sborG (Σ: gFunctors) := SBorG {
  sborG_gen_progG :> gen_sim_progG string ectx ectx Σ;
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


Section lifting.
Context `{!sborG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

Context (Ω : result → result → iProp Σ).

Lemma fresh_block_det σ_s σ_t :
  dom (gset loc) σ_s.(shp) = dom (gset loc) σ_t.(shp) →
  fresh_block σ_s.(shp) = fresh_block σ_t.(shp).
Proof. rewrite /fresh_block. intros ->. done. Qed.

(* reflexivity steps *)
Lemma sim_alloc_local T Φ π :
  (∀ t l_t l_s, t $$ tk_local -∗
    l_t ↦t∗[local]{t} repeat ScPoison (tsize T) -∗
    l_s ↦s∗[local]{t} repeat ScPoison (tsize T) -∗
    Place l_t (Tagged t) T ⪯{π, Ω} Place l_s (Tagged t) T [{ Φ }]) -∗
  Alloc T ⪯{π, Ω} Alloc T [{ Φ }].
Proof.
  iIntros "Hsim".
  iApply sim_lift_head_step_both. iIntros (??????) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iPoseProof (bor_interp_get_pure with "Hbor") as "%Hp".
  iModIntro. iSplitR.
  { iPureIntro. do 3 eexists. econstructor 2; econstructor. }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  inv_head_step.
  set (l_s := (fresh_block σ_s.(shp), 0)).
  iMod (heap_local_alloc _ _ _ T with "Hbor") as "(Hbor & Htag & Htarget & Hsource)".
  iModIntro.
  iExists (Place l_s (Tagged (σ_t.(snp))) T), [], (mkState (init_mem l_s (tsize T) σ_s.(shp)) (init_stacks σ_s.(sst) l_s (tsize T) (Tagged σ_s.(snp))) σ_s.(scs) (S σ_s.(snp)) σ_s.(snc)).
  iFrame. iSplitR.
  { iPureIntro. destruct Hp as (<- & _).  econstructor 2; econstructor. }
  iSplitL; last by iApply big_sepL2_nil.
  iApply ("Hsim" with "Htag Htarget Hsource").
Qed.

Lemma sim_alloc_public T Φ π :
  (∀ t l_t l_s, t $$ tk_pub -∗
    rrel (PlaceR l_t (Tagged t) T) (PlaceR l_s (Tagged t) T) -∗
    Place l_t (Tagged t) T ⪯{π, Ω} Place l_s (Tagged t) T [{ Φ }]) -∗
  Alloc T ⪯{π, Ω} Alloc T [{ Φ }].
Proof.
Admitted.

(* TODO: local ownership makes strong assertions: 
  we also have to deallocate the corresponding ghost state *)
(*Lemma sim_free_local : *)

  (*Free (Place l t T_t) ⪯{π, Ω*)

Lemma sim_free_public T_t T_s l_t l_s bor_t bor_s Φ π :
  rrel (PlaceR l_t bor_t T_t) (PlaceR l_s bor_s T_s) -∗
  #[☠] ⪯{π, Ω} #[☠] [{ Φ }] -∗
  Free (Place l_t bor_t T_t) ⪯{π, Ω} Free (Place l_s bor_s T_s) [{ Φ }].
Proof.
Admitted.

Lemma head_copy_inv (P : prog) l t T σ e σ' efs :
  head_step P (Copy (PlaceR l t T)) σ e σ' efs →
  ∃ v α',
  efs = [] ∧ (read_mem l (tsize T) (shp σ) = Some v) ∧
  (memory_read (sst σ) (scs σ) l t (tsize T) = Some α') ∧
  v <<t snp σ ∧
  σ' = mkState (shp σ) α' (scs σ) (snp σ) (snc σ) ∧
  e = (ValR v).
Proof. intros Hhead. inv_head_step. eauto 8. Qed.

Lemma sim_copy_public_controlled_update σ l l' (bor : tag) (T : type) (α' : stacks) (t : ptr_id) (tk : tag_kind) (sc : scalar)
  (ACC: memory_read σ.(sst) σ.(scs) l bor (tsize T) = Some α')
  (Hwf : state_wf σ)
  (Hlocal : ∀ stk n t' stk' kind, σ.(sst) !! l' = Some stk →
            access1 stk kind t' σ.(scs) = Some (n, stk') →
            tk = tk_local →
            t' = Tagged t ∧ stk' = stk) :
  let σ' := mkState σ.(shp) α' σ.(scs) σ.(snp) σ.(snc) in
  loc_controlled l' t tk sc σ →
  loc_controlled l' t tk sc σ'.
Proof.
  intros σ' Hcontrol Hpre.
  (* need to update the loc_controlled.
    intuitive justification:
    - if l is not affected by the Copy, we are fine.
    - if it is affected, we already know that we accessed with a public tag [bor_s].
      In case this current tag [t] is local, we have a contradiction as the tags must be the same.
      In case this current tag [t] is unique: if the item is in the stack, then it must still be because it would have been protected
      In case this current tag [t] is public: it should still be there, as it is not incompatible with our copy access (we leave SharedROs there).
  *)

  specialize (for_each_access1 _ _ _ _ _ _ _ ACC) as Hsub.
  assert (bor_state_pre l' t tk σ) as H.
  { move : Hpre. destruct tk; [ | | done ].
    all: intros (st' & pm & opro & Hα'_some & Hit & Hpm);
      specialize (Hsub _ _ Hα'_some) as (st & Hα_some & Hsublist & _);
      exists st, pm, opro;
      split_and!; [ done | | done]; specialize (Hsublist _ Hit) as ([] & Hit' & Heq & Heq' & Hperm'); simpl in *;
      rewrite Heq Heq' -Hperm'; done.
  }
  specialize (Hcontrol H) as [Hown Hmem].
  split; last done.
  move: Hpre.
  destruct tk; simpl.
  * (* goal: use access1_active_SRO_preserving *)
    intros (st & pm & opro & Hsome_st & Hit & Hpm). exists st. split; first done.
    destruct Hown as (st'' & Hsome_st'' & Hactive).
    destruct (for_each_lookup_case _ _ _ _ _ ACC _ _ _ Hsome_st'' Hsome_st) as [-> | [Hacc _]]; first done.
    destruct access1 as [ [n st']| ] eqn:Hacc_eq; simpl in Hacc; simplify_eq.
    eapply access1_active_SRO_preserving; [ | done | apply Hacc_eq | done ].
    eapply Hwf; done.
  * intros (st & pm & opro & Hsome_st & Hit & Hpm).
    destruct Hown as (st' & Hsome_st' & opro' & st'0 & Heq).
    destruct (for_each_lookup_case _ _ _ _ _ ACC _ _ _ Hsome_st' Hsome_st) as [-> | [Hacc _]]; first by eauto.
    destruct access1 as [ [n st'']| ] eqn:Hacc_eq; simpl in Hacc; simplify_eq.
    exists st. split; first done. exists opro'.
    eapply access1_head_preserving; [ eapply Hwf; done| done | | apply Hacc_eq| eexists; done ].
    (* need that opro = opro' *)
    specialize (access1_read_eq _ _ _ _ t _ _ _ ltac:(eapply Hwf; done) Hacc_eq ltac:(by left) Hit Hpm ltac:(done) ltac:(done)) as Heq.
    simplify_eq. done.
  * intros _. simpl in Hown.
    specialize (for_each_access1_lookup_inv _ _ _ _ _ _ _ ACC _ _ Hown) as (st' & Hst' & [[n' Hacc_eq] | Heq]).
    2: { rewrite Heq. done. }
    specialize (Hlocal _ _ _ _ _ Hown Hacc_eq eq_refl) as (-> & ->).
    done.
Qed.


Lemma sim_copy_public Φ π l_t bor_t T_t l_s bor_s T_s :
  rrel (PlaceR l_t bor_t T_t) (PlaceR l_s bor_s T_s) -∗
  (∀ v_t v_s, value_rel v_t v_s -∗ v_t ⪯{π, Ω} ValR v_s [{ Φ }]) -∗
  Copy (PlaceR l_t bor_t T_t) ⪯{π, Ω} Copy (PlaceR l_s bor_s T_s) [{ Φ }].
Proof.
  iIntros "#Hrel Hsim".
  iApply sim_lift_head_step_both. iIntros (??????) "[(HP_t & HP_s & Hbor) %Hsafe]".
  iModIntro.
  destruct Hsafe as [Hpool Hsafe].
  specialize (pool_safe_irred _ _ _ _ _ _  _ Hsafe Hpool ltac:(done)) as (v_s & Hread_s & (α' & Hstack_s) & Hwell_tagged_s).
  iDestruct "Hrel" as "[[<- Hrel] <-]".
  iDestruct "Hbor" as "(% & % & % & % & (Hc & Htag_auth & Htag_t_auth & Htag_s_auth) & #Hsrel & %Hcall_interp & %Htag_interp & %Hwf_s & %Hwf_t)".

  iAssert (⌜∀ i : nat, (i < tsize T_t)%nat → is_Some (shp σ_t !! (l_t +ₗ i))⌝)%I as "%Hsome_target".
  { iPoseProof (state_rel_heap_lookup_Some with "Hsrel") as "%Hl".
    iPureIntro. (* use read_mem_is_Some' *)
    specialize (proj2 (read_mem_is_Some' l_t (tsize T_t) σ_s.(shp)) ltac:(eauto)) as Him.
    intros i Hi. apply Hl, elem_of_dom. by eapply Him.
  }

  (* prove that it is a public location *)
  iAssert (⌜untagged_or_public M_tag bor_t ∧ bor_t = bor_s⌝)%I as %Hpub.
  { iDestruct "Hrel" as "[[-> ->] | (%t1 & %t2 & -> & -> & <- & Hpub)]"; first done.
    iPoseProof (tkmap_lookup with "Htag_auth Hpub") as "%". done.
  }
  destruct Hpub as [Hpub ->].

  (* prove reducibility *)
  iPoseProof (state_rel_stacks_eq with "Hsrel") as "%Hstacks_eq".
  iPoseProof (state_rel_calls_eq with "Hsrel") as "%Hcalls_eq".
  iSplitR.
  { iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom".
    iPureIntro.
    destruct (read_mem_is_Some l_t (tsize T_t) σ_t.(shp)) as [v_t Eqvt].
    { intros m. rewrite Hdom. apply (read_mem_is_Some' l_t (tsize T_t) σ_s.(shp)). by eexists. }
    have Eqα'2: memory_read σ_t.(sst) σ_t.(scs) l_t bor_s (tsize T_t) = Some α'.
    { rewrite -Hstacks_eq -Hcalls_eq. done. }
    eexists; eexists; eexists. eapply copy_head_step'; eauto.
  }
  (* we keep the head_step hypotheses to use the [head_step_wf] lemma below *)
  iIntros (e_t' efs_t σ_t') "%Hhead_t".
  specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead_t) as (v_t & α'0 & -> & COPY & ACC & BOR & -> & ->).
  iAssert (⌜α'0 = α'⌝)%I as "->".
  { iPureIntro. move : ACC Hstack_s. rewrite Hcalls_eq Hstacks_eq. congruence. }
  iModIntro.
  pose (σ_s' := (mkState (shp σ_s) α' (scs σ_s) (snp σ_s) (snc σ_s))).
  assert (Hhead_s : head_step P_s (Copy (Place l_t bor_s T_t)) σ_s (ValR v_s) σ_s' []).
  { eapply copy_head_step'; eauto. }
  iExists (Val v_s), [], σ_s'. iSplitR; first done.
  iFrame "HP_t HP_s".

  iSplitR "Hsim".
  {
    (* re-establish the invariants *)
    iExists M_call, M_tag, M_t, M_s.
    iFrame "Hc Htag_auth Htag_t_auth Htag_s_auth".
    iSplit; last iSplit; last iSplit; last iSplit.
    - (* state rel *)
      iPoseProof (state_rel_dom_eq with "Hsrel") as "%Hdom".
      iPoseProof (state_rel_snp_eq with "Hsrel") as "%Hsnp".
      iPoseProof (state_rel_snc_eq with "Hsrel") as "%Hsnc".
      iSplit; first done. iSplit; first done. iSplit; first done.
      iSplit; first done. iSplit; first done.
      simpl. iIntros (l) "Hs". iPoseProof (state_rel_pub_or_priv with "Hs Hsrel") as "$".
    - (* call invariant *)
      iPureIntro. intros c M' HM'_some.
      specialize (Hcall_interp c M' HM'_some) as (Hin & Hprot).
      split; first by apply Hin. intros pid L HL_some. specialize (Hprot pid L HL_some) as [Hpid Hprot].
      split; first by apply Hpid. intros l Hin_l.
      specialize (Hprot l Hin_l) as (stk & pm & Hstk_some & Hin_stack & Henabled).
      (* we use that reads must preserve active protectors (but note that the stack may have changed, even when there is an active protector) *)
      specialize (for_each_access1_active_preserving _ _ _ _ _ _ _ ACC l stk Hstk_some) as (stk' & Hstk'_some & Hac_pres).
      exists stk', pm. split; last split; [ done | by apply Hac_pres| done ].
    - (* tag invariant *)
      iPureIntro.
      intros t tk Htk_some. destruct (Htag_interp t tk Htk_some) as (Hsnp_lt_t & Hsnp_lt_s & Hctrl_t & Hctrl_s & Hag).
      split_and!; [ done | done | | | done ].
      + intros l sc_t Hsc_t. eapply sim_copy_public_controlled_update; [ by eauto .. | | by eauto].
        intros stk n t' stk' kind Hstk Hacc1 ->.
        eapply (local_access_eq _ _ _ _ _ _ _ _ _ _ _ _ Hstk Hacc1 Htk_some ltac:(eauto) Htag_interp).
      + intros l sc_s Hsc_s. eapply sim_copy_public_controlled_update; [ by eauto .. | | by eauto].
        intros stk n t' stk' kind Hstk Hacc1 ->.
        rewrite Hstacks_eq in Hstk. rewrite Hcalls_eq in Hacc1.
        assert (is_Some (M_t !! (t, l))) as Ht_some.
        { apply Hag. eauto. }
        eapply (local_access_eq _ _ _ _ _ _ _ _ _ _ _ _ Hstk Hacc1 Htk_some Ht_some Htag_interp).
    - (* source state wf *)
      iPureIntro. eapply head_step_wf; done.
    - (* target state wf *)
      iPureIntro. eapply head_step_wf; done.
  }
  iSplitL; last done.

  iApply "Hsim".
  (* proving the value relation *)
  specialize (read_mem_values _ _ _ _ COPY) as [Hlen_t Hv_t].
  specialize (read_mem_values _ _ _ _ Hread_s) as [Hlen_s Hv_s].
  iApply big_sepL2_intuitionistically_forall; first lia.
  iModIntro. iIntros (i sc_t sc_s) "%Hs_t %Hs_v".
  assert (i < tsize T_t)%nat as Hi. { rewrite -Hlen_t. eapply lookup_lt_is_Some_1. eauto. }
  iPoseProof (state_rel_pub_if_not_priv _ _ _ _ _ _ (l_t +ₗ i) with "[] Hsrel [Hrel]") as "Hpub".
  { iPureIntro. by apply Hsome_target. }
  { iPoseProof (state_rel_calls_eq with "Hsrel") as "%Hcall_eq".
    iPoseProof (state_rel_stacks_eq with "Hsrel") as "%Hstack_eq".
    iPureIntro. intros t Hpriv.
    specialize (for_each_lookup_case_2 _ _ _ _ _ Hstack_s) as (Hstk & _).
    specialize (Hstk i%nat ltac:(lia)) as (stk & stk' & ? & (_ & Haccess_some)).
    eapply (priv_pub_access_UB _ AccessRead _ _ _ _ stk); [ | | apply Hpriv | eauto..].
    - rewrite -Hstack_eq. done.
    - move : Haccess_some. rewrite Hcall_eq. destruct access1; cbn; intros; simplify_eq. eauto.
  }
  iPoseProof (pub_loc_lookup with "[] Hpub") as "(%sc_t' & %sc_s' & %Hread_both & Hsc_rel)"; first by eauto.
  enough (sc_t = sc_t' ∧ sc_s = sc_s') by naive_solver.
  move : Hread_both (Hv_t i Hi) (Hv_s i Hi) Hs_t Hs_v.
  by move => [-> ->] <- <- [= ->] [= ->].
Qed.

Lemma target_copy_local v_t T l t Ψ :
  length v_t = tsize T →
  t $$ tk_local -∗
  l ↦t∗[local]{t} v_t -∗
  (l ↦t∗[local]{t} v_t -∗ t $$ tk_local -∗ target_red #v_t Ψ)%E -∗
  target_red (Copy (Place l (Tagged t) T)) Ψ.
Proof.
  iIntros (Hlen) "Htag Ht Hsim".
  iApply target_red_lift_head_step. iIntros (?????) "(HP_t & HP_s & Hbor)".
  iModIntro.
  iPoseProof (heap_local_readN_target with "Hbor Ht Htag") as "(%Hd & %Hstack & %Hwf)".
  rewrite Hlen in Hd Hstack.
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[%Hwf_t %]".
  iSplitR.
  { iPureIntro.
    edestruct (copy_head_step P_t σ_t l (Tagged t) T) as (v & α & Hread & Hnewstack & Hhead);
      last (do 3 eexists; eapply Hhead).
    - done.
    - apply read_mem_is_Some'. eauto.
    - intros m stk Hm Hst. rewrite /access1_read_pre.
      rewrite Hstack in Hst; last lia. injection Hst as [= <-].
      exists 0%nat, (mkItem Unique (Tagged t) None).
      split_and!; [done.. |]. intros ? ? ?; lia.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead".
  specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead) as (v_t' & α' & -> & READ & ACC & BOR & -> & ->).
  rewrite READ in Hd. simplify_eq.
  iModIntro. iSplitR; first done.
  iFrame "HP_t HP_s".
  iSplitL "Hbor"; last iApply ("Hsim" with "Ht Htag").

  assert (α' = σ_t.(sst)) as ->.
  {
    apply map_eq. intros l'.
    specialize (for_each_dom _ _ _ _ _ ACC) as Hdom.
    destruct ((sst σ_t) !! l') as [stk | ] eqn:Hst; first last.
    { rewrite Hst. apply not_elem_of_dom in Hst. move : Hst. rewrite Hdom. apply not_elem_of_dom. }
    specialize (proj2 (elem_of_dom σ_t.(sst) l') ltac:(eauto)) as Hel. move: Hel.
    rewrite Hdom. intros (stk' & Hst')%elem_of_dom.
    specialize (for_each_lookup_case _ _ _ _ _ ACC l' stk stk' Hst Hst') as [Heq | [Hacc1 (i & Hi & ->)]].
    { by rewrite Hst Hst' Heq. }
    specialize (Hstack i ltac:(lia)).
    rewrite Hst in Hstack. injection Hstack as [=].
    specialize (tag_unique_head_access σ_t.(scs) stk (Tagged t) None AccessRead ltac:(exists []; eauto)) as (n & Hacc_eq).
    rewrite Hacc_eq in Hacc1. injection Hacc1 as [= <-]. by rewrite Hst Hst'.
  }
  destruct σ_t; done.
Qed.

Lemma source_copy_local v_s T l t Ψ π :
  length v_s = tsize T →
  t $$ tk_local -∗
  l ↦s∗[local]{t} v_s -∗
  (l ↦s∗[local]{t} v_s -∗ t $$ tk_local -∗ source_red #v_s π Ψ)%E -∗
  source_red (Copy (Place l (Tagged t) T)) π Ψ.
Proof.
  iIntros (Hlen) "Htag Hs Hsim".
  iApply source_red_lift_head_step. iIntros (??????) "[(HP_t & HP_s & Hbor) _]".
  iModIntro.
  iPoseProof (bor_interp_get_state_wf with "Hbor") as "[% %Hwf_s]".
  iPoseProof (heap_local_readN_source with "Hbor Hs Htag") as "(%Hd & %Hstack & %Hwf)".
  rewrite Hlen in Hd Hstack.
  assert (head_reducible P_s (Copy (Place l (Tagged t) T)) σ_s) as (e_s' & σ_s' & efs & Hhead).
  { edestruct (copy_head_step P_s σ_s l (Tagged t) T) as (v & α & Hread & Hnewstack & Hhead);
      last (do 3 eexists; eapply Hhead).
    - done.
    - apply read_mem_is_Some'. eauto.
    - intros m stk Hm Hst. rewrite /access1_read_pre.
      rewrite Hstack in Hst; last lia. injection Hst as [= <-].
      exists 0%nat, (mkItem Unique (Tagged t) None).
      split_and!; [done.. |]. intros ? ? ?; lia.
  }
  iExists e_s', σ_s'.
  specialize (head_copy_inv _ _ _ _ _ _ _ _ Hhead) as (v_t' & α' & -> & READ & ACC & BOR & -> & ->).
  rewrite READ in Hd. simplify_eq.
  iFrame "HP_t HP_s". iSplitR; first done.
  iSplitL "Hbor"; last by iApply ("Hsim" with "Hs Htag"). iModIntro.
  assert (α' = σ_s.(sst)) as ->.
  {
    apply map_eq. intros l'.
    specialize (for_each_dom _ _ _ _ _ ACC) as Hdom.
    destruct ((sst σ_s) !! l') as [stk | ] eqn:Hst; first last.
    { rewrite Hst. apply not_elem_of_dom in Hst. move : Hst. rewrite Hdom. apply not_elem_of_dom. }
    specialize (proj2 (elem_of_dom σ_s.(sst) l') ltac:(eauto)) as Hel. move: Hel.
    rewrite Hdom. intros (stk' & Hst')%elem_of_dom.
    specialize (for_each_lookup_case _ _ _ _ _ ACC l' stk stk' Hst Hst') as [Heq | [Hacc1 (i & Hi & ->)]].
    { by rewrite Hst Hst' Heq. }
    specialize (Hstack i ltac:(lia)).
    rewrite Hst in Hstack. injection Hstack as [=].
    specialize (tag_unique_head_access σ_s.(scs) stk (Tagged t) None AccessRead ltac:(exists []; eauto)) as (n & Hacc_eq).
    rewrite Hacc_eq in Hacc1. injection Hacc1 as [= <-]. by rewrite Hst Hst'.
  }
  by destruct σ_s.
Qed.

(* should work for any tag_kind [tk] *)
Lemma target_copy_protected v_t T l t tk Ψ c M  :
  length v_t = tsize T →
  (∀ i: nat, (i < tsize T)%nat → call_set_in M t (l +ₗ i)) →
  c @@ M -∗
  t $$ tk -∗
  l ↦t∗[tk]{t} v_t -∗
  (l ↦t∗[tk]{t} v_t -∗ c @@ M -∗ t $$ tk -∗ target_red #v_t Ψ)%E -∗
  target_red (Copy (Place l (Tagged t) T)) Ψ.
Proof.
Admitted.

(* doesn't need protectors due to source UB *)
Lemma source_copy_any v_s T l t tk Ψ π :
  length v_s = tsize T →
  t $$ tk -∗
  l ↦s∗[tk]{t} v_s -∗
  (l ↦s∗[tk]{t} v_s -∗ t $$ tk -∗ source_red #v_s π Ψ)%E -∗
  source_red (Copy (Place l (Tagged t) T)) π Ψ.
Proof.
Admitted.

(* Write lemmas *)
Lemma sim_write_public Φ π l_t bor_t T_t l_s bor_s T_s v_t' v_s' :
  rrel (PlaceR l_t bor_t T_t) (PlaceR l_s bor_s T_s) -∗
  value_rel v_t' v_s' -∗
  (#[☠] ⪯{π, Ω} #[☠] [{ Φ }]) -∗
  Write (Place l_t bor_t T_t) v_t' ⪯{π, Ω} Write (Place l_s bor_s T_s) v_s' [{ Φ }].
Proof.
Admitted.

(* note: this is a new lemma. we do not care about relating the values - we only care for the source expression requiring that [t] is still on top!
  TODO: can we make that more general/nicer?
*)
Lemma sim_write_unique_unprotected π l_t l_s t T v_t v_s v_t' v_s' Φ :
  t $$ tk_unq -∗
  l_t ↦t∗[unq]{t} v_t -∗
  l_s ↦s∗[unq]{t} v_s -∗
  (t $$ tk_unq -∗ l_t ↦t∗[unq]{t} v_t' -∗ l_s ↦s∗[unq]{t} v_s' -∗ #[☠] ⪯{π, Ω} #[☠] [{ Φ }]) -∗
  Write (Place l_t (Tagged t) T) #v_t' ⪯{π, Ω} Write (Place l_s (Tagged t) T) #v_s' [{ Φ }].
Proof.
Admitted.

Lemma target_write_local v_t v_t' T l t Ψ :
  length v_t = tsize T →
  length v_t' = tsize T →
  t $$ tk_local -∗
  l ↦t∗[tk_local]{t} v_t -∗
  (l ↦t∗[tk_local]{t} v_t' -∗ t $$ tk_local -∗ target_red #[☠] Ψ)%E -∗
  target_red (Write (Place l (Tagged t) T) #v_t') Ψ.
Proof.
Admitted.

Lemma source_write_local v_s v_s' T l t Ψ π :
  length v_s = tsize T →
  length v_s' = tsize T →
  t $$ tk_local -∗
  l ↦s∗[tk_local]{t} v_s -∗
  (l ↦s∗[tk_local]{t} v_s' -∗ t $$ tk_local -∗ source_red #[☠] π Ψ)%E -∗
  source_red (Write (Place l (Tagged t) T) #v_s') π Ψ.
Proof.
Admitted.

Lemma target_write_protected v_t v_t' T l t c M Ψ :
  length v_t = tsize T →
  length v_t' = tsize T →
  (∀ i: nat, (i < tsize T)%nat → call_set_in M t (l +ₗ i)) →
  c @@ M -∗
  t $$ tk_unq -∗
  l ↦t∗[tk_unq]{t} v_t -∗
  (l ↦t∗[tk_unq]{t} v_t' -∗ c @@ M -∗ t $$ tk_unq -∗ target_red #[☠] Ψ)%E -∗
  target_red (Write (Place l (Tagged t) T) #v_t') Ψ.
Proof.
Admitted.

(* doesn't need protectors: if the item isn't there anymore, it will be UB *)
Lemma source_write_unique v_s v_s' T l t Ψ π :
  length v_s = tsize T →
  length v_s' = tsize T →
  t $$ tk_unq -∗
  l ↦s∗[tk_unq]{t} v_s -∗
  (l ↦s∗[tk_unq]{t} v_s' -∗ t $$ tk_unq -∗ source_red #[☠] π Ψ)%E -∗
  source_red (Write (Place l (Tagged t) T) #v_s') π Ψ.
Proof.
Admitted.

Lemma sim_retag_public l_t l_s ot os c kind T rkind π Φ :
  value_rel [ScPtr l_t ot] [ScPtr l_s os] -∗
  (∀ nt, value_rel [ScPtr l_t nt] [ScPtr l_s nt] -∗
    #[ScPtr l_t nt] ⪯{π, Ω} #[ScPtr l_s nt] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] kind T rkind ⪯{π, Ω} Retag #[ScPtr l_s os] #[ScCallId c] kind T rkind [{ Φ }].
Proof.
Admitted.

(* TODO: for Mutable, this is currently not particularly useful, since reads are UB when the tag is not there.
  Instead, need a mechanism for "deferred observations" or such
*)
Lemma sim_retag_default mut T l_t l_s c ot π Φ :
  (0 < tsize T)%nat → (* TODO: check if we need that condition *)
  let pk : pointer_kind := RefPtr mut in
  let pm := match mut with Mutable => Unique | Immutable => SharedReadOnly end in
  (if mut is Immutable then is_freeze T else True) →
  sc_rel (ScPtr l_t ot) (ScPtr l_s ot) -∗
  (∀ nt v_t v_s,
    let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
    ⌜length v_t = tsize T⌝ -∗ ⌜length v_s = tsize T⌝ -∗
    value_rel v_t v_s -∗  (* as the pointers were public before *)
    nt $$ tk -∗
    l_t ↦t∗[tk]{nt} v_t -∗
    l_s ↦s∗[tk]{nt} v_s -∗
    (if mut is Immutable then sc_rel (ScPtr l_t (Tagged nt)) (ScPtr l_s (Tagged nt)) else True) -∗
    #[ScPtr l_t (Tagged nt)] ⪯{π, Ω} #[ScPtr l_s (Tagged nt)] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] pk T Default ⪯{π, Ω} Retag #[ScPtr l_s ot] #[ScCallId c] pk T Default [{ Φ }].
Proof.
Admitted.

Fixpoint seq_loc_set (l : loc) (n : nat) : gset loc :=
  match n with
  | O => ∅
  | S n => {[ l +ₗ n ]} ∪ seq_loc_set l n
  end.

Lemma sim_retag_fnentry mut T l_t l_s c M ot π Φ :
  let pk : pointer_kind := RefPtr mut in
  let pm := match mut with Mutable => Unique | Immutable => SharedReadOnly end in
  (if mut is Immutable then is_freeze T else True) →
  sc_rel (ScPtr l_t ot) (ScPtr l_s ot) -∗
  c @@ M -∗
  (∀ nt v_t v_s,
    let tk := match mut with Mutable => tk_unq | Immutable => tk_pub end in
    let L := seq_loc_set l_t (tsize T) in   (* uses that l_t = l_s *)
    ⌜length v_t = tsize T⌝ -∗ ⌜length v_s = tsize T⌝ -∗
    value_rel v_t v_s -∗  (*as the pointers were public before *)
    c @@ <[nt := L]> M -∗
    nt $$ tk -∗
    l_t ↦t∗[tk]{nt} v_t -∗
    l_s ↦s∗[tk]{nt} v_s -∗
    (if mut is Immutable then sc_rel (ScPtr l_t (Tagged nt)) (ScPtr l_s (Tagged nt)) else True) -∗
    #[ScPtr l_t (Tagged nt)] ⪯{π, Ω} #[ScPtr l_s (Tagged nt)] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] pk T FnEntry ⪯{π, Ω} Retag #[ScPtr l_s ot] #[ScCallId c] pk T FnEntry [{ Φ }].
Proof.
Admitted.

Lemma sim_initcall π Φ :
  (∀ c, c @@ ∅ -∗
    #[ScCallId c] ⪯{π, Ω} #[ScCallId c] [{ Φ }]) -∗
  InitCall ⪯{π, Ω} InitCall [{ Φ }].
Proof.
Admitted.

(* TODO: should we require that M = ∅ here and provide lemmas that allow to empty this?
  That is what the original formalization does, but I don't think we will need it..
*)
Lemma sim_endcall c M π Φ :
  c @@ M -∗
  #[☠] ⪯{π, Ω} #[☠] [{ Φ }] -∗
  EndCall #[ScCallId c] ⪯{π, Ω} EndCall #[ScCallId c] [{ Φ }].
Proof.
Admitted.

Lemma sim_call fn r_t r_s π Φ :
  Ω r_t r_s -∗
  (∀ r_t r_s : result, Ω r_t r_s -∗ Φ (of_result r_t) (of_result r_s)) -∗
  Call #[ScFnPtr fn] r_t ⪯{π, Ω} Call #[ScFnPtr fn] r_s [{ Φ }].
Proof.
  iIntros "Hval Hsim". iApply (sim_lift_call _ _ _ fn r_t r_s with "Hval"). by iApply "Hsim".
Qed.

End lifting.

