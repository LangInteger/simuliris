(** This file provides the basic heap and ghost state support for the BorIngLang program logic. *)
From iris.proofmode Require Export tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_heap gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.
From iris.prelude Require Import options.
From simuliris.stacked_borrows Require Import tkmap_view.
From simuliris.stacked_borrows Require Export class_instances tactics notation lang bor_semantics.

Definition wf_mem_tag (h: mem) (nxtp: ptr_id) :=
  ∀ l l' pid, h !! l = Some (ScPtr l' (Tagged pid)) → (pid < nxtp)%nat.

Definition stack_item_included (stk: stack) (nxtp: ptr_id) (nxtc: call_id) :=
  ∀ si, si ∈ stk → match si.(tg) with
                    | Tagged t => (t < nxtp)%nat
                    | _ => True
                   end ∧
                   match si.(protector) with
                    | Some c => (c < nxtc)%nat
                    | _ => True
                   end.

Definition is_tagged (it: item) :=
  match it.(tg) with Tagged _ => True | _ => False end.
Instance is_tagged_dec it: Decision (is_tagged it).
Proof. intros. rewrite /is_tagged. case tg; solve_decision. Defined.
Definition stack_item_tagged_NoDup (stk : stack) :=
  NoDup (fmap tg (filter is_tagged stk)).

Definition wf_stack (stk: stack) (nxtp: ptr_id) (nxtc: call_id) :=
  stack_item_included stk nxtp nxtc ∧ stack_item_tagged_NoDup stk.
Definition wf_stacks (α: stacks) (nxtp: ptr_id) (nxtc: call_id) :=
  ∀ l stk, α !! l = Some stk → wf_stack stk nxtp nxtc.
Definition wf_non_empty (α: stacks) :=
  ∀ l stk, α !! l = Some stk → stk ≠ [].
Definition wf_no_dup (α: stacks) :=
  ∀ l stk, α !! l = Some stk → NoDup stk.
Definition wf_cid_incl (cids: call_id_set) (nxtc: call_id) :=
  ∀ c : call_id, c ∈ cids → (c < nxtc)%nat.
Definition wf_scalar σ sc := ∀ t l, sc = ScPtr l t → t <t σ.(snp).

Record state_wf (s: state) := {
  state_wf_dom : dom (gset loc) s.(shp) ≡ dom (gset loc) s.(sst);
  state_wf_mem_tag : wf_mem_tag s.(shp) s.(snp);
  state_wf_stack_item : wf_stacks s.(sst) s.(snp) s.(snc);
  state_wf_non_empty : wf_non_empty s.(sst);
  (*state_wf_cid_no_dup : NoDup s.(scs) ;*)
  state_wf_cid_agree: wf_cid_incl s.(scs) s.(snc);
  (* state_wf_cid_non_empty : s.(scs) ≠ []; *)
  (* state_wf_no_dup : wf_no_dup σ.(cst).(sst); *)
}.

Fixpoint active_SRO (stk: stack) : gset ptr_id :=
  match stk with
  | [] => ∅
  | it :: stk =>
    match it.(perm) with
    | SharedReadOnly => match it.(tg) with
                        | Tagged t => {[t]} ∪ active_SRO stk
                        | Untagged => active_SRO stk
                        end
    | _ => ∅
    end
  end.


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
  call_source_name : gname;
  call_target_name : gname;

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

    Global Instance state_rel_persistent σ_t σ_s :
      (∀ sc_t sc_s, Persistent (sc_rel sc_t sc_s)) → Persistent (state_rel σ_t σ_s).
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
    Search "lookup" "insert".
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
    is_Some (σ_t.(shp) !! l) →
    priv_loc M_tag M_t Mcall t l →
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
    is_Some (σ_t.(shp) !! l) →
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    ⌜∀ t, ¬ priv_loc M_tag M_t Mcall t l⌝ -∗
    pub_loc sc_rel σ_t σ_s l.
  Proof.
    iIntros (Hs) "(%& % & % & % & % & Hrel) %Hnpriv".
    iPoseProof ("Hrel" $! l with "[//]") as "[Hpub | %Hpriv]"; first done.
    destruct Hpriv as (t & Hpriv). exfalso; by eapply Hnpriv.
  Qed.

  Lemma state_rel_heap_lookup_some M_tag M_t Mcall σ_t σ_s l :
    state_rel M_tag M_t Mcall σ_t σ_s -∗
    ⌜is_Some (σ_t.(shp) !! l) ↔ is_Some (σ_s.(shp) !! l)⌝.
  Proof.
    iIntros "(%Hshp & _)". iPureIntro. by rewrite -!elem_of_dom Hshp.
  Qed.

  Lemma pub_loc_lookup σ_t σ_s l :
    is_Some (σ_t.(shp) !! l) →
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
End call_defs.

Notation "c '@s@' M" := (call_set_is call_source_name c M) (at level 50).
Notation "c '@t@' M" := (call_set_is call_target_name c M) (at level 50).


(* Interpretation for heap assertions under control of tags
    The interpretation of the tag map and the "heap view" fragments are interlinked.
 *)
Section heap_defs.
  (** The assumption on the location still being valid for tag [t], i.e., [t] not being disabled. *)
  Definition bor_state_pre (l : loc) (t : ptr_id) (tk : tag_kind) (s : stack) :=
    tk = tk_local ∨ ∃ pm pro, mkItem pm (Tagged t) pro ∈ s ∧ pm ≠ Disabled.

  Definition bor_state_own (l : loc) (t : ptr_id) (tk : tag_kind) (s : stack) :=
    (tk = tk_unq ∧ ∃ s' op, s = (mkItem Unique (Tagged t) op) :: s') ∨
    (tk = tk_pub ∧ t ∈ active_SRO s) ∨
    (tk = tk_local ∧ s = [mkItem Unique (Tagged t) None]).

  Definition loc_controlled (l : loc) (t : ptr_id) (tk : tag_kind) (sc : scalar) (σ : state) :=
    ∃ s, σ.(sst) !! l = Some s ∧
      (bor_state_pre l t tk s → bor_state_own l t tk s ∧ σ.(shp) !! l = Some sc).

  Lemma loc_controlled_local l t sc σ :
    loc_controlled l t tk_local sc σ →
    σ.(sst) !! l = Some [mkItem Unique (Tagged t) None] ∧
    σ.(shp) !! l = Some sc.
  Proof.
    intros (s & Hs & Him). specialize (Him ltac:(by left)) as (Hbor & Hmem).
    split; last done. destruct Hbor as [ [[=] ] | [[[=] ] |[_ H] ] ].
    by rewrite Hs H.
  Qed.
  Lemma loc_controlled_unq l t sc σ :
    loc_controlled l t tk_unq sc σ →
    (∀ s, σ.(sst) !! l = Some s → ∃ pm pro, mkItem pm (Tagged t) pro ∈ s ∧ pm ≠ Disabled) →
    (∃ s' op, σ.(sst) !! l = Some $ (mkItem Unique (Tagged t) op) :: s') ∧
    σ.(shp) !! l = Some sc.
  Proof.
    intros (s & Hs & Him) Hpm.
    specialize (Hpm _ Hs). specialize (Him ltac:(by right)) as (Hbor & Hmem). split; last done.
    destruct Hbor as [[_ H]  | [[[=] ] |[[=] ] ] ].
    rewrite Hs. destruct H as (s' & op & ->). eauto.
  Qed.
  Lemma loc_controlled_pub l t sc σ :
    loc_controlled l t tk_pub sc σ →
    (∀ s, σ.(sst) !! l = Some s → ∃ pm pro, mkItem pm (Tagged t) pro ∈ s ∧ pm ≠ Disabled) →
    (∃ s, σ.(sst) !! l = Some s ∧ t ∈ active_SRO s) ∧
    σ.(shp) !! l = Some sc.
  Proof.
    intros (s & Hs & Him) Hpm.
    specialize (Hpm _ Hs). specialize (Him ltac:(by right)) as (Hbor & Hmem). split; last done.
    destruct Hbor as [[[=] ]  | [[_ H] |[[=] ] ] ].
    rewrite Hs. eauto.
  Qed.

  Lemma loc_controlled_mem_insert_ne l l' t tk sc sc' σ :
    l ≠ l' →
    loc_controlled l t tk sc σ →
    loc_controlled l t tk sc (state_upd_mem <[l' := sc']> σ).
  Proof.
    intros Hneq (s & Hsome & Him). exists s; split; first done.
    intros [Hownw Hmem]%Him. split; first done.
    rewrite lookup_insert_ne; done.
  Qed.
  Lemma loc_controlled_mem_insert l t tk sc sc' σ :
    loc_controlled l t tk sc σ →
    loc_controlled l t tk sc' (state_upd_mem <[l := sc']> σ).
  Proof.
    intros (s & Hsome & Him). exists s; split; first done.
    intros [Hownw Hmem]%Him. split; first done.
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
    intros (s & Hsome & Hcontrol) (s' & Hsome' & Hcontrol').
    rewrite Hsome in Hsome'. injection Hsome' as [= <-].
    specialize (Hcontrol ltac:(by left)) as [[[[=]] | [[[=] ] | [_  ->]]] Hmem].
    specialize (Hcontrol' ltac:(by left)) as [[[[=]] | [[[=] ] | [_  Heq]]] Hmem'].
    injection Heq. rewrite Hmem in Hmem'. injection Hmem'. done.
  Qed.
  Lemma loc_controlled_local_pre l t t' tk' st sc σ :
    σ.(sst) !! l = Some st →
    loc_controlled l t tk_local sc σ →
    bor_state_pre l t' tk' st →
    tk' = tk_local ∨ t' = t.
  Proof.
    intros Hst [Heq _]%loc_controlled_local [-> | Hprot]; first by left.
    destruct Hprot as (pm & pro & Hel & _).
    rewrite Heq in Hst. injection Hst as [= <-].
    apply elem_of_list_singleton in Hel.
    injection Hel. eauto.
  Qed.
  Lemma loc_controlled_local_own l t t' tk' st sc σ :
    σ.(sst) !! l = Some st →
    loc_controlled l t tk_local sc σ →
    bor_state_own l t' tk' st →
    (tk' = tk_unq ∨ tk' = tk_local) ∧ t = t'.
  Proof.
    intros Hst [Heq _]%loc_controlled_local [[-> (s' & ? & ->)] | [[-> Hpub] | [-> ->]]].
    - rewrite Heq in Hst. injection Hst. eauto.
    - exfalso. rewrite Heq in Hst. injection Hst as [= <-]. done.
    - rewrite Heq in Hst. injection Hst. eauto.
  Qed.

  (* having local ownership of a location is authoritative, in the sense that we can update memory without hurting other tags that control this location. *)
  Lemma loc_controlled_local_authoritative l t t' tk' sc sc' σ f :
    loc_controlled l t tk_local sc (state_upd_mem f σ) →
    loc_controlled l t' tk' sc' σ →
    t ≠ t' →
    loc_controlled l t' tk' sc' (state_upd_mem f σ).
  Proof.
    intros Hcontrol (s' & Hsome' & Hcontrol') Hneq.
    exists s'; split; first done.
    intros [Hown Hshp]%Hcontrol'.
    by edestruct (loc_controlled_local_own l t t' tk' s' sc (state_upd_mem f σ)) as [_ <-].
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


  Definition tag_interp (M : gmap ptr_id (tag_kind * unit)) (M_t M_s : gmap (ptr_id * loc) scalar) σ_t σ_s : Prop :=
    ∀ (t : ptr_id) tk, M !! t = Some (tk, ()) →
      (* tags are valid *)
      (t < σ_t.(snp))%nat ∧ (t < σ_s.(snp))%nat ∧
      (* at all locations, the values agree, and match the physical state assuming the tag currently has control over the location *)
      (∀ l sc_t, M_t !! (t, l) = Some sc_t → loc_controlled l t tk sc_t σ_t) ∧
      (∀ l sc_s, M_s !! (t, l) = Some sc_s → loc_controlled l t tk sc_s σ_s) ∧
      dom_agree_on_tag M_t M_s t.
End heap_defs.


Notation "p '@@' tk" := (tkmap_elem tag_name p tk ()) (at level 50).

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
    ghost_map_auth call_source_name 1 M_call ∗
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

End state_interp.


(** Array generalizes pointsto connectives to lists of scalars *)
Definition array_tag `{!bor_stateG Σ} γh (t : ptr_id) (l : loc) (dq : dfrac) (scs : list scalar) : iProp Σ :=
  ([∗ list] i ↦ sc ∈ scs, ghost_map_elem γh (t, l +ₗ i) dq sc)%I.

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
      t @@ tk_local ∗
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
        eapply state_wf_mem_tag0; done.
    Qed.

  Lemma heap_local_access_target σ_t σ_s (t : ptr_id) l  sc :
    bor_interp σ_t σ_s -∗
    l ↦t[local]{t} sc -∗
    t @@ tk_local -∗
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
    t @@ tk_local -∗
    ⌜∀ i : nat, i < length scs → σ_t.(shp) !! (l +ₗ i) = scs !! i ⌝ ∗
    ⌜∀ i, i < length scs → σ_t.(sst) !! (l +ₗ i) = Some [mkItem Unique (Tagged t) None]⌝ ∗
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
    t @@ tk_local -∗
    ⌜read_mem l (length scs) σ_t.(shp) = Some scs⌝ ∗
    ⌜∀ i, i < length scs → σ_t.(sst) !! (l +ₗ i) = Some [mkItem Unique (Tagged t) None]⌝ ∗
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

  Lemma heap_local_access_source σ_t σ_s (t : ptr_id) l sc :
    bor_interp σ_t σ_s -∗
    l ↦s[local]{t} sc -∗
    t @@ tk_local -∗
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
    t @@ tk_local -∗
    ⌜read_mem l (length scs) σ_s.(shp) = Some scs⌝ ∗
    ⌜∀ i, i < length scs → σ_s.(sst) !! (l +ₗ i) = Some [mkItem Unique (Tagged t) None]⌝ ∗
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

End lemmas.










(* NOTE: might need to generalize that with the bijection a bit when we want to do cool things, e.g., pass parts of an object to a function (but for just obtaining a reflexivity thm, it should be fine) *)
Section val_rel.
  Context {Σ} `{bor_stateG Σ}.
  Fixpoint sc_rel (sc1 sc2 : scalar) {struct sc2} : iProp Σ :=
    match sc1, sc2 with
    | ScInt z1, ScInt z2 => ⌜z1 = z2⌝
    | ScFnPtr f1, ScFnPtr f2 => ⌜f1  = f2⌝
    | ScPtr l1 t1, ScPtr l2 t2 =>
        (* through srel: the stacks are the same, the allocation size is the same, and the locations are related (i.e.: if tagged, then it is public) *)
        ⌜l1 = l2⌝ ∗
        (⌜t1 = Untagged⌝ ∗ ⌜t2 = Untagged⌝) ∨
        (∃ p1 p2, ⌜t1 = Tagged p1⌝ ∗ ⌜t2 = Tagged p2⌝ ∗
        (* may want to generalize that properly when we have a proper bijection on tags*)
        ⌜p1 = p2⌝ ∗
        p1 @@ tk_pub
        (* note: we do not have any assertion about the value as viewed by the tag here -- we don't really care about it, we need to do a retag anyways. what the tk_pub gives us is that the locations store related values *)
      )
    | _, _ => False
    end.

  Global Instance sc_rel_persistent sc_t sc_s : Persistent (sc_rel sc_t sc_s).
  Proof. destruct sc_t, sc_s; apply _. Qed.

  Lemma sc_rel_public_ptr_inv σ_t σ_s t1 t2 l1 l2 :
    bor_interp sc_rel σ_t σ_s -∗
    sc_rel (ScPtr l1 (Tagged t1)) (ScPtr l2 (Tagged t2)) -∗
    ⌜l1 = l2 ∧ t1 = t2⌝ ∗
    ∀ sc_s, ⌜σ_s.(shp) !! l1 = Some sc_s⌝ → ∃ sc_t, ⌜σ_t.(shp) !! l2 = Some sc_t⌝ ∗ sc_rel sc_t sc_s.
  Proof.
  Admitted.



  (*Definition value_rel (v1 v2 : value) := Forall2*)
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

Lemma sim_alloc T Φ π :
  (∀ t l_t l_s, t @@ tk_local -∗
    l_t ↦t∗[local]{t} repeat ScPoison (tsize T) -∗
    l_s ↦s∗[local]{t} repeat ScPoison (tsize T) -∗
    Place l_t (Tagged t) T ⪯{π, Ω} Place l_s (Tagged t) T {{ Φ }}) -∗
  Alloc T ⪯{π, Ω} Alloc T {{ Φ }}.
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

(*Lemma sim_make_public T Φ π : *)
  (*t @@ tk_local -∗ *)
  (*l_t ↦t∗[local]{t} repeat ScPoison (tsize T) -∗*)
  (*l_s ↦s∗[local]{t} repeat ScPoison (tsize T) -∗*)


Lemma target_local_copy scs T l t Ψ :
  length scs = tsize T →
  t @@ tk_local -∗
  l ↦t∗[local]{t} scs -∗
  (l ↦t∗[local]{t} scs -∗ target_red #scs Ψ)%E -∗
  target_red (Copy (Place l (Tagged t) T)) Ψ.
Proof.
  iIntros (Hlen) "Htag Ht Hsim".
  iApply target_red_lift_head_step. iIntros (?????) "(HP_t & HP_s & Hbor)".
  iModIntro.
  iPoseProof (heap_local_accessN_target with "Hbor Ht Htag") as "(%Hd & %Hstack & %Hwf & Hclose)".
  iSplitR.
  { iPureIntro. do 3 eexists. econstructor 2.
    - econstructor. rewrite -Hlen. apply Hd.
    - econstructor.
      + instantiate (1 := σ_t.(sst)).
        (*induction T.*)
        (** cbn. induction sz; cbn; first done.*)
        admit.
      + done.
  }
  iIntros (e_t' efs_t σ_t') "%Hhead". inv_head_step.
  rewrite Hlen READ in Hd. injection Hd as ->.
  iMod ("Hclose" $! scs with "[//] [//]") as "[Hbor Ht]".
  iModIntro. iSplitR; first done.
  iFrame.
  iSplitL "Hbor"; last by iApply "Hsim".
  (* TODO: have write-id lemma *)
  admit.
Admitted.

Lemma source_local_copy scs T l t Ψ π :
  length scs = tsize T →
  t @@ tk_local -∗
  l ↦s∗[local]{t} scs -∗
  (l ↦s∗[local]{t} scs -∗ source_red #scs π Ψ)%E -∗
  source_red (Copy (Place l (Tagged t) T)) π Ψ.
Proof.
  iIntros (Hlen) "Htag Hs Hsim".
  iApply source_red_lift_head_step. iIntros (??????) "[(HP_t & HP_s & Hbor) _]".
  iModIntro.
  iPoseProof (heap_local_accessN_source with "Hbor Hs Htag") as "(%Hd & %Hstack & %Hwf & Hclose)".
  assert (head_reducible P_t (Copy (Place l (Tagged t) T)) σ_s) as (e_s' & σ_s' & efs & Hstep).
  { do 3 eexists. econstructor 2.
    - econstructor. rewrite -Hlen. apply Hd.
    - econstructor.
      + instantiate (1 := σ_t.(sst)).
        (*induction T.*)
        (** cbn. induction sz; cbn; first done.*)
        admit.
      + done.
  }
  iExists e_s', σ_s'. inv_head_step.
  iSplitR; first by eauto using head_step, bor_step, mem_expr_step.
  rewrite Hlen READ in Hd. injection Hd as ->.
  iMod ("Hclose" $! scs with "[//] [//]") as "[Hbor Ht]".
  iModIntro. iFrame.
  iSplitL "Hbor"; last by iApply "Hsim".
  (* TODO: have write-id lemma *)
  admit.
Admitted.

(*Lemma sim_retag_default_mutref l_t l_s ot Φ c pkind T π : *)
  (*(∀ nt, nt @@ tk_local -∗ #[ScPtr l_t nt] ⪯{π, Ω} #[ScPtr l_s nt] [{ Φ }]) -∗*)
  (*Retag #[ScPtr l_t ot] #[ScCallId c] (RefPtr Mutable) T Default ⪯{π, Ω} Retag #[ScPtr l_s ot] #[ScCallId c] (RefPtr Mutable) T Default [{ Φ }].*)
(*Proof. *)

(*Abort.*)








