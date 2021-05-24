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

  (* A bijection on blocks, stating that the size of the allocation and the stacks are pointwise the same, and the target locations are in public or private relation *)
  heap_bij_inG :> gset_bijG Σ block block;
  heap_bij_name : gname;

  (* Size of blocks *)
  freeable_inG :> ghost_mapG Σ loc (option nat);
  freeable_source_name : gname;
  freeable_target_name : gname;

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

(* NOTE: doing this in simplang style doesn't work. 
  the language doesn't offer any guarantees that locations that were used once will not be re-used.
 *)
Section freeable.
  Context {Σ} (freeable_name : gname) {freeable_inG : ghost_mapG Σ loc (option nat)}.
  (*[σ] is the heap map. [bs] is the set of all blocks ever allocated. [hF] is the freeable map, mapping to the allocation size. *)
  Definition heap_freeable_rel (σ : gmap loc scalar) (bs : gset block) (hF : gmap loc (option nat)) : Prop :=
    ∀ l (o : option nat), hF !! l = Some o →
     l.1 ∈ bs ∧
     l.2 = 0 ∧
     0 < default 1%nat o ∧
     ∀ i, is_Some (σ !! (l +ₗ i)) ↔ (0 ≤ i < default O o)%Z.

  Definition heap_freeable_def (l : loc) (q : Qp) (n: option nat) : iProp Σ :=
    ⌜l.2 = 0⌝ ∗ l ↪[ freeable_name ]{# q } n.
  Definition heap_freeable_aux : seal (@heap_freeable_def). by eexists. Qed.
  Definition heap_freeable := unseal heap_freeable_aux.
  Definition heap_freeable_eq : @heap_freeable = @heap_freeable_def :=
    seal_eq heap_freeable_aux.

  Definition heap_freeable_auth σ bs : iProp Σ := ∃ hF,
    ghost_map_auth freeable_name 1 hF ∗ ⌜heap_freeable_rel σ bs hF⌝.

  Local Notation "†{ q } l …? n" := (heap_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l …? n") : bi_scope.
  Local Notation "† l …? n" := (heap_freeable  l 1 n) (at level 20) : bi_scope.

  Lemma heap_freeable_idx l n :
    †l…?n -∗ ⌜l.2 = 0⌝.
  Proof. rewrite heap_freeable_eq. iIntros "[$ _]". Qed.

  Lemma heap_freeable_excl l l' n n' :
    l.1 = l'.1 →
    †l…?n -∗ †l'…?n' -∗ False.
  Proof.
    rewrite heap_freeable_eq.
    iIntros (?) "[% Hl1] [% Hl2]". destruct l, l'; simplify_eq/=.
    by iDestruct (ghost_map_elem_valid_2 with "Hl1 Hl2") as %[? ?].
  Qed.

  Lemma heap_freeable_rel_stable σ bs h l p :
    heap_freeable_rel σ bs h → is_Some (σ !! l) →
    heap_freeable_rel (<[l := p]>σ) bs h.
  Proof.
    intros REL Hσ blk qs Hqs. destruct (REL blk qs) as [? [? [? REL']]]; first done.
    split_and!; [done..|]=> i. rewrite -REL' lookup_insert_is_Some.
    destruct (decide (l = blk +ₗ i)); naive_solver.
  Qed.

  Instance option_proper A : Proper ((=) ==> iff) (is_Some (A:=A)). 
  Proof. intros a b ->; done. Qed.

  Lemma heap_freeable_rel_init_mem l h n σ bs sc:
    n ≠ O →
    l.2 = 0 →
    l.1 ∉ bs →
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    heap_freeable_rel σ bs h →
    heap_freeable_rel (heap_array l (replicate n sc) ∪ σ) ({[l.1]} ∪ bs)
                      (<[l := Some n]> h).
  Proof.
    move => ?? Hnotin Hnone Hrel l' o /lookup_insert_Some[[??]|[? Hl]]; simplify_eq/=.
    - split_and!; [set_solver|done|lia|] => i.
      split.
      + move => [?].
        rewrite lookup_union_Some ?Hnone.
        2: { apply heap_array_map_disjoint. naive_solver lia. }
        rewrite heap_array_lookup => -[[?[?[?]]]|//]. simplify_eq.
        rewrite lookup_replicate. lia.
      + move => ?.
        eexists _.
        rewrite lookup_union_Some ?Hnone.
        2: { apply heap_array_map_disjoint. naive_solver lia. }
        left. apply heap_array_lookup. eexists i.
        split_and!; [lia|done |].
        rewrite lookup_replicate. naive_solver lia.
    - have [?[?[? Hi]]]:= Hrel _ _ Hl.
      split_and!; [set_solver|done|lia|] => i.
      have <-:= Hi i. f_equiv.
      apply option_eq => ?.
      rewrite lookup_union_Some.
      2: { apply heap_array_map_disjoint. naive_solver lia. }
      rewrite heap_array_lookup.
      split; [|naive_solver].
      move => [[?[?[?]]]|//].
      contradict Hnotin.
      have ->: l.1 = l'.1 by destruct l, l'; naive_solver.
      done.
  Qed.

  Lemma heap_freeable_rel_free_mem σ hF n l bs:
    l.2 = 0 →
    hF !! l = Some (Some n) →
    heap_freeable_rel σ bs hF →
    heap_freeable_rel (free_mem l n σ) bs (<[l:=None]> hF).
  Proof.
    intros ? Hl REL b qs Hlookup.
    destruct (REL l (Some n)) as [? [? [? REL']]]; auto.
    move: Hlookup => /lookup_insert_Some [[??]|[NEQ ?]]; simplify_eq.
    - split_and!; [done| done| simpl; lia |] => i /=. split; [|lia] => -[?].
      have ->: free_mem b n σ !! (b +ₗ i) = None; last naive_solver.
      destruct (decide (0 ≤ i < n))%Z.
      + apply lookup_free_mem_2; [done|]. simpl. lia.
      + destruct (decide (i < 0))%Z.
        * rewrite lookup_free_mem_3 => /=; [|done|lia].
          apply eq_None_not_Some. naive_solver lia.
        * rewrite lookup_free_mem_4 => /=; [|done|lia].
          apply eq_None_not_Some. naive_solver lia.
    - destruct (REL b qs) as [? [? [? REL'']]]; auto.
      split_and!; [done..|]=> i. rewrite -REL'' lookup_free_mem_1 //=.
      destruct b, l; simplify_eq/=. congruence.
  Qed.

  (*Lemma heap_freeable_inj n1 l1 l2 n2 σ bs:*)
    (*(0 < n1)%Z →*)
    (*(∀ m, is_Some (σ !! (l1 +ₗ m)) ↔ (0 ≤ m < n1)%Z) →*)
    (*loc_chunk l1 = loc_chunk l2 →*)
    (*heap_ctx γ σ bs -∗ †l2…?n2 -∗ ⌜n2 = Some (Z.to_nat n1) ∧ l1 = l2⌝.*)
  (*Proof.*)
    (*iIntros (? Hrel1 ?) "(%hF & ? & HhF & %Hrel) Hf".*)
    (*rewrite heap_freeable_eq. iDestruct "Hf" as (?) "Hf".*)
    (*iDestruct (ghost_map_lookup with "HhF Hf") as %Hf.*)
    (*iPureIntro.*)
    (*have [? [? [? {}Hrel2]]]:= Hrel _ _ Hf.*)
    (*destruct n2; last first. {*)
      (*have [_ [|? Hl]]:= Hrel1 0; [lia|].*)
      (*have [/=[|] ]:= Hrel2 (loc_idx l1 - loc_idx l2)%Z; last lia.*)
      (*eexists _. erewrite <-Hl. f_equal. rewrite /loc_add. destruct l1, l2 => /=.*)
      (*f_equal; [done |lia].*)
    (*}*)
    (*simplify_eq/=.*)
    (*destruct (decide (l1 = l2)).*)
    (*{ subst. split; [|done].*)
      (*have Heq: (∀ i : Z, (0 ≤ i < n) ↔ (0 ≤ i < n1))%Z. naive_solver.*)
      (*f_equal.*)
      (*destruct (decide (n1 < n)%Z). { have := Heq n1. lia. }*)
      (*destruct (decide (n < n1)%Z). { have := Heq n. lia. }*)
      (*lia.*)
    (*}*)
    (*have ?: loc_idx l1 ≠ loc_idx l2 by destruct l1, l2;  naive_solver.*)
    (*destruct (decide (loc_idx l1 < loc_idx l2)%Z).*)
    (*- have [_ [|? Hl]]:= Hrel1 0; first lia.*)
      (*have [/=[|] ]:= Hrel2 (loc_idx l1 - loc_idx l2)%Z; last lia.*)
      (*eexists _. erewrite <-Hl. f_equal. rewrite /loc_add. destruct l1, l2 => /=.*)
      (*f_equal; [done |lia].*)
    (*- have [_ [|? Hl]]:= Hrel2 0; first lia.*)
      (*have [/=[|] ]:= Hrel1 (loc_idx l2 - loc_idx l1)%Z; last lia.*)
      (*eexists _. erewrite <-Hl. f_equal. rewrite /loc_add. destruct l1, l2 => /=.*)
      (*f_equal; [done |lia].*)
  (*Qed.*)

  (*Lemma heap_freeable_lookup σ l l' x n bs:*)
    (*σ !! l' = Some x → loc_chunk l' = loc_chunk l →*)
    (*heap_ctx γ σ bs -∗ †l…?n -∗ ⌜∃ n' : nat, n' < default 0 n ∧ l' = l +ₗ n'⌝.*)
  (*Proof.*)
    (*iIntros (Hlo ?) "(%hF&?&HhF&%Hrel) Hf".*)
    (*rewrite heap_freeable_eq. iDestruct "Hf" as (?) "Hf".*)
    (*iDestruct (ghost_map_lookup with "HhF Hf") as %Hf.*)
    (*iPureIntro.*)
    (*have [? {}Hrel]:= Hrel _ _ Hf.*)
    (*have Hl': l' = (l +ₗ (loc_idx l' - loc_idx l)).*)
    (*{ destruct l', l => /=. rewrite /loc_add/=. f_equal; [done|lia]. }*)
    (*rewrite Hl' in Hlo.*)
    (*eapply mk_is_Some, Hrel in Hlo.*)
    (*eexists (Z.to_nat (loc_idx l' - loc_idx l)). split; [lia|].*)
    (*rewrite Hl'. f_equal => /=. lia.*)
  (*Qed.*)
End freeable.

(** Allocation size notation *)
Notation "† l '…?t' n" := (heap_freeable freeable_target_name l 1 n)
  (at level 20, format "† l …?t  n") : bi_scope.
Notation "† l '…t' n" := (heap_freeable freeable_target_name l 1 (Some n))
  (at level 20, format "† l …t  n") : bi_scope.
Notation "† l '…t' -" := (heap_freeable freeable_target_name l 1 None)
  (at level 20, format "† l …t  -") : bi_scope.
Notation "† l '…?s' n" := (heap_freeable freeable_source_name l 1 n)
  (at level 20, format "† l …?s  n") : bi_scope.
Notation "† l '…s' n" := (heap_freeable freeable_source_name l 1 (Some n))
  (at level 20, format "† l …s  n") : bi_scope.
Notation "† l '…s' -" := (heap_freeable freeable_source_name l 1 None)
  (at level 20, format "† l …s  -") : bi_scope.


Section mem_bijection.
  Context {Σ} `{bor_stateG Σ}.

  Definition heap_bij_auth (L : gset (block * block)) : iProp Σ :=
    gset_bij_own_auth heap_bij_name (DfracOwn 1) L.
  Definition heap_bij_elem (b_t : block) (b_s : block) :=
    gset_bij_own_elem heap_bij_name b_t b_s.
  Definition heap_bij_elem_loc (l_t l_s : loc) : iProp Σ :=
    heap_bij_elem l_t.1 l_s.1 ∗ ⌜l_t.2 = l_s.2⌝.

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

    Definition pub_loc σ_t σ_s (l_t l_s : loc) : iProp Σ := 
      ∀ sc_t, ⌜σ_t.(shp) !! l_t = Some sc_t⌝ → ∃ sc_s, ⌜σ_s.(shp) !! l_s = Some sc_s⌝ ∗ sc_rel sc_t sc_s.
    Definition priv_loc t (l_t : loc) : Prop := 
      ∃ tk, M_tag !! t = Some (tk, tt) ∧ is_Some (M_t !! (t, l_t)) ∧
        (* local *)
        (tk = tk_local ∨ 
        (* unique with protector *)
        (tk = tk_unq ∧ ∃ c M' L, Mcall_t !! c = Some M' ∧ M' !! t = Some L ∧ l_t ∈ L)).
      
    Definition alloc_block_rel (σ_t σ_s : state) (b_t b_s : block) : iProp Σ :=  
      ∃ n : option nat, 
        (* same size *)
        † (b_t, 0) …?t n ∗ † (b_s, 0) …?s n ∗
        (* same stacks *)
        ⌜∀ i st, σ_t.(sst) !! (b_t, i) = Some st → σ_s.(sst) !! (b_s, i) = Some st⌝ ∗
        (* private / public locations of the target *)
        ∀ i, ⌜is_Some (σ_t.(shp) !! (b_t, i))⌝ → 
          pub_loc σ_t σ_s (b_t, i) (b_s, i) ∨ ⌜∃ t, priv_loc t (b_t, i)⌝.

    Definition heap_bij_interp (L : gset (block * block)) σ_t σ_s : iProp Σ :=
      [∗ set] p ∈ L, let '(b_t, b_s) := p in alloc_block_rel σ_t σ_s b_t b_s.
  End defs.
End mem_bijection.

Notation "b_t '⇔h' b_s" := (heap_bij_elem b_t b_s) (at level 50) : bi_scope. 
Notation "l_t '↔h' l_s" := (heap_bij_elem_loc l_t l_s) (at level 50) : bi_scope.

Section bijection_lemmas.
  Context {Σ} `{bor_stateG Σ}.
  Context (sc_rel : scalar → scalar → iProp Σ).

  (*Lemma heap_bij_interp_alloc L t : *)
    (*(∀ b_s, (b_t, b_s) ∉ L) →*)
    (*heap_bij_interp sc_rel M_tag M_t Mcall_t L σ_t σ_s -∗*)
    (*heap_bij_interp sc_rel M_tag (Minit_mem ) Mcall_t L (state_upd_mem (init_mem (b_t, 0) n) σ_t)*)


  (* TODO: accessors *)
  Lemma heap_bij_interp_update_private_target M_tag M_t Mcall_t L σ_t σ_s l_t t sc : 
    is_Some (σ_t.(shp) !! l_t) →
    priv_loc M_tag M_t Mcall_t t l_t →
    heap_bij_interp sc_rel M_tag M_t Mcall_t L σ_t σ_s -∗
    heap_bij_interp sc_rel M_tag (<[(t, l_t) := sc]> M_t) Mcall_t L (state_upd_mem (<[l_t := sc]>) σ_t) σ_s.
  Proof.
    (* 
      1. CA: is the block in the bijection or not. If not, we are done.
      2. Otherwise, the interesting part are the public/private locations.
      3. We prove that it is a private location for t. 
    *)
  Admitted.

  Lemma heap_bij_interp_update_private_source M_tag M_t Mcall_t L σ_t σ_s l_t l_s t sc : 
    is_Some (σ_t.(shp) !! l_t) →
    priv_loc M_tag M_t Mcall_t t l_t →
    (l_t.1, l_s.1) ∈ L →
    l_t.2 = l_s.2 → 
    heap_bij_interp sc_rel M_tag M_t Mcall_t L σ_t σ_s -∗
    heap_bij_interp sc_rel M_tag M_t Mcall_t L σ_t (state_upd_mem (<[l_s := sc]>) σ_s).
  Proof.
    (* 
      1. the interesting part are the public/private locations.
      2. We prove that the target location is private. 
          For any other location, this is fine, because l_t is in bijection with l_s, 
            so other locations cannot be tripped by that.
    *)
  Admitted.
End bijection_lemmas.

(* Interpretation for call ids *)
Section call_defs.
  Context {Σ} (call_gname : gname) {call_inG : ghost_mapG Σ (call_id) (gmap ptr_id (gset loc))}.

  Implicit Types (c : call_id) (pid : ptr_id) (pm : permission).

  Definition call_set_is (c : call_id) (M : gmap ptr_id (gset loc)) :=
    ghost_map_elem call_gname c (DfracOwn 1) M.

  (* This does not assert ownership of the authoritative part. Instead, this is owned by bor_interp below, 
    since also the block bijection needs access to it. *)
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

  (* TODO: we should really try to pose weaker requirements here.
    maybe something like: there is a granting item for t among the items accessible from the top? *)
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

  Definition tag_interp (M : gmap ptr_id (tag_kind * unit)) (M_t M_s : gmap (ptr_id * loc) scalar) σ_t σ_s : Prop := 
    ∀ (t : ptr_id) tk, M !! t = Some (tk, ()) → 
      (* tags are valid *)
      (t < σ_t.(snp))%nat ∧ (t < σ_s.(snp))%nat ∧
      (∃ lb_t lb_s (len : nat),
        (* at all offsets, the values agree, and match the physical state assuming the tag currently has control over the location *)
        (∀ o, o < len → ∃ sc_t sc_s,
          M_t !! (t, lb_t +ₗ o) = Some sc_t ∧ loc_controlled (lb_t +ₗ o) t tk sc_t σ_t ∧
          M_s !! (t, lb_s +ₗ o) = Some sc_s ∧ loc_controlled (lb_s +ₗ o) t tk sc_s σ_s) ∧ 
        (* locations in the heap view are valid *)
        (∀ l sc, M_t !! (t, l) = Some sc → ∃ o : nat, l = lb_t +ₗ o ∧ o < len) ∧
        (∀ l sc, M_s !! (t, l) = Some sc → ∃ o : nat, l = lb_s +ₗ o ∧ o < len)
      ).
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
  Definition bor_auth (M_call_s M_call_t : gmap call_id (gmap ptr_id (gset loc))) (M_tag : gmap ptr_id (tag_kind * unit)) (M_t M_s : gmap (ptr_id * loc) scalar) (L : gset (block * block)) : iProp Σ := 
    ghost_map_auth call_source_name 1 M_call_s ∗
    ghost_map_auth call_target_name 1 M_call_t ∗
    tkmap_auth tag_name 1 M_tag ∗
    ghost_map_auth heap_view_target_name 1 M_t ∗
    ghost_map_auth heap_view_source_name 1 M_s ∗
    gset_bij_own_auth heap_bij_name (DfracOwn 1) L.
  Definition bor_interp (σ_t : state) (σ_s : state) : iProp Σ :=
  (* since multiple parts of the interpretation need access to these maps, we own the authoritative parts here and not in the interpretations below *)
   ∃ (M_call_s M_call_t : gmap call_id (gmap ptr_id (gset loc)))
     (M_tag : gmap ptr_id (tag_kind * unit))
     (M_t M_s : gmap (ptr_id * loc) scalar) 
     (L : gset (block * block)),
    bor_auth M_call_s M_call_t M_tag M_t M_s L ∗

    heap_bij_interp sc_rel M_tag M_t M_call_t L σ_t σ_s ∗
    ⌜call_set_interp M_call_s σ_s⌝ ∗
    ⌜call_set_interp M_call_t σ_t⌝ ∗
    ⌜tag_interp M_tag M_t M_s σ_t σ_s⌝ ∗

    (* TODO: for the future, it would be nice to generalize that to a bijection, too *)
    ⌜σ_s.(snp) = σ_t.(snp)⌝ ∗
    ⌜σ_s.(snc) = σ_t.(snc)⌝ ∗
    ⌜σ_s.(scs) = σ_t.(scs)⌝ ∗
    ⌜state_wf σ_s⌝ ∗
    ⌜state_wf σ_t⌝.

  Lemma bor_interp_get_pure σ_t σ_s :
    bor_interp σ_t σ_s -∗ ⌜σ_s.(snp) = σ_t.(snp) ∧ σ_s.(snc) = σ_t.(snc) ∧ σ_s.(scs) = σ_t.(scs) ∧ state_wf σ_s ∧ state_wf σ_t⌝.
  Proof. iIntros "(% & % & % & % & % & %& ? & ? & ? & ? & ? & %)". eauto. Qed.
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
    iIntros "(% & % & % & % & % & % & ? & Hbij & ? & ? & Htag & %Hsnp & %Hsnc & %Hscs & %Hwf_s & %Hwf_t)".
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
    iIntros "(% & % & % & % & % & % & (Hc_t & ? & Htag_auth & Htag_t_auth & Htag_s_auth & Hbij_auth) & Hbij & ? & ? & %Htag_interp & %Hsnp & %Hsnc & %Hscs & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    destruct (Htag_interp _ _ Htag_lookup) as (_ & _ & Ha).
    destruct Ha as (lb_t & lb_s & len & Ha & Ht & _).
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    specialize (Ht _ _ Ht_lookup) as (o & -> & Ho).
    destruct (Ha o ltac:(lia)) as (sc_t & sc_s & Ht_lookup' & Hcontrol & _).
    rewrite Ht_lookup in Ht_lookup'. injection Ht_lookup' as [= <-].
    specialize (loc_controlled_local _ _ _ _ Hcontrol) as (Hstack & Hmem).
    iSplitR; first done. iSplitR; first done.
    iSplitR. { iPureIntro. intros tg l ->. 
      destruct tg as [tg | ]; last done.
      eapply state_wf_mem_tag; done.
    } 

    iIntros (sc') "%Hwf_sc".
    iMod (ghost_map_update sc' with "Htag_t_auth Hp") as "[Htag_t_auth $]".
    iModIntro. rewrite /bor_interp.
    iExists M_call_s, M_call_t, M_tag, (<[(t, lb_t +ₗ o):=sc']> M_t), M_s, L.
    iFrame. cbn. iSplitL "Hbij". 
    { iApply (heap_bij_interp_update_private_target with "Hbij"). 
      - eauto. 
      - exists tk_local. split_and!; [done | by eauto | by left ].
    } 
    iSplitR; first last.
    { repeat iSplitL; [ done.. | ].
      iPureIntro. apply state_wf_upd_mem; [by eauto | done | done].
    } 
    clear Ha lb_s sc_s.

    iPureIntro.
    intros t' tk' (? & ? & H')%Htag_interp. do 2 (split; first done).
    destruct H' as (lb_t' & lb_s' & len' & Hoo & Ha_t & Ha_s).
    exists lb_t', lb_s', len'. 
    split_and!; last done.
    - intros o' Ho'. specialize (Hoo _ Ho') as (sc_t & sc_s & Hoo). 
      destruct (decide (t = t')) as [<- | Hneq]; first last.
      { exists sc_t, sc_s. rewrite lookup_insert_ne; last congruence.
        split_and!; [ apply Hoo | | apply Hoo..].  
        destruct (decide (lb_t' +ₗ o' = lb_t +ₗ o)) as [-> | Hneq_loc].
        { (* this is contradictory, as tag t has local ownership *)
          admit.
        } 
        apply loc_controlled_mem_insert_ne; [done | apply Hoo]. 
      } 
      revert Hoo.
      destruct (decide (lb_t' +ₗ o' = lb_t +ₗ o)) as [-> | Hneq_loc] => Hoo.
      + exists sc', sc_s.
        rewrite lookup_insert. split_and!; [ done | | apply Hoo..].  
        eapply loc_controlled_mem_insert, Hoo.
      + exists sc_t, sc_s.
        rewrite lookup_insert_ne; last congruence. 
        split_and!; [ apply Hoo | | apply Hoo..].  
        eapply loc_controlled_mem_insert_ne; [done | apply Hoo].
    - (* easy *) admit.
  Admitted. 

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
        (* asserts that: the stacks are the same, the allocation size is the same, and that the locations are related *)
        l1 ↔h l2 ∗
        (⌜t1 = Untagged⌝ ∗ ⌜t2 = Untagged⌝) ∨
        (∃ p1 p2, ⌜t1 = Tagged p1⌝ ∗ ⌜t2 = Tagged p2⌝ ∗
        (* may want to generalize that properly when we have a proper bijection on tags*)
        ⌜p2 = p1⌝ ∗
        p1 @@ tk_pub
        (* note: we do not have any assertion about the value as viewed by the tag here -- we don't really care about it, we need to do a retag anyways *)
      )
    | _, _ => False
    end.
 
  Global Instance sc_rel_persistent sc_t sc_s : Persistent (sc_rel sc_t sc_s).
  Proof. destruct sc_t, sc_s; apply _. Qed.

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








