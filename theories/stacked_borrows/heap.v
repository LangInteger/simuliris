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




(* maintain for each tag: the permissions (public or unique) and, optionally, the
    regions of memory maintained by it: base locations for target and source, and the length of the maintained allocation.
*)
Class bor_stateG Σ := {
  (* Maintaining the stack & scalar for each location *)
  (*heap_inG :> ghost_mapG Σ loc (scalar * stack);*)
  (*heap_source_name : gname;*)
  (*heap_target_name : gname;*)

  (* A bijection on blocks, stating the size of the allocation and that the stacks are pointwise the same *)
  (*heap_bij_inG :> gset_bijG Σ block block;*)
  (*heap_bij_name : gname;*)

  (* Maintaining the locations protected by each call id *)
  call_inG :> ghost_mapG Σ call_id (gmap ptr_id (gset loc));
  call_source_name : gname;
  call_target_name : gname;

  (* tag ownership *)
  tag_inG :> tkmapG Σ ptr_id (option unit);
  tag_name : gname;

  (* A view of parts of the heap, conditional on the ptr_id *)
  heap_view_inG :> ghost_mapG Σ (ptr_id * loc) scalar;
  heap_view_source_name : gname;
  heap_view_target_name : gname;
}.

(* Interpretation for "local" fragments of the heap *)
(*Section loc_heap_defs.*)
  (*Context {Σ} (heap_gname : gname) {heap_inG : ghost_mapG Σ loc (scalar * stack)}.*)

  (*Definition heap_pointsto (l : loc) (sc : scalar)  (s : stack) :=*)
    (*ghost_map_elem heap_gname l (DfracOwn 1) (sc, s).*)

  (*Definition heap_interp (σ : state) : iProp Σ := *)
    (*∃ M : gmap loc (scalar * stack), ghost_map_auth heap_gname 1 M ∗*)
      (*⌜∀ l sc s, M !! l = Some (sc, s) → σ.(shp) !! l = Some sc ∧ σ.(sst) !! l = Some s⌝.*)


(*End loc_heap_defs.*)

(*Notation "l '↦t' sct" := (heap_pointsto heap_target_name l sct.1 sct.2)*)
  (*(at level 20, format "l  ↦t sct") : bi_scope.*)
(*Notation "l '↦s' sct" := (heap_pointsto heap_source_name l sct.1 sct.2)*)
  (*(at level 20, format "l  ↦s sct") : bi_scope.*)

(* Interpretation for call ids *)
Section call_defs.
  Context {Σ} (call_gname : gname) {call_inG : ghost_mapG Σ (call_id) (gmap ptr_id (gset loc))}.

  Implicit Types (c : call_id) (pid : ptr_id) (pm : permission).

  Definition call_set_is (c : call_id) (M : gmap ptr_id (gset loc)) :=
    ghost_map_elem call_gname c (DfracOwn 1) M.

  (* This does not assert ownership of the authoritative part. Instead, this is owned by bor_interp below, 
    since also the block bijection needs access to it. *)
  Definition call_set_interp (M : gmap call_id (gmap ptr_id (gset loc))) (σ : state) : iProp Σ :=
    ⌜∀ c (M' : gmap ptr_id (gset loc)), M !! c = Some M' →
      c ∈ σ.(scs) ∧
      (* for every ptr_id *)
      ∀ pid (S : gset loc), M' !! pid = Some S →
        pid < σ.(snp) ∧
        (* for every protected location [l], there needs to be a protector in the stack *)
        ∀ (l : loc), l ∈ S → ∃ s pm, σ.(sst) !! l = Some s ∧
          mkItem pm (Tagged pid) (Some c) ∈ s ∧ pm ≠ Disabled⌝.
End call_defs.

Notation "c '@s@' M" := (call_set_is call_source_name c M) (at level 50).
Notation "c '@t@' M" := (call_set_is call_target_name c M) (at level 50).

Notation "p '-->[' tk ']' ol" := (tkmap_elem tag_name p tk ol) (at level 50).

Definition state_upd_mem (f : mem → mem) σ :=
  mkState (f σ.(shp)) σ.(sst) σ.(scs) σ.(snp) σ.(snc).
Definition state_upd_stacks (f : stacks → stacks) σ :=
  mkState σ.(shp) (f σ.(sst)) σ.(scs) σ.(snp) σ.(snc).

(* Interpretation for heap assertions under control of tags
    The interpretation of the tag map and the "heap view" fragments are interlinked.
 *)
Section heap_defs.
  Context {Σ} (heap_gname_t heap_gname_s tag_name : gname) {tag_inG : tkmapG Σ ptr_id (option unit) } {heap_inG : ghost_mapG Σ (ptr_id * loc) scalar}.

  (** The assumption on the location still being valid for tag [t], i.e., [t] not being disabled. *)
  Definition bor_state_pre (l : loc) (t : ptr_id) (tk : tag_kind) (s : stack) :=
    tk = tk_local ∨ ∃ pm pro, mkItem pm (Tagged t) pro ∈ s ∧ pm ≠ Disabled.

  (* TODO: we should really try to pose weaker requirements here.
    maybe something like: there is a granting item for t among the items accessible from the top? *)
  Definition bor_state_own (l : loc) (t : ptr_id) (tk : tag_kind) (s : stack) :=
    (tk = tk_unq ∧ ∃ s' op, s = (mkItem Unique (Tagged t) op) :: s') ∨
    (tk = tk_pub ∧ t ∈ active_SRO s) ∨
    (tk = tk_local ∧ s = [mkItem Unique (Tagged t) None]).

  (* TODO: I think we will want to generalize this by not having these explicit ownership modes,
      but rather having a disjunction "either the value in the ghost state is current, because there are only reading items on top, or it is not current and there are other writing items on top.
      Then we could use the stack assertion to determine which case we are in and what behavior we get.
  *)
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



  (* TODO: probably need to incorporate here that the blocks are in bijection
      i.e.: stacks are pointwise the same, length of blocks is the same.
  *)
  Context (sc_rel : scalar → scalar → iProp Σ).
  Definition tag_interp (M : gmap ptr_id (tag_kind * option unit)) (M_t M_s : gmap (ptr_id * loc) scalar) σ_t σ_s : iProp Σ := 
    ∀ (t : ptr_id) tk ol, ⌜M !! t = Some (tk, ol)⌝ -∗
      (* tags are valid *)
      ⌜(t < σ_t.(snp))%nat⌝ ∧ ⌜(t < σ_s.(snp))%nat⌝ ∗
      (
        (* tag allocated, but locations are currently not shared *)
        (*⌜(ol = None ∧ ∀ l, M_t !! (t, l) = None ∧ M_s !! (t, l) = None)⌝ ∨*)
      (* tag allocated and the locations are shared *)
      (∃ lb_t lb_s (len : nat), ⌜ol = Some tt⌝ ∗
        (* at all offsets, the values agree, and match the physical state assuming the tag currently has control over the location *)
        (∀ o, ⌜o < len⌝ → ∃ sc_t sc_s,
          ⌜M_t !! (t, lb_t +ₗ o) = Some sc_t ∧ loc_controlled (lb_t +ₗ o) t tk sc_t σ_t ∧
          M_s !! (t, lb_s +ₗ o) = Some sc_s ∧ loc_controlled (lb_s +ₗ o) t tk sc_s σ_s⌝ ∗
          (* values need to be related if the tag is public. TODO: remove *)
          (⌜tk = tk_pub⌝ → sc_rel sc_t sc_s)) ∗
        (* TODO: assert same size of allocation here *)
        (* locations in the heap view are valid *)
        (⌜∀ l sc, M_t !! (t, l) = Some sc → ∃ o : nat, l = lb_t +ₗ o ∧ o < len⌝) ∗
        (⌜∀ l sc, M_s !! (t, l) = Some sc → ∃ o : nat, l = lb_s +ₗ o ∧ o < len⌝)
      )).
  Global Instance tag_interp_persistent M M_t M_s σ_t σ_s : 
    (∀ sc_t sc_s, Persistent (sc_rel sc_t sc_s)) → Persistent (tag_interp M M_t M_s σ_t σ_s).
  Proof. intros Hpers. apply _. Qed.
End heap_defs.

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


(* TODO *)
(*Section mem_bijection.*)
  (*Context {Σ} (sbijG_bij_name : gname) {bij_inG : gset_bijG Σ block block}.*)

  (*Definition heap_bij_auth (L : gset (block * block)) : iProp Σ :=*)
    (*gset_bij_own_auth sbijG_bij_name (DfracOwn 1) L.*)
  (*Definition heap_bij_elem (l_t : block) (l_s : block) :=*)
    (*gset_bij_own_elem sbijG_bij_name l_t l_s.*)

  (*Definition alloc_shr_rel val_rel b_t b_s pid : iProp Σ :=*)
    (*(∃ n vs_t vs_s, *)
      (*(Loc b_t 0, pid) ↦t∗{dq} map (λ v, (v, tk_shr)) vs_t ∗*)
      (*(Loc b_s 0, pid) ↦s∗{dq} map (λ v, (v, tk_shr)) vs_s ∗*)
      (*vrel_list val_rel vs_t vs_s ∗*)
      (*⌜length vs_t = n ∧ length vs_s = n⌝ ∗*)
      (*mkloc b_t 0 ==>t n ∗*)
      (*mkloc b_s 0 ==>s n).*)

  (*Definition alloc_unq_rel val_rel b_t b_s pid : iProp Σ :=*)
    (*(∃ (n : nat) vs_t vs_s,*)
      (*(Loc b_t 0, pid) ↦t∗ map (λ v, (v, tk_unq)) vs_t ∗*)
      (*(Loc b_s 0, pid) ↦s∗ map (λ v, (v, tk_unq)) vs_s ∗*)
      (*vrel_list val_rel vs_t vs_s ∗*)
      (*⌜length vs_t = n ∧ length vs_s = n⌝ ∗*)
      (*mkloc b_t 0 ==>t n ∗*)
      (*mkloc b_s 0 ==>s n).*)

  (*Definition heap_bij_interp (val_rel : val → val → iProp Σ) :=*)
    (*(∃ L, heap_bij_auth L ∗*)
      (*[∗ set] p ∈ L,*)
        (*let '(b_t, b_s) := p in alloc_unq_rel val_rel b_t b_s pid ∨ alloc_shr_rel val_rel b_t b_s pid)%I.*)
(*End definitions.*)

Section state_interp.
  Context `{bor_stateG Σ}.

  (* We generally do not enforce that stacks for all locations are equal: that would make non-determinism in choosing locations slightly clunky.
    Rather, we should again force equality in bijections.
  *)
  Definition bor_interp sc_rel (σ_t : state) (σ_s : state) : iProp Σ :=
  (* since multiple parts of the interpretation need access to these maps, we own the authoritative parts here and not in the interpretation below *)
   ∃ (M_call_s M_call_t : gmap call_id (gmap ptr_id (gset loc)))
     (M_tag : gmap ptr_id (tag_kind * option unit))
     (M_t M_s : gmap (ptr_id * loc) scalar),
    ghost_map_auth call_source_name 1 M_call_s ∗
    ghost_map_auth call_target_name 1 M_call_t ∗
    tkmap_auth tag_name 1 M_tag ∗
    ghost_map_auth heap_view_target_name 1 M_t ∗
    ghost_map_auth heap_view_source_name 1 M_s ∗
    
    call_set_interp M_call_s σ_s ∗
    call_set_interp M_call_t σ_t ∗
    tag_interp sc_rel M_tag M_t M_s σ_t σ_s ∗

    (*heap_interp heap_source_name σ_s ∗ *)
    (*heap_interp heap_target_name σ_t ∗*)

    (* TODO: for the future, it would be nice to generalize that to a bijection, too *)
    ⌜σ_s.(snp) = σ_t.(snp)⌝ ∗
    ⌜σ_s.(snc) = σ_t.(snc)⌝ ∗
    ⌜σ_s.(scs) = σ_t.(scs)⌝ ∗
    ⌜state_wf σ_s⌝ ∗
    ⌜state_wf σ_t⌝.

  Lemma bor_interp_get_pure sc_rel σ_t σ_s :
    bor_interp sc_rel σ_t σ_s -∗ ⌜σ_s.(snp) = σ_t.(snp) ∧ σ_s.(snc) = σ_t.(snc) ∧ σ_s.(scs) = σ_t.(scs) ∧ state_wf σ_s ∧ state_wf σ_t⌝.
  Proof. iIntros "(_&_&_&%)". eauto. Qed.

End state_interp.


(** Array generalizes pointsto connectives to lists of scalars *)
(*Definition array_local `{!bor_stateG Σ} γh (l : loc) (scts : list (scalar * stack)) : iProp Σ :=*)
  (*([∗ list] i ↦ sct ∈ scts, heap_pointsto γh (l +ₗ i) sct.1 sct.2)%I.*)
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

(*Notation "l '↦t∗' scts" := (array_local heap_target_name l scts)*)
  (*(at level 20, format "l  ↦t∗  scts") : bi_scope.*)
(*Notation "l '↦s∗' scts" := (array_local heap_source_name l scts)*)
  (*(at level 20, format "l  ↦s∗  scts") : bi_scope.*)

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

(** Lemmas / Accessors *)
Add Printing Constructor state item.
Section lemmas.
  Context `{bor_stateG Σ} (sc_rel : scalar → scalar → iProp Σ)
    (sc_rel_pers : ∀ sc_t sc_s, Persistent (sc_rel sc_t sc_s)).
  Notation bor_interp := (bor_interp sc_rel).

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
      t -->[tk_local] (Some ()) ∗
      l_t ↦t∗[local]{t} repeat ScPoison (tsize T) ∗
      l_s ↦s∗[local]{t} repeat ScPoison (tsize T).
  Proof.
    iIntros "(? & ? & Htag & %Hsnp & %Hsnc & %Hscs & %Hwf_s & %Hwf_t)".
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
    t -->[tk_local] (Some tt) -∗
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
    iIntros "(Hc_t & Hc_s & Htag_auth & %Hsnp & %Hsnc & %Hscs & %Hwf_s & %Hwf_t)".
    iIntros "Hp Htag".
    iDestruct "Htag_auth" as (M_tag Mtag_t Mtag_s) "(Htag_auth & Htag_t_auth & Htag_s_auth & #H)".
    iPoseProof (tkmap_lookup with "Htag_auth Htag") as "%Htag_lookup".
    iDestruct ("H" with "[//]") as "(_ & _ & Ha)".
    iDestruct "Ha" as (lb_t lb_s len) "(_ & Ha & %Ht & _)".
    iPoseProof (ghost_map_lookup with "Htag_t_auth Hp") as "%Ht_lookup".
    specialize (Ht _ _ Ht_lookup) as (o & -> & Ho).
    iDestruct ("Ha" $! o with "[//]") as (sc_t sc_s) "(%Hcontrol & _)".
    destruct Hcontrol as (Ht_lookup' & Hcontrol & _ & _).
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
    iFrame "Hc_t Hc_s". cbn. iSplitL; first last.
    { repeat iSplitL; [ done.. | ].
      iPureIntro. apply state_wf_upd_mem; [by eauto | done | done].
    } 
    iExists M_tag, (<[(t, lb_t +ₗ o):=sc']> Mtag_t), Mtag_s.
    iFrame. iClear "Ha Htag". clear lb_s sc_s.

    iIntros (t' tk' ol') "%Hlookup". iDestruct ("H" with "[//]") as "(? & ? & H')".
    do 2 (iSplitR; first done).
    iDestruct "H'" as (lb_t' lb_s' len') "(-> & Hoo & %Ha_t & %Ha_s)".
    iExists lb_t', lb_s', len'. iSplitR; first done.
    iSplitL; last iSplit; last done.
    - iIntros (o') "%Ho'". iDestruct ("Hoo" with "[//]") as (sc_t sc_s) "[%Hoo Hsc]".
      iClear "Hoo".
      destruct (decide (t = t')) as [<- | Hneq]; first last.
      { iExists sc_t, sc_s. rewrite lookup_insert_ne; last congruence.
        iSplitR; last iApply "Hsc". iPureIntro. 
        split_and!; [ apply Hoo | | apply Hoo..].  
        destruct (decide (lb_t' +ₗ o' = lb_t +ₗ o)) as [-> | Hneq_loc].
        { (* this is contradictory, as tag t has local ownership *)
          admit.
        } 
        apply loc_controlled_mem_insert_ne; [done | apply Hoo]. 
      } 
      rewrite Htag_lookup in Hlookup. injection Hlookup as [= <-].
      destruct (decide (lb_t' +ₗ o' = lb_t +ₗ o)) as [-> | Hneq_loc].
      + iExists sc', sc_s. iSplit; last (iIntros "%"; congruence).
        iPureIntro. 
        rewrite lookup_insert. split_and!; [ done | | apply Hoo..].  
        eapply loc_controlled_mem_insert; done.
      + iExists sc_t, sc_s. iSplit; last (iIntros "%"; congruence).
        iPureIntro. 
        rewrite lookup_insert_ne; last congruence. 
        split_and!; [ apply Hoo | | apply Hoo..].  
        eapply loc_controlled_mem_insert_ne; [done | apply Hoo].
    - iPureIntro. (* easy *) admit.
  Admitted. 

  Lemma heap_local_accessN_target' σ_t σ_s (t : ptr_id) l scs :
    bor_interp σ_t σ_s -∗
    l ↦t∗[local]{t} scs -∗
    t -->[tk_local] (Some tt) -∗
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
    t -->[tk_local] (Some tt) -∗
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

  Lemma heap_local_access_source σ_t σ_s (t : ptr_id) l  sc :
    bor_interp σ_t σ_s -∗
    l ↦s[local]{t} sc -∗
    t -->[tk_local] (Some tt) -∗
    ⌜σ_s.(shp) !! l = Some sc⌝ ∗
    ⌜σ_s.(sst) !! l = Some [mkItem Unique (Tagged t) None]⌝ ∗
    ⌜wf_scalar σ_s sc⌝ ∗
    (∀ sc',
      ⌜wf_scalar σ_t sc' ⌝ -∗
      (*stack_wf st' σ_t -∗ *)
      |==>
      bor_interp σ_t (state_upd_mem (<[l := sc']>) σ_s) ∗
      l ↦s[local]{t} sc').
  Proof.
  Admitted. 

  Lemma heap_local_accessN_source σ_t σ_s (t : ptr_id) l scs :
    bor_interp σ_t σ_s -∗
    l ↦s∗[local]{t} scs -∗
    t -->[tk_local] (Some tt) -∗
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











Section val_rel.
  Context {Σ} `{bor_stateG Σ}.
  Fixpoint sc_rel (sc1 sc2 : scalar) {struct sc2} : iProp Σ :=
    match sc1, sc2 with
    | ScInt z1, ScInt z2 => ⌜z1 = z2⌝
    | ScFnPtr f1, ScFnPtr f2 => ⌜f1  = f2⌝
    | ScPtr l1 t1, ScPtr l2 t2 =>
        (⌜t1 = Untagged⌝ ∗ ⌜t2 = Untagged⌝ (* TODO: probably need somethng more here *)) ∨
        (∃ p1 p2, ⌜t1 = Tagged p1⌝ ∗ ⌜t2 = Tagged p2⌝ ∗
        (* TODO: may want to generalize that properly when we have a proper bijection on tags*)
        ⌜p2 = p1⌝ ∗
        p1 -->[tk_pub] (Some tt)
        (* note: we do not have any assertion about the value as viewed by the tag here -- we don't really care about it, we need to do a retag anyways *)
      )
    | _, _ => False
    end.
 
  Global Instance sc_rel_persistent sc_t sc_s : Persistent (sc_rel sc_t sc_s).
  Proof. destruct sc_t, sc_s; apply _. Qed.

  (*Definition val_rel (v1 v2 : value) *)
End val_rel.

Class sborG (Σ: gFunctors) := SBorG {
  sborG_gen_progG :> gen_sim_progG string ectx ectx Σ;
  sborG_stateG :> bor_stateG Σ;
}.

Global Instance sborG_SimulLang `{!sborG Σ} : SimulLang (iPropI Σ) bor_lang := {
  state_interp P_t σ_t P_s σ_s :=
    (gen_prog_interp (hG := gen_prog_inG_target) P_t ∗
     gen_prog_interp (hG := gen_prog_inG_source) P_s ∗
     bor_interp sc_rel σ_t σ_s
    )%I;
}.


Section lifting.
Context `{!sborG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : expr → expr → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types r r_s r_t : result.
Implicit Types l : loc.
Implicit Types f : fname.

Context (Ω : result → result → iProp Σ).
Local Notation "et '⪯' es [{ Φ }]" := (et ⪯{Ω} es [{Φ}])%I (at level 40, Φ at level 200) : bi_scope.
Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{Ω} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

(*Definition as_local (scs : list scalar) t := map (λ sc, (sc, [mkItem Unique (Tagged t) None])) scs.*)
(*Lemma as_local_const sc n t :*)
  (*as_local (repeat sc n) t = repeat (sc, [mkItem Unique (Tagged t) None]) n.*)
(*Proof.*)
  (*induction n as [ | n IH]; cbn; first done. by rewrite -IH.*)
(*Qed.*)

Lemma sim_alloc T Φ :
  (∀ t l_t l_s, t -->[tk_local] Some () -∗
    l_t ↦t∗[local]{t} repeat ScPoison (tsize T) -∗
    l_s ↦s∗[local]{t} repeat ScPoison (tsize T) -∗
    Place l_t (Tagged t) T ⪯ Place l_s (Tagged t) T {{ Φ }}) -∗
  Alloc T ⪯ Alloc T {{ Φ }}.
Proof.
  iIntros "Hsim".
  iApply sim_lift_head_step_both. iIntros (????) "[(HP_t & HP_s & Hbor) %Hnreach]".
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

Lemma target_local_copy scs T l t Ψ :
  length scs = tsize T →
  t -->[tk_local] Some tt -∗ 
  l ↦t∗[local]{t} scs -∗
  (l ↦t∗[local]{t} scs -∗ target_red #scs Ψ)%E -∗
  target_red (Copy (Place l (Tagged t) T)) Ψ.
Proof.
  iIntros (Hlen) "Htag Ht Hsim".
  iApply target_red_lift_head_step. iIntros (????) "(HP_t & HP_s & Hbor)".
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

Lemma source_local_copy scs T l t Ψ :
  length scs = tsize T →
  t -->[tk_local] Some tt -∗ 
  l ↦s∗[local]{t} scs -∗
  (l ↦s∗[local]{t} scs -∗ source_red #scs Ψ)%E -∗
  source_red (Copy (Place l (Tagged t) T)) Ψ.
Proof.
  iIntros (Hlen) "Htag Hs Hsim".
  iApply source_red_lift_head_step. iIntros (????) "[(HP_t & HP_s & Hbor) _]".
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

Lemma sim_retag_default_mutref l_t l_s ot Φ c pkind T : 
  (∀ nt, t -->[tk_local] #[ScPtr l_t nt] ⪯ #[ScPtr l_s nt] [{ Φ }]) -∗
  Retag #[ScPtr l_t ot] #[ScCallId c] (RefPtr Mutable) T Default ⪯ Retag #[ScPtr l_s ot] #[ScCallId c] (RefPtr Mutable) T Default [{ Φ }].
Proof. 









