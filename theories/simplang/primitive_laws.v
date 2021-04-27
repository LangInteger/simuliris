(** This file proves the basic laws of the SimpLang program logic by applying
the Simuliris lifting lemmas. *)

From iris.proofmode Require Export tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_heap gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.simplang Require Export class_instances tactics notation.
From iris.prelude Require Import options.

(** Allocation state for each block: either deallocated or allocated with total size n*)
Inductive alloc_state :=
  | DeallocSt
  | AllocSt (n : nat).

Class sheapG (Σ: gFunctors) := SHeapG {
  sheapG_gen_heapG :> gen_sim_heapG loc loc (option (lock_state * val)) (option (lock_state * val)) Σ;
  sheapG_gen_progG :> gen_sim_progG string ectx ectx Σ;
  (* allocation size control *)
  sheapG_ghost_mapG :> ghost_mapG Σ block alloc_state;
  sheapG_allocN_source : gname;
  sheapG_allocN_target : gname;
}.

(** This class is instantiated per proof (usually at the beginning of the file).
   It states additional components of the state interpretation, i.e.,
   invariants on the relation of source and target programs and states.
 *)
Class sheapInv (Σ : gFunctors) := SHeapRel {
  sheap_inv : iProp Σ;
}.

(** Allocation size control, serving as a tracker of the size of blocks and a deallocation permission for whole blocks *)
Section alloc_size.
  Context `{ghost_mapG Σ block alloc_state}.

  Definition heap_alloc_rel (M : gmap block alloc_state) (σ : gmap loc (option (lock_state * val))) :=
      (* allocations have a positive size *)
      (∀ b l, M !! b = Some (AllocSt l) → l > 0) ∧
      (* l is the full length of the allocation *)
      (∀ b l, M !! b = Some (AllocSt l) → (∀ i, (∃ v, σ !! (mkloc b i) = Some (Some v)) ↔ (0 ≤ i < Z.of_nat l)%Z)) ∧
      (* deallocated*)
      (∀ b, M !! b = Some DeallocSt → (∀ i, σ !! (mkloc b i) = None ∨ σ !! (mkloc b i) = Some (None)) 
        (* but we need to make sure that at least one location, at offset 0, was allocated at some point before, 
           to make the bijection on heap locations work (having [Some None] allows us to use stuckness) *)
        ∧ σ !! (mkloc b 0) = Some None).
  Definition alloc_size_interp (γ : gname) (σ : gmap loc (option (lock_state * val))) : iProp Σ :=
    ∃ M, ghost_map_auth γ 1 M ∗ ⌜heap_alloc_rel M σ⌝.

  Lemma alloc_size_update γ (l : loc) v v' (σ : gmap loc (option (lock_state * val))) :
    σ !! l = Some (Some v) →
    alloc_size_interp γ σ -∗
    alloc_size_interp γ (<[ l := Some v' ]> σ).
  Proof.
    iIntros (Hlookup) "Hinterp". iDestruct "Hinterp" as (M) "[Hauth %Hrel]".
    iExists M. iFrame. iPureIntro.
    destruct Hrel as (Hgt & Hequiv & Hdealloc). split; first done. split.
    - intros b l' Hml i. specialize (Hequiv _ _ Hml). rewrite -Hequiv.
      split; intros (w & Hl).
      + destruct (decide (l = mkloc b i)) as [-> | Hneq].
        * eauto.
        * apply lookup_insert_Some in Hl as [(Heq' & [= ->]) |[_ ?] ]; [congruence | eauto].
      + destruct (decide (l = mkloc b i)) as [-> | Hneq].
        * exists v'. apply lookup_insert_Some; by left.
        * exists w. apply lookup_insert_Some; by right.
    - intros b Hml; split.
      + intros i; specialize (proj1 (Hdealloc _ Hml) i) as [Hdealloc' | Hdealloc'].
        * left. destruct (decide (l = mkloc b i)) as [-> | Hneq]; first congruence.
          apply lookup_insert_None; eauto.
        * right. destruct (decide (l = mkloc b i)) as [-> | Hneq]; first congruence.
          apply lookup_insert_Some; by right.
      + specialize (proj2 (Hdealloc _ Hml) ) as Hdealloc'.
        destruct (decide (l = mkloc b 0)) as [-> | Hneq]; first congruence.
        apply lookup_insert_Some; by right.
  Qed.

  Lemma alloc_size_lookup_alloc γ b σ n :
    ghost_map_elem γ b (DfracOwn 1) (AllocSt n) -∗
    alloc_size_interp γ σ -∗
    ⌜(∀ i, (∃ v, σ !! (mkloc b i) = Some (Some v)) ↔ (0 ≤ i < Z.of_nat n)%Z) ∧ n > 0⌝.
  Proof.
    iIntros "Helem Hauth". iDestruct "Hauth" as (M) "[Hauth %Hrel]".
    iDestruct (ghost_map_lookup with "Hauth Helem") as "%He". iPureIntro. split; by eapply Hrel.
  Qed.

  Lemma alloc_size_lookup_dealloc γ b σ :
    ghost_map_elem γ b (DfracOwn 1) DeallocSt -∗
    alloc_size_interp γ σ -∗
    ⌜∀ i, σ !! (mkloc b i) = None ∨ σ !! (mkloc b i) = Some None⌝.
  Proof.
    iIntros "Helem Hauth". iDestruct "Hauth" as (M) "[Hauth %Hrel]".
    iDestruct (ghost_map_lookup with "Hauth Helem") as "%He". iPureIntro. by eapply Hrel.
  Qed.

  Lemma alloc_size_free γ b σ (n : nat) :
    ghost_map_elem γ b (DfracOwn 1) (AllocSt n) -∗
    alloc_size_interp γ σ ==∗
    alloc_size_interp γ (free_mem (mkloc b 0) n σ) ∗ ghost_map_elem γ b (DfracOwn 1) DeallocSt.
  Proof.
    iIntros "Helem Hauth". iDestruct (alloc_size_lookup_alloc with "Helem Hauth") as "%Hl_prev".
    iDestruct "Hauth" as (M) "[Hauth %Hrel]".
    iMod (ghost_map_update DeallocSt with "Hauth Helem") as "[Hauth Helem]". iFrame.
    iModIntro. iExists (<[b := DeallocSt]> M). iFrame "Hauth". iPureIntro.
    destruct Hrel as (Hsize &Hrel &Hdealloc). split; [ | split].
    - intros b' l Hl. apply lookup_insert_Some in Hl as [[_ [=]] | [_ Hl]]. by eapply Hsize.
    - intros b' l Hl i. apply lookup_insert_Some in Hl as [[_ [=]] | [Hneq Hl]]. split.
      + intros (w & Hlookup). apply (Hrel _ _ Hl). exists w.
        erewrite <-lookup_free_mem_1; [done| intros [=];congruence].
      + intros (w & Hlookup)%(Hrel _ _ Hl). exists w.
        rewrite lookup_free_mem_1; [done | intros [=]; congruence].
    - intros b' Hl. destruct (decide (b = b')) as [<- | Hneq].
      + split.
        * assert (∀ i, ¬ (0 ≤ i < n)%Z → σ !! (mkloc b i) = None ∨ σ !! (mkloc b i) = Some None) as Hi.
          { intros i Hni. destruct (σ !! _) as [[] | ] eqn:Hi; [ | by eauto..].
            contradict Hni. apply Hl_prev. eauto. }
          intros i.
          destruct (decide (i < 0)%Z). { rewrite lookup_free_mem_3; [ | done | cbn; lia]. apply Hi; lia. }
          destruct (decide (i < n)%Z); first last. { rewrite lookup_free_mem_4; [ | done | cbn; lia]. apply Hi; lia. }
          right. apply lookup_free_mem_2; [done | cbn; lia ].
        * apply lookup_free_mem_2; [done | cbn; lia].
      + rewrite lookup_free_mem_1; last done. split.
        { intros i. rewrite lookup_free_mem_1; last done. apply Hdealloc.
          apply lookup_insert_Some in Hl as [[] | [_ ?]]; done.
        }
        apply Hdealloc. apply lookup_insert_Some in Hl as [[] | [_ ?]]; done.
  Qed.

  Lemma heap_alloc_rel_allocN M b σ ls :
    length ls > 0 →
    (∀ i, σ !! (mkloc b i) = None) →
    heap_alloc_rel M σ →
    heap_alloc_rel (<[b := AllocSt (length ls)]> M) (heap_array (mkloc b 0) ls ∪ σ).
  Proof.
    intros Hl Hd (Hsize & Hm &Hdealloc).
    assert (heap_array (mkloc b 0) ls ##ₘ σ) as Hdisj.
    { apply heap_array_map_disjoint. intros i Hi Hi'. apply Hd. }
    split.
    { intros b' n [[<- [= <-]] | [_ Hs]]%lookup_insert_Some; first done. by eapply Hsize. }
    split.
    { intros b' n. rewrite lookup_insert_Some.
      intros [[<- [= <-]] | [? Hs]] i.
      - split.
        + intros (v & [Hlookup | Hlookup]%lookup_union_Some); last done.
          * apply heap_array_lookup in Hlookup as (j & w & ? & Heq & [= ->] & ?).
            inversion Heq; subst. apply list_lookup_alt in H3 as (? & _). lia.
          * exfalso. congruence.
        + intros [H1 H2]. exists (RSt 0, (ls !!! (Z.to_nat i))).
          apply lookup_union_Some_l. apply heap_array_lookup.
          exists i, (ls !!! Z.to_nat i). repeat split; [done | ].
          apply list_lookup_lookup_total_lt. lia.
      - split.
        + intros (v & [Hlookup | Hlookup]%lookup_union_Some); last done.
          * exfalso. apply heap_array_lookup in Hlookup as (j & w & ? & ? & [= ->] & ?).
            inversion H3; subst. congruence.
          * apply (Hm _ _ Hs); eauto.
        + intros (v & Hi)%(Hm _ _ Hs). exists v. apply lookup_union_Some_r; done.
    }
    { intros b'. rewrite lookup_insert_Some. intros [[_ [=]] | [Hneq Hlookup]]; split.
      - intros i; rewrite lookup_union_r; first by eapply Hdealloc.
        destruct (heap_array _ _ !! _) eqn:Heq; last done.
        apply heap_array_lookup in Heq as (j & w & ? & [=] & ?); congruence.
      - rewrite lookup_union_r; first by eapply Hdealloc.
        destruct (heap_array _ _ !! _) eqn:Heq; last done.
        apply heap_array_lookup in Heq as (j & w & ? & [=] & ?); congruence.
    }
  Qed.

  Lemma alloc_size_allocN γ b σ ls :
    length ls > 0 →
    (∀ i, σ !! (mkloc b i) = None) →
    alloc_size_interp γ σ ==∗
    alloc_size_interp γ (heap_array (mkloc b 0) ls ∪ σ) ∗
    ghost_map_elem γ b (DfracOwn 1) (AllocSt (length ls)).
  Proof.
    iIntros (Hl Hd) "Hi". iDestruct "Hi" as (M) "(Hauth & %Hsize & %Hm & %Hdealloc)".
    iMod (ghost_map_insert b (AllocSt (length ls)) with "Hauth") as "[Hauth $]".
    { destruct (M !! b) eqn:Hlookup; last done. destruct a.
      - specialize (Hdealloc _ Hlookup) as [_ Hdealloc]. congruence.
      - specialize (Hm _ _ Hlookup) as Hm1. specialize (Hsize _ _ Hlookup).
        destruct (proj2 (Hm1 0) ltac:(lia)). specialize (Hd 0). congruence.
    }
    iModIntro. iExists (<[b := AllocSt (length ls)]> M). iFrame "Hauth". iPureIntro.
    by apply heap_alloc_rel_allocN.
  Qed.

End alloc_size.
Section heap.

End heap.

Global Instance sheapG_SimulLang `{!sheapG Σ} `{!sheapInv Σ} : SimulLang (iPropI Σ) simp_lang := {
  state_interp P_t σ_t P_s σ_s :=
    (gen_prog_interp (hG := gen_prog_inG_target) P_t ∗
     gen_prog_interp (hG := gen_prog_inG_source) P_s ∗
     gen_heap_interp (hG := gen_heap_inG_target) σ_t.(heap) ∗
     gen_heap_interp (hG := gen_heap_inG_source) σ_s.(heap) ∗
     alloc_size_interp sheapG_allocN_target σ_t.(heap) ∗
     alloc_size_interp sheapG_allocN_source σ_s.(heap) ∗
     sheap_inv
    )%I;
}.

(** Since we use an [option val] instance of [gen_heap], we need to overwrite
the notations.  That also helps for scopes and coercions. *)
(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "l '↦t{' dq } v" := (mapsto (hG:=gen_heap_inG_target) (L:=loc) (V:=option (lock_state * val)) l dq (Some (RSt 0, v%V)))
  (at level 20, format "l  ↦t{ dq }  v") : bi_scope.
Notation "l '↦t□' v" := (mapsto (hG:=gen_heap_inG_target) (L:=loc) (V:=option (lock_state * val)) l DfracDiscarded (Some (RSt 0, v%V)))
  (at level 20, format "l  ↦t□  v") : bi_scope.
Notation "l '↦t{#' q } v" := (mapsto (hG:=gen_heap_inG_target) (L:=loc) (V:=option (lock_state * val)) l (DfracOwn q) (Some (RSt 0, v%V)))
  (at level 20, format "l  ↦t{# q }  v") : bi_scope.
Notation "l '↦t' v" := (mapsto (hG:=gen_heap_inG_target) (L:=loc) (V:=option (lock_state * val)) l (DfracOwn 1) (Some (RSt 0, v%V)))
  (at level 20, format "l  ↦t  v") : bi_scope.
Notation "l '↦{' st '}t' v" := (mapsto (hG:=gen_heap_inG_target) (L:=loc) (V:=option (lock_state * val)) l (DfracOwn 1) (Some (st, v%V)))
  (at level 20, format "l  ↦{ st }t  v") : bi_scope.

Notation "l '↦s{' dq } v" := (mapsto (hG:=gen_heap_inG_source) (L:=loc) (V:=option (lock_state * val)) l dq (Some (RSt 0, v%V)))
  (at level 20, format "l  ↦s{ dq }  v") : bi_scope.
Notation "l '↦s□' v" := (mapsto (hG:=gen_heap_inG_source) (L:=loc) (V:=option (lock_state * val)) l DfracDiscarded (Some (RSt 0, v%V)))
  (at level 20, format "l  ↦s□  v") : bi_scope.
Notation "l '↦s{#' q } v" := (mapsto (hG:=gen_heap_inG_source) (L:=loc) (V:=option (lock_state * val)) l (DfracOwn q) (Some (RSt 0, v%V)))
  (at level 20, format "l  ↦s{# q }  v") : bi_scope.
Notation "l '↦s' v" := (mapsto (hG:=gen_heap_inG_source) (L:=loc) (V:=option (lock_state * val)) l (DfracOwn 1) (Some (RSt 0, v%V)))
  (at level 20, format "l  ↦s  v") : bi_scope.
Notation "l '↦{' st '}s' v" := (mapsto (hG:=gen_heap_inG_source) (L:=loc) (V:=option (lock_state * val)) l (DfracOwn 1) (Some (st, v%V)))
  (at level 20, format "l  ↦{ st }s  v") : bi_scope.

(** The [array] connective is a version of [mapsto] that works with lists of values. *)
(** [array_st] is parameterized over the individual lock states *)
(* again parameterized over the ghost names *)
Definition array_st `{!sheapG Σ} {γh γm} {hG : gen_heapPreNameG loc (option (lock_state * val)) Σ γh γm} (l : loc) (dq : dfrac) (vs : list val) (sts : list lock_state) : iProp Σ :=
  ([∗ list] i ↦ v; st ∈ vs; sts, mapsto (hG:=hG) (l +ₗ i) dq (Some (st, v%V)))%I.
Definition array `{!sheapG Σ} {γh γm} {hG : gen_heapPreNameG loc (option (lock_state * val)) Σ γh γm} (l : loc) (dq : dfrac) (vs : list val) : iProp Σ := array_st l dq vs (replicate (length vs) (RSt 0)).

Lemma array_st_length_inv `{!sheapG Σ} {γh γm} {hG : gen_heapPreNameG loc (option (lock_state * val)) Σ γh γm} (l : loc) (dq : dfrac) (vs : list val) (sts : list lock_state) :
  array_st l dq vs sts -∗ ⌜ length vs = length sts⌝.
Proof. iApply big_sepL2_length. Qed.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "l ↦t∗{ dq } vs" := (array (hG:=gen_heap_inG_target) l dq vs)
  (at level 20, format "l  ↦t∗{ dq }  vs") : bi_scope.
Notation "l ↦t∗□ vs" := (array (hG:=gen_heap_inG_target) l DfracDiscarded vs)
  (at level 20, format "l  ↦t∗□  vs") : bi_scope.
Notation "l ↦t∗{# q } vs" := (array (hG:=gen_heap_inG_target) l (DfracOwn q) vs)
  (at level 20, format "l  ↦t∗{# q }  vs") : bi_scope.
Notation "l ↦t∗ vs" := (array (hG:=gen_heap_inG_target) l (DfracOwn 1) vs)
  (at level 20, format "l  ↦t∗  vs") : bi_scope.
Notation "l '↦{' sts '}t∗' vs" := (array_st (hG:=gen_heap_inG_target) l (DfracOwn 1) vs sts)
  (at level 20, format "l  '↦{' sts '}t∗'  vs") : bi_scope.

Notation "l ↦s∗{ dq } vs" := (array (hG:=gen_heap_inG_source) l dq vs)
  (at level 20, format "l  ↦s∗{ dq }  vs") : bi_scope.
Notation "l ↦s∗□ vs" := (array (hG:=gen_heap_inG_source) l DfracDiscarded vs)
  (at level 20, format "l  ↦s∗□  vs") : bi_scope.
Notation "l ↦s∗{# q } vs" := (array (hG:=gen_heap_inG_source) l (DfracOwn q) vs)
  (at level 20, format "l  ↦s∗{# q }  vs") : bi_scope.
Notation "l ↦s∗ vs" := (array (hG:=gen_heap_inG_source) l (DfracOwn 1) vs)
  (at level 20, format "l  ↦s∗  vs") : bi_scope.
Notation "l '↦{' sts '}s∗' vs" := (array_st (hG:=gen_heap_inG_source) l (DfracOwn 1) vs sts)
  (at level 20, format "l  '↦{' sts '}s∗'  vs") : bi_scope.

(** Program assertions *)
Notation "f '@t' Kt" := (hasfun (hG:=gen_prog_inG_target) f Kt)
  (at level 20, format "f  @t  Kt") : bi_scope.
Notation "f '@s' Ks" := (hasfun (hG:=gen_prog_inG_source) f Ks)
  (at level 20, format "f  @s  Ks") : bi_scope.

(** Allocation size notation *)
Notation "l '==>s' n" := (ghost_map_elem sheapG_allocN_source (loc_chunk l) (DfracOwn 1) (AllocSt n))
  (at level 20, format "l  ==>s  n") : bi_scope.
Notation "l '==>t' n" := (ghost_map_elem sheapG_allocN_target (loc_chunk l) (DfracOwn 1) (AllocSt n))
  (at level 20, format "l  ==>t  n") : bi_scope.
Notation "'†s' l" := (ghost_map_elem sheapG_allocN_source (loc_chunk l) (DfracOwn 1) DeallocSt)
  (at level 20, format "†s  l") : bi_scope.
Notation "'†t' l" := (ghost_map_elem sheapG_allocN_target (loc_chunk l) (DfracOwn 1) DeallocSt)
  (at level 20, format "†t  l") : bi_scope.

Section lifting.
Context `{!sheapG Σ} `{!sheapInv Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → val → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types v v_s v_t : val.
Implicit Types l : loc.
Implicit Types f : fname.

Context (Ω : val → val → iProp Σ).
Local Notation "et '⪯' es [{ Φ }]" := (et ⪯{Ω} es [{Φ}])%I (at level 40, Φ at level 200) : bi_scope.


(** Heap for target *)

(** We need to adjust the [gen_heap] lemmas because of our
value type being [option val]. *)

Lemma mapsto_target_valid l dq v : l ↦t{dq} v -∗ ⌜✓ dq⌝.
Proof. apply mapsto_valid. Qed.
Lemma mapsto_target_valid_2 l dq1 dq2 v1 v2 :
  l ↦t{dq1} v1 -∗ l ↦t{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  iIntros "H1 H2". iDestruct (mapsto_valid_2 with "H1 H2") as %[? [=?]]. done.
Qed.
Lemma mapsto_target_agree l dq1 dq2 v1 v2 : l ↦t{dq1} v1 -∗ l ↦t{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %[=?]. done. Qed.

Lemma mapsto_target_combine l dq1 dq2 v1 v2 :
  l ↦t{dq1} v1 -∗ l ↦t{dq2} v2 -∗ l ↦t{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". iDestruct (mapsto_combine with "Hl1 Hl2") as "[$ Heq]".
  by iDestruct "Heq" as %[= ->].
Qed.

Lemma mapsto_target_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦t{dq1} v1 -∗ l2 ↦t{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_frac_ne. Qed.
Lemma mapsto_target_ne l1 l2 dq2 v1 v2 : l1 ↦t v1 -∗ l2 ↦t{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_ne. Qed.

Lemma mapsto_target_persist l dq v : l ↦t{dq} v ==∗ l ↦t□ v.
Proof. apply mapsto_persist. Qed.

(** Heap for source *)

Lemma mapsto_source_valid l dq v : l ↦s{dq} v -∗ ⌜✓ dq⌝.
Proof. apply mapsto_valid. Qed.
Lemma mapsto_source_valid_2 l dq1 dq2 v1 v2 :
  l ↦s{dq1} v1 -∗ l ↦s{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  iIntros "H1 H2". iDestruct (mapsto_valid_2 with "H1 H2") as %[? [=?]]. done.
Qed.
Lemma mapsto_source_agree l dq1 dq2 v1 v2 : l ↦s{dq1} v1 -∗ l ↦s{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %[=?]. done. Qed.

Lemma mapsto_source_combine l dq1 dq2 v1 v2 :
  l ↦s{dq1} v1 -∗ l ↦s{dq2} v2 -∗ l ↦s{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". iDestruct (mapsto_combine with "Hl1 Hl2") as "[$ Heq]".
  by iDestruct "Heq" as %[= ->].
Qed.

Lemma mapsto_source_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦s{dq1} v1 -∗ l2 ↦s{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_frac_ne. Qed.
Lemma mapsto_source_ne l1 l2 dq2 v1 v2 : l1 ↦s v1 -∗ l2 ↦s{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_ne. Qed.

Lemma mapsto_source_persist l dq v : l ↦s{dq} v ==∗ l ↦s□ v.
Proof. apply mapsto_persist. Qed.

(** Array lemmas *)
Lemma target_array_st_access vs sts (i : nat) v st l :
  vs !! i = Some v →
  sts !! i = Some st →
  l ↦{sts}t∗ vs -∗
  (l +ₗ i) ↦{st}t v ∗ (∀ v' st', (l +ₗ i) ↦{st'}t v' -∗ l ↦{<[i := st']> sts}t∗ <[i := v']>vs).
Proof.
  iIntros (Hsome_v Hsome_st) "Hs".
  rewrite /array_st. iApply (big_sepL2_insert_acc _ _ _ i v st Hsome_v Hsome_st with "Hs").
Qed.

Lemma source_array_st_access vs sts (i : nat) v st l :
  vs !! i = Some v →
  sts !! i = Some st →
  l ↦{sts}s∗ vs -∗
  (l +ₗ i) ↦{st}s v ∗ (∀ v' st', (l +ₗ i) ↦{st'}s v' -∗ l ↦{<[i := st']> sts}s∗ <[i := v']>vs).
Proof.
  iIntros (Hsome_v Hsome_st) "Hs".
  rewrite /array_st. iApply (big_sepL2_insert_acc _ _ _ i v st Hsome_v Hsome_st with "Hs").
Qed.

Lemma target_array_access vs (i : nat) v l :
  vs !! i = Some v →
  l ↦t∗ vs -∗
  (l +ₗ i) ↦t v ∗ (∀ v', (l +ₗ i) ↦t v' -∗ l ↦t∗ <[i := v']>vs).
Proof.
  iIntros (Hsome) "Hs". rewrite /array.
  iPoseProof (target_array_st_access vs (replicate (length vs) (RSt 0)) i v (RSt 0) l with "Hs") as "[$ Ha]"; first done.
  { apply lookup_replicate; split; [done | ]. by eapply list_lookup_alt. }
  iIntros (v') "Hv'". iSpecialize ("Ha" $! v' (RSt 0) with "Hv'").
  by rewrite insert_replicate insert_length.
Qed.

Lemma source_array_access vs (i : nat) v l :
  vs !! i = Some v →
  l ↦s∗ vs -∗
  (l +ₗ i) ↦s v ∗ (∀ v', (l +ₗ i) ↦s v' -∗ l ↦s∗ <[i := v']>vs).
Proof.
  iIntros (Hsome) "Hs". rewrite /array.
  iPoseProof (source_array_st_access vs (replicate (length vs) (RSt 0)) i v (RSt 0) l with "Hs") as "[$ Ha]"; first done.
  { apply lookup_replicate; split; [done | ]. by eapply list_lookup_alt. }
  iIntros (v') "Hv'". iSpecialize ("Ha" $! v' (RSt 0) with "Hv'").
  by rewrite insert_replicate insert_length.
Qed.

Lemma source_array_st_access' vs sts l :
  (0 ≤ loc_idx l < length vs)%Z →
  (mkloc (loc_chunk l) 0) ↦{sts}s∗ vs -∗
  l ↦{sts !!! Z.to_nat (loc_idx l)}s (vs !!! Z.to_nat (loc_idx l)) ∗
  (∀ v' st', l ↦{st'}s v' -∗ (mkloc (loc_chunk l) 0) ↦{<[Z.to_nat (loc_idx l) := st']> sts}s∗ (<[Z.to_nat (loc_idx l) := v']> vs)).
Proof.
  iIntros (Hsome) "Hs".
  iPoseProof (array_st_length_inv with "Hs") as "%Hl".
  iPoseProof (source_array_st_access _ _ (Z.to_nat (loc_idx l)) with "Hs") as "[Hl_s Hclose_s]".
  { apply list_lookup_alt. split; last reflexivity. lia. }
  { apply list_lookup_alt. split; last reflexivity. lia. }
  rewrite mkloc_add. assert (Z.of_nat (Z.to_nat (loc_idx l))= loc_idx l) as -> by lia. rewrite loc_eta.
  iFrame.
Qed.

Lemma target_array_st_access' vs sts l :
  (0 ≤ loc_idx l < length vs)%Z →
  (mkloc (loc_chunk l) 0) ↦{sts}t∗ vs -∗
  l ↦{sts !!! Z.to_nat (loc_idx l)}t (vs !!! Z.to_nat (loc_idx l)) ∗
  (∀ v' st', l ↦{st'}t v' -∗ (mkloc (loc_chunk l) 0) ↦{<[Z.to_nat (loc_idx l) := st']> sts}t∗ (<[Z.to_nat (loc_idx l) := v']> vs)).
Proof.
  iIntros (Hsome) "Hs".
  iPoseProof (array_st_length_inv with "Hs") as "%Hl".
  iPoseProof (target_array_st_access _ _ (Z.to_nat (loc_idx l)) with "Hs") as "[Hl_s Hclose_s]".
  { apply list_lookup_alt. split; last reflexivity. lia. }
  { apply list_lookup_alt. split; last reflexivity. lia. }
  rewrite mkloc_add. assert (Z.of_nat (Z.to_nat (loc_idx l))= loc_idx l) as -> by lia. rewrite loc_eta.
  iFrame.
Qed.

Lemma source_array_access' vs l :
  (0 ≤ loc_idx l < length vs)%Z →
  (mkloc (loc_chunk l) 0) ↦s∗ vs -∗
  l ↦s (vs !!! Z.to_nat (loc_idx l)) ∗ (∀ v', l ↦s v' -∗ (mkloc (loc_chunk l) 0) ↦s∗ (<[Z.to_nat (loc_idx l) := v']> vs)).
Proof.
  iIntros (Hsome) "Hs".
  iPoseProof (source_array_access _ (Z.to_nat (loc_idx l)) with "Hs") as "[Hl_s Hclose_s]".
  { apply list_lookup_alt. split; last reflexivity. lia. }
  rewrite mkloc_add. assert (Z.of_nat (Z.to_nat (loc_idx l))= loc_idx l) as -> by lia. rewrite loc_eta.
  iFrame.
Qed.

Lemma target_array_access' vs l :
  (0 ≤ loc_idx l < length vs)%Z →
  (mkloc (loc_chunk l) 0) ↦t∗ vs -∗
  l ↦t (vs !!! Z.to_nat (loc_idx l)) ∗ (∀ v', l ↦t v' -∗ (mkloc (loc_chunk l) 0) ↦t∗ (<[Z.to_nat (loc_idx l) := v']> vs)).
Proof.
  iIntros (Hsome) "Hs".
  iPoseProof (target_array_access _ (Z.to_nat (loc_idx l)) with "Hs") as "[Hl_s Hclose_s]".
  { apply list_lookup_alt. split; last reflexivity. lia. }
  rewrite mkloc_add. assert (Z.of_nat (Z.to_nat (loc_idx l))= loc_idx l) as -> by lia. rewrite loc_eta.
  iFrame.
Qed.

(** Alloc for source *)
Lemma alloc_source_ne l1 l2 n1 n2 : l1 ==>s n1 -∗ l2 ==>s n2 -∗ ⌜loc_chunk l1 ≠ loc_chunk l2⌝.
Proof. iIntros "Hn1 Hn2". iApply (ghost_map_elem_ne with "Hn1 Hn2"). Qed.

Lemma alloc_source_offset l n i : l ==>s n -∗ (l +ₗ i) ==>s n.
Proof. done. Qed.

Lemma alloc_source_lt l n σ : alloc_size_interp sheapG_allocN_source (σ.(heap)) -∗ l ==>s n -∗ ⌜0 < n⌝.
Proof.
  iIntros "Hinterp Hn".
  iDestruct "Hinterp" as (M) "(Hauth  & %Hs & _)".
  iPoseProof (ghost_map_lookup with "Hauth Hn") as "%Ha".
  iPureIntro. by eapply Hs.
Qed.

Lemma alloc_source_dealloc l n : l ==>s n -∗ †s l -∗ False.
Proof. iIntros "Hn1 Hn2". iPoseProof (ghost_map_elem_agree with "Hn1 Hn2") as "%Ha". iPureIntro; congruence. Qed.

(* We can learn that l's index must be 0, if it points to the full allocation. *)
Lemma alloc_source_seq_start n vs l σ :
  n = length vs →
  alloc_size_interp sheapG_allocN_source (σ.(heap)) -∗
  gen_heap_interp (hG := gen_heap_inG_source) σ.(heap) -∗
  l ==>s n -∗
  l ↦s∗ vs -∗
  ⌜loc_idx l = 0⌝.
Proof.
  iIntros (->) "Ha Hσ Halloc Hl".
  iPoseProof (alloc_size_lookup_alloc with "Halloc Ha") as "%Hs".
  iAssert (∀ i, ⌜(0 ≤ i < length vs)%Z⌝ → ⌜∃ w, heap σ !! (l +ₗ i) = Some (Some w)⌝)%I with "[Hσ Hl]" as "Hhea".
  { iIntros (i) "%Hrange".
    iPoseProof (source_array_access _ (Z.to_nat i) with "Hl") as "[Hs _]".
    { apply list_lookup_alt; split; [lia | reflexivity]. }
    iDestruct (gen_heap_valid with "Hσ Hs") as %?. iPureIntro.
    replace (Z.of_nat (Z.to_nat i)) with i in H by lia. eauto.
  }
  destruct Hs as [Hs ?].
  destruct (decide (loc_idx l < 0)%Z) as [Hlt | Hnlt].
  { iPoseProof ("Hhea" $! 0 with "[]") as "%Heh"; first by iPureIntro; lia.
    exfalso. destruct l; cbn in*. apply Hs in Heh. cbn in Heh. lia.
  }
  destruct (decide (loc_idx l > 0)%Z) as [Hgt | Hngt]; last by iPureIntro; lia.
  iPoseProof ("Hhea" $! (pred (length vs)) with "[]") as "%Heh"; first by iPureIntro; lia.
  exfalso. destruct l; cbn in*. apply Hs in Heh. cbn in Heh. lia.
Qed.


(** Alloc for target *)
Lemma alloc_target_ne l1 l2 n1 n2 : l1 ==>t n1 -∗ l2 ==>t n2 -∗ ⌜loc_chunk l1 ≠ loc_chunk l2⌝.
Proof. iIntros "Hn1 Hn2". iApply (ghost_map_elem_ne with "Hn1 Hn2"). Qed.

Lemma alloc_target_offset l n i : l ==>t n -∗ (l +ₗ i) ==>t n.
Proof. done. Qed.

Lemma alloc_target_lt l n σ : alloc_size_interp sheapG_allocN_target (σ.(heap)) -∗ l ==>t n -∗ ⌜0 < n⌝.
Proof.
  iIntros "Hinterp Hn".
  iDestruct "Hinterp" as (M) "(Hauth  & %Hs & _)".
  iPoseProof (ghost_map_lookup with "Hauth Hn") as "%Ha".
  iPureIntro. by eapply Hs.
Qed.

Lemma alloc_target_dealloc l n : l ==>t n -∗ †t l -∗ False.
Proof. iIntros "Hn1 Hn2". iPoseProof (ghost_map_elem_agree with "Hn1 Hn2") as "%Ha". iPureIntro; congruence. Qed.

Lemma alloc_target_seq_start n vs l σ :
  n = length vs →
  alloc_size_interp sheapG_allocN_target σ.(heap) -∗
  gen_heap_interp (hG := gen_heap_inG_target) σ.(heap) -∗
  l ==>t n -∗
  l ↦t∗ vs -∗
  ⌜loc_idx l = 0⌝.
Proof.
  iIntros (->) "Ha Hσ Halloc Hl".
  iPoseProof (alloc_size_lookup_alloc with "Halloc Ha") as "%Hs".
  iAssert (∀ i, ⌜(0 ≤ i < length vs)%Z⌝ → ⌜∃ w, heap σ !! (l +ₗ i) = Some (Some w)⌝)%I with "[Hσ Hl]" as "Hhea".
  { iIntros (i) "%Hrange".
    iPoseProof (target_array_access _ (Z.to_nat i) with "Hl") as "[Hs _]".
    { apply list_lookup_alt; split; [lia | reflexivity]. }
    iDestruct (gen_heap_valid with "Hσ Hs") as %?. iPureIntro.
    replace (Z.of_nat (Z.to_nat i)) with i in H by lia. eauto.
  }
  destruct Hs as [Hs ?].
  destruct (decide (loc_idx l < 0)%Z) as [Hlt | Hnlt].
  { iPoseProof ("Hhea" $! 0 with "[]") as "%Heh"; first by iPureIntro; lia.
    exfalso. destruct l; cbn in*. apply Hs in Heh. cbn in Heh. lia.
  }
  destruct (decide (loc_idx l > 0)%Z) as [Hgt | Hngt]; last by iPureIntro; lia.
  iPoseProof ("Hhea" $! (pred (length vs)) with "[]") as "%Heh"; first by iPureIntro; lia.
  exfalso. destruct l; cbn in*. apply Hs in Heh. cbn in Heh. lia.
Qed.



(** Program for target *)
Lemma hasfun_target_agree f K_t1 K_t2 : f @t K_t1 -∗ f @t K_t2 -∗ ⌜K_t1 = K_t2⌝.
Proof. apply hasfun_agree. Qed.

(** Program for source *)
Lemma hasfun_source_agree f K_s1 K_s2 : f @s K_s1 -∗ f @s K_s2 -∗ ⌜K_s1 = K_s2⌝.
Proof. apply hasfun_agree. Qed.


(** operational heap lemmas *)
Lemma heap_array_to_seq_mapsto l v (n : nat) γh γm (hG : gen_heapPreNameG loc (option (lock_state * val)) Σ γh γm) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_sim_heap.mapsto (hG:=hG) l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, gen_sim_heap.mapsto (hG:=hG) (l +ₗ (i : nat)) (DfracOwn 1) (Some (RSt 0, v)).
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma target_red_allocN_seq n v Ψ :
  (0 < n)%Z →
  (∀ l, ([∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦t v) -∗
    l ==>t (Z.to_nat n) -∗ target_red (of_val #l) Ψ) -∗
  target_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Ψ.
Proof.
  iIntros (Hn) "Hloc". iApply target_red_lift_head_step.
  iIntros (P_s σ_s P_t σ_t) "(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv)". iModIntro.
  iSplitR. { eauto using alloc_fresh with head_step. }
  iIntros (e_t' efs_t σ_t') "%"; inv_head_step.
  set (l := mkloc b 0).
  iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hσ_t")
    as "(Hσ_t & Hl & _)".
  { apply heap_array_map_disjoint. rewrite replicate_length Z2Nat.id; rewrite /loc_add; auto with lia.  }
  iPoseProof (heap_array_to_seq_mapsto with "Hl") as "Hmap".
  iFrame.
  iMod (alloc_size_allocN _ b (σ_t.(heap)) (replicate (Z.to_nat n) v) with "Ha_t") as "(Ha_t & Hn)";
    [rewrite replicate_length; lia | done | ].
  iModIntro. iFrame. iSplitR; first done.
  rewrite replicate_length. iApply ("Hloc" with "Hmap Hn").
Qed.

Lemma source_red_allocN_seq n v Ψ :
  (0 < n)%Z →
  (∀ l, ([∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦s v) -∗
  l ==>s (Z.to_nat n) -∗ source_red (of_val #l) Ψ) -∗
  source_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Ψ.
Proof.
  iIntros (Hn) "Hloc". iApply source_red_lift_head_step.
  iIntros (P_s σ_s P_t σ_t) "[(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv) _]".
  assert (head_reducible P_s (AllocN #n v) σ_s) as (e_s' & σ_s' & efs & Hred).
  { eauto using alloc_fresh with lia head_step. }
  inv_head_step. (set l := mkloc b 0).
  iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hσ_s")
    as "(Hσ_s & Hl & Hm)".
  { apply heap_array_map_disjoint. rewrite replicate_length Z2Nat.id /loc_add; auto with lia. }
  iModIntro. iExists #l, (state_init_heap l n v σ_s).
  iSplitR. { eauto with lia head_step. }
  iFrame.
  iMod (alloc_size_allocN _ b (σ_s.(heap)) (replicate (Z.to_nat n) v) with "Ha_s") as "(Ha_s & Hn)";
    [rewrite replicate_length; lia | done | ].
  iModIntro. iFrame. rewrite replicate_length.
  iApply ("Hloc" with "[Hl] [Hn]"); last done. iApply (heap_array_to_seq_mapsto with "Hl").
Qed.

Lemma target_red_alloc v Ψ :
  (∀ l, l ↦t v -∗ l ==>t 1 -∗ target_red (of_val #l) Ψ) -∗
  target_red (Alloc (Val v)) Ψ.
Proof.
  iIntros "Ht". iApply (target_red_allocN_seq); first lia.
  iIntros (l) "[Hl _]". iApply "Ht". by rewrite loc_add_0.
Qed.

Lemma source_red_alloc v Ψ :
  (∀ l, l ↦s v -∗ l ==>s 1 -∗ source_red (of_val #l) Ψ) -∗
  source_red (Alloc (Val v)) Ψ.
Proof.
  iIntros "Ht". iApply (source_red_allocN_seq); first lia.
  iIntros (l) "[Hl _]". iApply "Ht". by rewrite loc_add_0.
Qed.

Lemma heap_array_st_validN {γh γm} {hG : gen_heapPreNameG loc (option (lock_state * val)) Σ γh γm} σ vs sts n l :
  length vs = Z.to_nat n →
  gen_heap_interp (hG := hG) σ.(heap) -∗
  array_st (hG := hG) l (DfracOwn 1) vs sts -∗
  ⌜∀ i, (0 ≤ i < n)%Z → σ.(heap) !! (l +ₗ i) = Some (Some (sts !!! (Z.to_nat i), vs !!! (Z.to_nat i)))⌝.
Proof.
  iIntros (Hn) "Hσ Hl".
  iPoseProof (array_st_length_inv with "Hl") as "%Hlen".
  iInduction vs as [] "IH" forall (n l sts Hlen Hn); cbn in Hn.
  - iPureIntro. intros i ?. lia.
  - destruct sts as [ | b sts]; [cbn in Hlen; lia |].
    rewrite /array_st big_sepL2_cons loc_add_0. iDestruct "Hl" as "[Hl0 Hlr]".
    iDestruct (gen_heap_valid with "Hσ Hl0") as "%Hs".
    iPoseProof ("IH" $! (Z.pred n) (l +ₗ 1) sts with "[] [] Hσ [Hlr]") as "%IH".
    + iPureIntro; cbn in Hlen. lia.
    + iPureIntro. lia.
    + iApply (big_sepL2_mono with "Hlr").
      intros k v st Hv Hst; simpl. rewrite loc_add_assoc. replace (Z.of_nat (S k)) with (1 + k)%Z; [done | lia].
    + iPureIntro. intros i Hi. destruct (decide (i = 0)) as [-> | ].
      { rewrite loc_add_0. eauto. }
      specialize (IH (Z.pred i) ltac:(lia)) as IH.
      rewrite !lookup_total_cons_ne_0; [ | lia | lia].
      replace (Nat.pred (Z.to_nat i)) with (Z.to_nat (Z.pred i)) by lia.
      rewrite -IH. rewrite loc_add_assoc. by replace (1 + Z.pred i)%Z with i%Z by lia.
Qed.

Lemma heap_array_validN {γh γm} {hG : gen_heapPreNameG loc (option (lock_state * val)) Σ γh γm} σ vs n l :
  length vs = Z.to_nat n →
  gen_heap_interp (hG := hG) σ.(heap) -∗
  array (hG := hG) l (DfracOwn 1) vs -∗
  ⌜∀ i, (0 ≤ i < n)%Z → σ.(heap) !! (l +ₗ i) = Some (Some (RSt 0, vs !!! (Z.to_nat i)))⌝.
Proof.
  iIntros (Hn) "Hσ Hl".
  iPoseProof (heap_array_st_validN with "Hσ Hl") as "%Ha"; first done.
  iPureIntro. intros i Hi. rewrite (Ha i Hi).
  rewrite lookup_total_replicate_2; [done | lia].
Qed.

Lemma heap_array_st_freeN {γh γm} {hG : gen_heapPreNameG loc (option (lock_state * val)) Σ γh γm} σ vs sts n l :
  length vs = n →
  gen_heap_interp (hG:=hG) σ.(heap) -∗
  array_st (hG := hG) l (DfracOwn 1) vs sts ==∗
  gen_heap_interp (hG:=hG) (free_mem l n σ.(heap)).
Proof.
  iIntros (<-) "Hσ Hl". iPoseProof (array_st_length_inv with "Hl") as "%Hl".
  iInduction vs as [] "IH" forall (l σ sts Hl); first done.
  destruct sts as [ | st sts]; [ cbn in Hl; lia | ].
  rewrite /array_st big_sepL2_cons loc_add_0. iDestruct "Hl" as "[Hl0 Hlr]".
  iMod (gen_heap_update _ _ _ None with "Hσ Hl0") as "[Hσ _]".
  iMod ("IH" $! (l +ₗ 1) (state_upd_heap <[l:=None]> σ) sts with "[] Hσ [Hlr]") as "IH'".
  - iPureIntro; cbn in Hl; lia.
  - iApply (big_sepL2_mono with "Hlr").
    intros k v st' Ha Hst'; simpl. rewrite loc_add_assoc. replace (Z.of_nat (S k)) with (1 + k)%Z; [done | lia].
  - iModIntro. cbn. rewrite (upd_free_mem σ l _ 1); last lia. iApply "IH'".
Qed.

Lemma target_red_freeN vs l n Ψ :
  length vs = (Z.to_nat n) →
  l ↦t∗ vs -∗
  l ==>t (Z.to_nat n) -∗
  target_red (of_val #()) Ψ -∗
  target_red (FreeN (Val $ LitV $ LitInt n) (Val $ LitV (LitLoc l))) Ψ.
Proof.
  iIntros (Hn) "Hl Hn Hsim". iApply target_red_lift_head_step.
  iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv)".
  iPoseProof (alloc_size_lookup_alloc with "Hn Ha_t") as "%Halloc".
  iPoseProof (alloc_target_lt with "Ha_t Hn") as "%Hlt".
  iPoseProof (alloc_target_seq_start with "Ha_t Hσ_t Hn Hl") as "%Hidx_lt"; first done.
  iPoseProof (heap_array_validN with "Hσ_t Hl") as "%Hv"; first done.
  iModIntro.
  assert (∀ i, (0 ≤ i < n)%Z → ∃ v, heap σ_t !! (l +ₗ i) = Some (Some (RSt 0, v))) as Hi1 by eauto.
  assert (∀ i, (∃ v st, heap σ_t !! (l +ₗ i) = Some (Some (st, v))) → (0 ≤ i < n)%Z) as Hi2.
  { intros i (v &st & Hv0). replace (Z.of_nat (Z.to_nat n)) with n in Halloc by lia. apply Halloc.
      exists (st, v). destruct l; rewrite /loc_add Hidx_lt in Hv0; cbn in *.
      replace (0%nat + i)%Z with i in Hv0 by lia. apply Hv0.
  }
  iSplitR; first by eauto with lia head_step.
  iIntros (e_t' efs σ_t') "%"; inv_head_step.

  iMod (alloc_size_free with "Hn Ha_t") as "[Ha_t Hn]". iFrame.
  iMod (heap_array_st_freeN with "Hσ_t Hl") as "$"; first done.
  iModIntro. iSplitR; first done.
  assert (mkloc (loc_chunk l) 0 = l) as ->.
  { destruct l; cbn in *; rewrite Hidx_lt. replace 0%Z with (Z.of_nat 0); done. }
  done.
Qed.

Lemma target_red_free v l Ψ :
  l ↦t v -∗
  l ==>t 1 -∗
  target_red (of_val #()) Ψ -∗
  target_red (FreeN (Val $ LitV $ LitInt 1) (Val $ LitV (LitLoc l))) Ψ.
Proof.
  iIntros "Hl Hn". replace (1) with (Z.to_nat 1) by lia.
  iApply (target_red_freeN [v] with "[Hl] Hn"); first done.
  cbn. rewrite loc_add_0; eauto.
Qed.

Lemma source_red_freeN vs l n Ψ :
  length vs = (Z.to_nat n) →
  l ↦s∗ vs -∗
  l ==>s (Z.to_nat n) -∗
  source_red (of_val #()) Ψ -∗
  source_red (FreeN (Val $ LitV $ LitInt n) (Val $ LitV (LitLoc l))) Ψ.
Proof.
  iIntros (Hn) "Hl Hn Hsim". iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv) _]".
  iPoseProof (alloc_size_lookup_alloc with "Hn Ha_s") as "%Halloc".
  iPoseProof (alloc_source_lt with "Ha_s Hn") as "%Hlt".
  iPoseProof (alloc_source_seq_start with "Ha_s Hσ_s Hn Hl") as "%Hidx_lt"; first done.
  iPoseProof (heap_array_validN with "Hσ_s Hl") as "%Hv"; first done.
  iModIntro.
  assert (∀ i, (0 ≤ i < n)%Z → ∃ v, heap σ_s !! (l +ₗ i) = Some (Some (RSt 0, v))) as Hi1 by eauto.
  assert (∀ i, (∃ v st, heap σ_s !! (l +ₗ i) = Some (Some (st, v))) → (0 ≤ i < n)%Z) as Hi2.
  { intros i (v &st & Hv0). replace (Z.of_nat (Z.to_nat n)) with n in Halloc by lia. apply Halloc.
      exists (st, v). destruct l; rewrite /loc_add Hidx_lt in Hv0; cbn in *.
      replace (0%nat + i)%Z with i in Hv0 by lia. apply Hv0.
  }
  iExists (Val #()), (state_upd_heap (free_mem l (Z.to_nat n)) σ_s).
  iSplitR; first eauto with lia head_step.
  { iPureIntro. econstructor; eauto with lia. }

  iMod (alloc_size_free with "Hn Ha_s") as "[Ha_s Hn]". iFrame.
  iMod (heap_array_st_freeN with "Hσ_s Hl") as "$"; first done.
  iModIntro.
  assert (mkloc (loc_chunk l) 0 = l) as ->.
  { destruct l; cbn in *; rewrite Hidx_lt. replace 0%Z with (Z.of_nat 0); done. }
  done.
Qed.

Lemma source_red_free v l Ψ :
  l ↦s v -∗
  l ==>s 1 -∗
  source_red (of_val #()) Ψ -∗
  source_red (FreeN (Val $ LitV $ LitInt 1) (Val $ LitV (LitLoc l))) Ψ.
Proof.
  iIntros "Hl Hn". replace (1) with (Z.to_nat 1) by lia.
  iApply (source_red_freeN [v] with "[Hl] Hn"); first done.
  cbn. rewrite loc_add_0; eauto.
Qed.

Lemma target_red_load_sc l dq v Ψ :
  l ↦t{dq} v -∗
  (l ↦t{dq} v -∗ target_red (of_val v) Ψ) -∗
  target_red (Load ScOrd (Val $ LitV $ LitLoc l)) Ψ.
Proof.
  iIntros "Hl Ht". iApply target_red_lift_head_step.
  iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iDestruct (gen_heap_valid with "Hσ_t Hl") as %?. iModIntro.
  iSplit; first by eauto with head_step.
  iIntros (??? Hstep); inv_head_step.
  iModIntro. iFrame. iSplit;[done|]. by iApply "Ht".
Qed.

(** FIXME: this is not the theorem we would like as the lock_state does currently not interact well with fractions *)
Lemma target_red_load_na l v Ψ :
  l ↦t v -∗
  (l ↦t v -∗ target_red (of_val v) Ψ) -∗
  target_red (Load Na1Ord (Val $ LitV $ LitLoc l)) Ψ.
Proof.
  iIntros "Hl Ht". iApply target_red_lift_head_step.
  iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv)".
  iDestruct (gen_heap_valid with "Hσ_t Hl") as %?. iModIntro.
  iSplit; first by eauto with head_step.
  iIntros (??? Hstep); inv_head_step.
  iMod (gen_heap_update with "Hσ_t Hl") as "[$ Hl]".
  iDestruct (alloc_size_update with "Ha_t") as "$"; first done.
  iModIntro. iFrame. iSplitR; first done.

  iApply target_red_lift_head_step.
  iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv)".
  iDestruct (gen_heap_valid with "Hσ_t Hl") as %?. iModIntro.
  iSplit; first by eauto with head_step.
  iIntros (??? Hstep); inv_head_step.
  iMod (gen_heap_update with "Hσ_t Hl") as "[$ Hl]".
  iDestruct (alloc_size_update with "Ha_t") as "$"; first done.
  iModIntro. iFrame. iSplitR; first done. by iApply "Ht".
Qed.

Lemma source_red_load_sc l dq v Ψ :
  l ↦s{dq} v -∗
  (l ↦s{dq} v -∗ source_red (of_val v) Ψ) -∗
  source_red (Load ScOrd (Val $ LitV $ LitLoc l)) Ψ.
Proof.
  iIntros "Hl Ht". iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _]".
  iDestruct (gen_heap_valid with "Hσ_s Hl") as %?.
  assert (∃ e_s' σ_s', head_step P_s (Load ScOrd #l) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iModIntro; iExists e_s', σ_s'. iSplit; first by eauto. inv_head_step.
  iModIntro. iFrame. by iApply "Ht".
Qed.

(** FIXME: this is not the theorem we would like as the lock_state does currently not interact well with fractions *)
Lemma source_red_load_na l v Ψ :
  l ↦s v -∗
  (l ↦s v -∗ source_red (of_val v) Ψ) -∗
  source_red (Load Na1Ord (Val $ LitV $ LitLoc l)) Ψ.
Proof.
  iIntros "Hl Ht". iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv) _]".
  iDestruct (gen_heap_valid with "Hσ_s Hl") as %?.
  assert (∃ e_s' σ_s', head_step P_s (Load Na1Ord #l) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iModIntro; iExists e_s', σ_s'. iSplit; first by eauto. inv_head_step.
  iMod (gen_heap_update with "Hσ_s Hl") as "[$ Hl]".
  iDestruct (alloc_size_update with "Ha_s") as "$"; first done.
  iModIntro. iFrame.

  iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv) _]".
  iDestruct (gen_heap_valid with "Hσ_s Hl") as %?.
  assert (∃ e_s' σ_s', head_step P_s0 (Load Na2Ord #l) σ_s0 e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with lia head_step. }
  iModIntro; iExists e_s', σ_s'. iSplit; first by eauto. inv_head_step.
  iMod (gen_heap_update with "Hσ_s Hl") as "[$ Hl]".
  iDestruct (alloc_size_update with "Ha_s") as "$"; first done.
  iModIntro. iFrame.
  by iApply "Ht".
Qed.

Lemma target_red_store_sc l v v' Ψ :
  l ↦t v' -∗
  (l ↦t v -∗ target_red (of_val #()) Ψ) -∗
  target_red (Store ScOrd (Val $ LitV (LitLoc l)) (Val v)) Ψ.
Proof.
  iIntros "Hl Hsim". iApply target_red_lift_head_step.
  iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv) !>".
  iDestruct (gen_heap_valid with "Hσ_t Hl") as %?.
  iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%"; inv_head_step.
  iMod (gen_heap_update with "Hσ_t Hl") as "[$ Hl]".
  iFrame. iDestruct (alloc_size_update with "Ha_t") as "$"; first done.
  iModIntro. iSplitR; first done. by iApply "Hsim".
Qed.

Lemma target_red_store_na l v v' Ψ :
  l ↦t v' -∗
  (l ↦t v -∗ target_red (of_val #()) Ψ) -∗
  target_red (Store Na1Ord (Val $ LitV (LitLoc l)) (Val v)) Ψ.
Proof.
  iIntros "Hl Hsim". iApply target_red_lift_head_step.
  iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv) !>".
  iDestruct (gen_heap_valid with "Hσ_t Hl") as %?.
  iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%"; inv_head_step.
  iMod (gen_heap_update with "Hσ_t Hl") as "[$ Hl]".
  iFrame. iDestruct (alloc_size_update with "Ha_t") as "$"; first done.
  iModIntro. iSplitR; first done.

  iApply target_red_lift_head_step.
  iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv) !>".
  iDestruct (gen_heap_valid with "Hσ_t Hl") as %?.
  iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%"; inv_head_step.
  iMod (gen_heap_update with "Hσ_t Hl") as "[$ Hl]".
  iFrame. iDestruct (alloc_size_update with "Ha_t") as "$"; first done.
  iModIntro. iSplitR; first done. by iApply "Hsim".
Qed.

Lemma source_red_store_sc l v v' Ψ :
  l ↦s v' -∗
  (l ↦s v -∗ source_red (of_val #()) Ψ) -∗
  source_red (Store ScOrd (Val $ LitV (LitLoc l)) (Val v)) Ψ.
Proof.
  iIntros "Hl Hsim". iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv) _] !>".
  iDestruct (gen_heap_valid with "Hσ_s Hl") as %?.
  assert (∃ e_s' σ_s', head_step P_s (Store ScOrd (Val $ LitV (LitLoc l)) (Val v)) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done. inv_head_step.
  iMod (gen_heap_update with "Hσ_s Hl") as "[$ Hl]".
  iFrame. iDestruct (alloc_size_update with "Ha_s") as "$"; first done.
  iModIntro. by iApply "Hsim".
Qed.

Lemma source_red_store_na l v v' Ψ :
  l ↦s v' -∗
  (l ↦s v -∗ source_red (of_val #()) Ψ) -∗
  source_red (Store Na1Ord (Val $ LitV (LitLoc l)) (Val v)) Ψ.
Proof.
  iIntros "Hl Hsim". iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv) _] !>".
  iDestruct (gen_heap_valid with "Hσ_s Hl") as %?.
  assert (∃ e_s' σ_s', head_step P_s (Store Na1Ord (Val $ LitV (LitLoc l)) (Val v)) σ_s e_s' σ_s' [])
    as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done. inv_head_step.
  iMod (gen_heap_update with "Hσ_s Hl") as "[$ Hl]".
  iFrame. iDestruct (alloc_size_update with "Ha_s") as "$"; first done.
  iModIntro.

  iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Ha_t & Ha_s & Hinv) _] !>".
  iDestruct (gen_heap_valid with "Hσ_s Hl") as %?.
  assert (∃ e_s' σ_s', head_step P_s0 (Store Na2Ord (Val $ LitV (LitLoc l)) (Val v)) σ_s0 e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done. inv_head_step.
  iMod (gen_heap_update with "Hσ_s Hl") as "[$ Hl]".
  iFrame. iDestruct (alloc_size_update with "Ha_s") as "$"; first done.
  iModIntro. by iApply "Hsim".
Qed.

(** operational lemmas for calls *)
Lemma target_red_call f K_t v Ψ :
  f @t K_t -∗
  target_red (fill K_t (Val v)) Ψ -∗
  target_red (Call (Val $ LitV $ LitFn f) (Val v)) Ψ.
Proof.
  iIntros "Hf Hred". iApply target_red_lift_head_step.
  iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & ?) !>".
  iDestruct (gen_prog_valid with "HP_t Hf") as %?.
  iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%"; inv_head_step.
  iModIntro. by iFrame.
Qed.

Lemma source_red_call f K_s v Ψ :
  f @s K_s -∗
  source_red (fill K_s (Val v)) Ψ -∗
  source_red (Call (Val $ LitV $ LitFn f) (Val v)) Ψ.
Proof.
  iIntros "Hf Hred". iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & ?) _] !>".
  iDestruct (gen_prog_valid with "HP_s Hf") as %?.
  assert (∃ e_s' σ_s', head_step P_s (Call (Val $ LitV $ LitFn f) (Val v)) σ_s e_s' σ_s' [])
    as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done. inv_head_step.
  iModIntro. iFrame.
Qed.

(** Call lemmas for sim *)
Lemma sim_call e_t e_s v_t v_s f :
  to_val e_t = Some v_t →
  to_val e_s = Some v_s →
  ⊢ Ω v_t v_s -∗ Call (## f) e_t ⪯{Ω} Call (## f) e_s {{ Ω }}.
Proof.
  intros <-%of_to_val <-%of_to_val.
  (* FIXME use lifting lemma for this *)
  iIntros "H". rewrite /sim /sim_stutter /sim_def sim_expr_unfold. iIntros (????) "[H1 H2]". iModIntro.
  iRight; iRight. iExists f, empty_ectx, v_t, empty_ectx, v_s, σ_s. cbn. iFrame.
  iSplitR; first done. iSplitR. { iPureIntro. constructor. }
  iIntros (v_t' v_s' ) "H". iApply sim_value. iApply "H".
Qed.

(** fork *)
Lemma sim_fork e_t e_s Ψ :
  #() ⪯ #() [{ Ψ }] -∗
  e_t ⪯ e_s [{ lift_post Ω }] -∗
  Fork e_t ⪯ Fork e_s [{ Ψ }].
Proof.
  iIntros "Hval Hsim". iApply sim_lift_head_step_both.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) %Hnstuck] !>".
  iSplitR. { eauto with head_step. }
  iIntros (e_t' efs_t σ_t') "%"; inv_head_step.
  iModIntro. iExists _, _, _. iSplitR. { eauto with head_step. }
  simpl. iFrame.
Qed.

(** Coinduction support *)
Lemma sim_while_while b_t b_s c_t c_s inv Ψ :
  inv -∗
  □ (inv -∗
    (if: c_t then b_t ;; while: c_t do b_t od else #())%E ⪯{Ω}
    (if: c_s then b_s ;; while: c_s do b_s od else #())%E
      [{ λ e_t e_s, Ψ e_t e_s ∨ (⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗ inv) }]) -∗
  (while: c_t do b_t od ⪯{Ω} while: c_s do b_s od [{ Ψ }])%E.
Proof.
  iIntros "Hinv_init #Hstep".
  iApply (sim_lift_head_coind _ (λ e_t e_s, ⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗ inv)%I with "[] [Hinv_init]"); first last.
  { iFrame. eauto. }
  iModIntro. iIntros (?? ?? ??) "(-> & -> & Hinv) (Hstate & Hnreach)".
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%Hhead"; inv_head_step.
  assert (∃ e_s' σ_s', head_step P_s (while: c_s do b_s od ) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iModIntro. iExists e_s', σ_s'. inv_head_step. iFrame. iSplit;[done|].
  iSplitR; first by eauto with head_step. iApply "Hstep". iFrame.
Qed.


Lemma sim_while_rec b_t c_t v_s (K_s : ectx) (inv : val → iProp Σ) Ψ rec_n :
  inv v_s -∗
  rec_n @s K_s -∗
  □ (∀ v_s', inv v_s' -∗
    (if: c_t then b_t ;; while: c_t do b_t od else #())%E ⪯{Ω} (fill K_s v_s')%E
    [{ λ e_t e_s , Ψ e_t e_s ∨ (∃ v_s', ⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = Call ##rec_n (Val v_s')⌝ ∗ inv v_s') }]) -∗
  (while: c_t do b_t od ⪯{Ω} Call ## rec_n v_s [{ Ψ }])%E.
Proof.
  iIntros "Hinv #Hrec #Hstep". iApply (sim_lift_head_coind _ (λ e_t e_s, (∃ v_s', ⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = Call ##rec_n (Val v_s')⌝ ∗ inv v_s')%I)); first last.
  { iExists v_s. eauto. }
  iModIntro. iIntros (?? ?? ??) "He (Hstate & Hnreach)". iDestruct "He" as (v_s') "(-> & -> & Hinv)".
  iSpecialize ("Hstep" with "Hinv").
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%Hhead"; inv_head_step.
  iModIntro. iExists (fill K_s v_s'), σ_s.

  iDestruct "Hstate" as "(? & HP_s & ? & ? &?)".
  iDestruct (gen_prog_valid with "HP_s Hrec") as %?.
  iFrame. by eauto with head_step.
Qed.

Lemma sim_rec_while b_s c_s v_t (K_t : ectx) (inv : val → iProp Σ) Ψ rec_n :
  inv v_t -∗
  rec_n @t K_t -∗
  □ (∀ v_t', inv v_t' -∗
    (fill K_t v_t')%E ⪯{Ω}  (if: c_s then b_s ;; while: c_s do b_s od else #())%E
    [{ λ e_t e_s , Ψ e_t e_s ∨ (∃ v_t', ⌜e_t = Call ##rec_n (Val v_t')⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗  inv v_t') }]) -∗
  ( Call ##rec_n v_t ⪯{Ω} while: c_s do b_s od [{ Ψ }])%E.
Proof.
  iIntros "Hinv #Hrec #Hstep". iApply (sim_lift_head_coind _ (λ e_t e_s, (∃ v_t', ⌜e_t = Call ##rec_n (Val v_t')⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗  inv v_t'))%I); first last.
  { iExists v_t. eauto. }
  iModIntro. iIntros (?? ?? ??) "He (Hstate & Hnreach)". iDestruct "He" as (v_s') "(-> & -> & Hinv)".
  iSpecialize ("Hstep" with "Hinv").

  iDestruct "Hstate" as "(HP_t & ? & ? & ? &?)".
  iDestruct (gen_prog_valid with "HP_t Hrec") as %?.
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%Hhead"; inv_head_step.
  iModIntro.
  assert (∃ e_s' σ_s', head_step P_s (while: c_s do b_s od ) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. inv_head_step. iFrame. iPureIntro. eauto with head_step.
Qed.

Lemma sim_rec_rec v_t v_s (K_t K_s : ectx) (inv : val → val → iProp Σ) Ψ rec_t rec_s :
  inv v_t v_s -∗
  rec_t @t K_t -∗
  rec_s @s K_s -∗
  □ (∀ v_t' v_s', inv v_t' v_s' -∗
    (fill K_t v_t')%E ⪯{Ω} (fill K_s v_s')%E
    [{ λ e_t e_s , Ψ e_t e_s ∨ (∃ v_t' v_s', ⌜e_t = Call ##rec_t (Val v_t')⌝ ∗ ⌜e_s = Call ##rec_s (Val v_s')⌝ ∗ inv v_t' v_s') }]) -∗
  ( Call ##rec_t v_t ⪯{Ω} Call ##rec_s v_s [{ Ψ }])%E.
Proof.
  iIntros "Hinv #Hrec_t #Hrec_s #Hstep".
  iApply (sim_lift_head_coind _ (λ e_t e_s, (∃ v_t' v_s', ⌜e_t = Call ##rec_t (Val v_t')⌝ ∗ ⌜e_s = Call ##rec_s (Val v_s')⌝ ∗ inv v_t' v_s'))%I); first last.
  { iExists v_t, v_s. eauto. }
  iModIntro. iIntros (?? ?? ??) "He (Hstate & Hnreach)". iDestruct "He" as (v_t' v_s') "(-> & -> & Hinv)".
  iSpecialize ("Hstep" with "Hinv").

  iDestruct "Hstate" as "(HP_t & HP_s & ? & ? &?)".
  iDestruct (gen_prog_valid with "HP_t Hrec_t") as %?.
  iDestruct (gen_prog_valid with "HP_s Hrec_s") as %?.
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%Hhead"; inv_head_step.
  iModIntro.
  assert (∃ e_s' σ_s', head_step P_s (Call ##rec_s v_s') σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. inv_head_step. iFrame. iPureIntro. eauto with head_step.
Qed.
End lifting.
