(** This file proves the basic laws of the SimpLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From simuliris.base_logic Require Export gen_sim_heap.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Export class_instances.
From simuliris.simplang Require Import tactics notation.
From iris.prelude Require Import options.


Class sheapG (Σ: gFunctors) := SHeapG {
  sheapG_gen_heapG :> gen_sim_heapG loc loc (option val) (option val) Σ;
}.

(* TODO: probably want to have ghost state for the programs *)
Global Instance sheapG_SimulLang `{!sheapG Σ} : SimulLang (iPropI Σ) simp_lang := {
  (*iris_invG := heapG_invG;*)
  state_interp P_t σ_t P_s σ_s :=
    (gen_heap_interp (hG := gen_heap_inG_target) σ_t.(heap) ∗
     gen_heap_interp (hG := gen_heap_inG_source) σ_s.(heap))%I;
}.

(** Since we use an [option val] instance of [gen_heap], we need to overwrite
the notations.  That also helps for scopes and coercions. *)
(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "l '↦t{' dq } v" := (mapsto (hG:=gen_heap_inG_target) (L:=loc) (V:=option val) l dq (Some v%V))
  (at level 20, format "l  ↦t{ dq }  v") : bi_scope.
Notation "l '↦t□' v" := (mapsto (hG:=gen_heap_inG_target) (L:=loc) (V:=option val) l DfracDiscarded (Some v%V))
  (at level 20, format "l  ↦t□  v") : bi_scope.
Notation "l '↦t{#' q } v" := (mapsto (hG:=gen_heap_inG_target) (L:=loc) (V:=option val) l (DfracOwn q) (Some v%V))
  (at level 20, format "l  ↦t{# q }  v") : bi_scope.
Notation "l '↦t' v" := (mapsto (hG:=gen_heap_inG_target) (L:=loc) (V:=option val) l (DfracOwn 1) (Some v%V))
  (at level 20, format "l  ↦t  v") : bi_scope.

Notation "l '↦s{' dq } v" := (mapsto (hG:=gen_heap_inG_source) (L:=loc) (V:=option val) l dq (Some v%V))
  (at level 20, format "l  ↦s{ dq }  v") : bi_scope.
Notation "l '↦s□' v" := (mapsto (hG:=gen_heap_inG_source) (L:=loc) (V:=option val) l DfracDiscarded (Some v%V))
  (at level 20, format "l  ↦s□  v") : bi_scope.
Notation "l '↦s{#' q } v" := (mapsto (hG:=gen_heap_inG_source) (L:=loc) (V:=option val) l (DfracOwn q) (Some v%V))
  (at level 20, format "l  ↦s{# q }  v") : bi_scope.
Notation "l '↦s' v" := (mapsto (hG:=gen_heap_inG_source) (L:=loc) (V:=option val) l (DfracOwn 1) (Some v%V))
  (at level 20, format "l  ↦s  v") : bi_scope.

Section lifting.
Context `{!sheapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → val → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types v v_s v_t : val.
Implicit Types l : loc.

Context (Ω : val → val → iProp Σ).
Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{Ω} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.


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

Lemma heap_array_to_seq_mapsto l v (n : nat) γh γm (hG : gen_heapPreNameG loc (option val) Σ γh γm) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_sim_heap.mapsto (hG:=hG) l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, gen_sim_heap.mapsto (hG:=hG) (l +ₗ (i : nat)) (DfracOwn 1) (Some v).
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

Lemma sim_allocN_target n v Φ e_s :
  (0 < n)%Z →
  (∀ l, [∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦t v -∗ of_val #l ⪯ e_s {{ Φ }}) -∗
  AllocN (Val $ LitV $ LitInt $ n) (Val v) ⪯ e_s {{ Φ }}.
Proof.
  iIntros (Hn) "Hloc".
  iApply sim_head_step_target. iIntros (P_t P_s σ_t σ_s) "[Hσ_t Hσ_s]". iModIntro.
  iSplitR. { iPureIntro. eauto with lia head_step. }
  iIntros (e_t' σ_t') "%"; inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hσ_t")
    as "(Hσ_t & Hl & Hm)".
  { apply heap_array_map_disjoint. rewrite replicate_length Z2Nat.id; auto with lia. }
  iPoseProof (heap_array_to_seq_mapsto with "Hl") as "Hmap".
  iModIntro. iFrame. iSpecialize ("Hloc" $! l).
  (* TODO: why does this fail? *)
  (*by iApply "Hloc". *)
Admitted.

Lemma sim_allocN_source n v Φ e_t :
  (0 < n)%Z →
  (∀ l, [∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦s v -∗ e_t ⪯ of_val #l  {{ Φ }}) -∗
  e_t ⪯ AllocN (Val $ LitV $ LitInt $ n) (Val v) {{ Φ }}.
Proof.
  iIntros (Hn) "Hloc".
  iApply sim_head_step_source. iIntros (P_t P_s σ_t σ_s) "[Hσ_t Hσ_s]".
  assert (head_reducible P_s (AllocN #n v) σ_s) as (e_s' & σ_s' & Hred).
  { eauto with lia head_step. }
  inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hσ_s")
    as "(Hσ_s & Hl & Hm)".
  { apply heap_array_map_disjoint. rewrite replicate_length Z2Nat.id; auto with lia. }
  iModIntro. iExists #l, (state_init_heap l n v σ_s).
  iSplitR. { eauto with lia head_step. }
  iFrame.
  iPoseProof (heap_array_to_seq_mapsto with "Hl") as "Hmap".
  iSpecialize ("Hloc" $! l).
  (* TODO: why does this fail? *)
  (*by iApply "Hloc". *)
Admitted.

Lemma sim_alloc_target v e_s Φ :
  (∀ l, l ↦t v -∗ of_val #l ⪯ e_s {{ Φ }}) -∗ Alloc (Val v) ⪯ e_s {{ Φ }}.
Proof.
  iIntros "H". iApply sim_allocN_target; first lia.
  iIntros (l). iSplitL; last done. by rewrite loc_add_0.
Qed.

Lemma sim_alloc_source v e_t Φ :
  (∀ l, l ↦s v -∗ e_t ⪯ of_val #l {{ Φ }}) -∗ e_t ⪯ Alloc (Val v) {{ Φ }}.
Proof.
  iIntros "H". iApply sim_allocN_source; first lia.
  iIntros (l). iSplitL; last done. by rewrite loc_add_0.
Qed.

Lemma sim_free_target v l e_s Φ :
  l ↦t v -∗ #() ⪯ e_s {{ Φ }} -∗ Free (Val $ LitV (LitLoc l)) ⪯ e_s {{ Φ }}.
Proof.
  iIntros "Hl Hsim". iApply sim_head_step_target. iIntros (????) "[Hσ_t Hσ_s]".
  iDestruct (gen_heap_valid with "Hσ_t Hl") as %?.
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' σ_t') "%"; inv_head_step.
  iMod (gen_heap_update with "Hσ_t Hl") as "[$ Hl]".
  iModIntro. iFrame.
Qed.

Lemma sim_free_source v l e_t Φ :
  l ↦s v -∗ e_t ⪯ #() {{ Φ }} -∗ e_t ⪯ Free (Val $ LitV (LitLoc l)) {{ Φ }}.
Proof.
  iIntros "Hl Hsim". iApply sim_head_step_source. iIntros (????) "[Hσ_t Hσ_s]".
  iDestruct (gen_heap_valid with "Hσ_s Hl") as %?.
  iModIntro.
  assert (head_reducible P_s (Free #l) σ_s) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done.
  inv_head_step. iMod (gen_heap_update with "Hσ_s Hl") as "[$ Hl]".
  iModIntro. iFrame.
Qed.

Lemma sim_store_target l v v' e_s Φ :
  l ↦t v' -∗
  (l ↦t v -∗ #() ⪯ e_s {{ Φ }}) -∗
  Store (Val $ LitV (LitLoc l)) (Val v) ⪯ e_s {{ Φ }}.
Proof.
  iIntros "Hl Hsim". iApply sim_head_step_target. iIntros (????) "[Hσ_t Hσ_s] !>".
  iDestruct (gen_heap_valid with "Hσ_t Hl") as %?.
  iSplitR; first by eauto with head_step.
  iIntros (e_t' σ_t') "%"; inv_head_step.
  iMod (gen_heap_update with "Hσ_t Hl") as "[$ Hl]".
  iModIntro. iFrame. by iApply "Hsim".
Qed.

Lemma sim_store_source l v v' e_t Φ :
  l ↦s v' -∗
  (l ↦s v -∗ e_t ⪯ #() {{ Φ }}) -∗
  e_t ⪯ Store (Val $ LitV (LitLoc l)) (Val v) {{ Φ }}.
Proof.
  iIntros "Hl Hsim". iApply sim_head_step_source. iIntros (????) "[Hσ_t Hσ_s] !>".
  iDestruct (gen_heap_valid with "Hσ_s Hl") as %?.
  assert (head_reducible P_s (Store (Val $ LitV (LitLoc l)) (Val v)) σ_s) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done. inv_head_step.
  iMod (gen_heap_update with "Hσ_s Hl") as "[$ Hl]".
  iModIntro. iFrame. by iApply "Hsim".
Qed.

End lifting.
