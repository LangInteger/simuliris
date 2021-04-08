(** This file proves the basic laws of the SimpLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Export tactics.
From iris.bi.lib Require Import fractional.
From simuliris.base_logic Require Export gen_sim_heap gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.simplang Require Export class_instances tactics notation.
From iris.prelude Require Import options.

Class sheapG (Σ: gFunctors) := SHeapG {
  sheapG_gen_heapG :> gen_sim_heapG loc loc (option val) (option val) Σ;
  sheapG_gen_progG :> gen_sim_progG string ectx ectx Σ;
}.

(** This class is instantiated per proof (usually at the beginning of the file).
   It states additional components of the state interpretation, i.e.,
   invariants on the relation of source and target programs and states.
 *)
Class sheapInv (Σ : gFunctors) := SHeapRel {
  sheap_inv : iProp Σ;
}.

Global Instance sheapG_SimulLang `{!sheapG Σ} `{!sheapInv Σ} : SimulLang (iPropI Σ) simp_lang := {
  state_interp P_t σ_t P_s σ_s :=
    (gen_prog_interp (hG := gen_prog_inG_target) P_t ∗
     gen_prog_interp (hG := gen_prog_inG_source) P_s ∗
     gen_heap_interp (hG := gen_heap_inG_target) σ_t.(heap) ∗
     gen_heap_interp (hG := gen_heap_inG_source) σ_s.(heap) ∗
     sheap_inv
    )%I;
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

Notation "f '@t' Kt" := (hasfun (hG:=gen_prog_inG_target) f Kt)
  (at level 20, format "f  @t  Kt") : bi_scope.
Notation "f '@s' Ks" := (hasfun (hG:=gen_prog_inG_source) f Ks)
  (at level 20, format "f  @s  Ks") : bi_scope.

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

(** Program for target *)
Lemma hasfun_target_agree f K_t1 K_t2 : f @t K_t1 -∗ f @t K_t2 -∗ ⌜K_t1 = K_t2⌝.
Proof. apply hasfun_agree. Qed.

(** Program for source *)
Lemma hasfun_source_agree f K_s1 K_s2 : f @s K_s1 -∗ f @s K_s2 -∗ ⌜K_s1 = K_s2⌝.
Proof. apply hasfun_agree. Qed.

(** operational heap lemmas *)
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

Lemma target_red_allocN_seq n v Ψ :
  (0 < n)%Z →
  (∀ l, ([∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦t v) -∗
    target_red (of_val #l) Ψ) -∗
  target_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Ψ.
Proof.
  iIntros (Hn) "Hloc". iApply target_red_lift_head_step.
  iIntros (P_s σ_s P_t σ_t) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)". iModIntro.
  iSplitR. { iPureIntro. eauto with lia head_step. }
  iIntros (e_t' σ_t') "%"; inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hσ_t")
    as "(Hσ_t & Hl & Hm)".
  { apply heap_array_map_disjoint. rewrite replicate_length Z2Nat.id; auto with lia. }
  iPoseProof (heap_array_to_seq_mapsto with "Hl") as "Hmap".
  iModIntro. iFrame. by iApply "Hloc".
Qed.

Lemma source_red_allocN_seq n v Ψ :
  (0 < n)%Z →
  (∀ l, ([∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦s v) -∗
    source_red (of_val #l) Ψ) -∗
  source_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Ψ.
Proof.
  iIntros (Hn) "Hloc". iApply source_red_lift_head_step.
  iIntros (P_s σ_s P_t σ_t) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _]".
  assert (head_reducible P_s (AllocN #n v) σ_s) as (e_s' & σ_s' & Hred).
  { eauto with lia head_step. }
  inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hσ_s")
    as "(Hσ_s & Hl & Hm)".
  { apply heap_array_map_disjoint. rewrite replicate_length Z2Nat.id; auto with lia. }
  iModIntro. iExists #l, (state_init_heap l n v σ_s).
  iSplitR. { eauto with lia head_step. }
  iFrame. iModIntro.
  iApply "Hloc". iApply (heap_array_to_seq_mapsto with "Hl").
Qed.

Lemma target_red_alloc v Ψ :
  (∀ l, l ↦t v -∗ target_red (of_val #l) Ψ) -∗
  target_red (Alloc (Val v)) Ψ.
Proof.
  iIntros "Ht". iApply (target_red_allocN_seq); first lia.
  iIntros (l) "[Hl _]". iApply "Ht". by rewrite loc_add_0.
Qed.

Lemma source_red_alloc v Ψ :
  (∀ l, l ↦s v -∗ source_red (of_val #l) Ψ) -∗
  source_red (Alloc (Val v)) Ψ.
Proof.
  iIntros "Ht". iApply (source_red_allocN_seq); first lia.
  iIntros (l) "[Hl _]". iApply "Ht". by rewrite loc_add_0.
Qed.

Lemma target_red_free v l Ψ :
  l ↦t v -∗ target_red (of_val #()) Ψ -∗
  target_red (Free (Val $ LitV (LitLoc l))) Ψ.
Proof.
  iIntros "Hl Hsim". iApply target_red_lift_head_step.
  iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iDestruct (gen_heap_valid with "Hσ_t Hl") as %?.
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' σ_t') "%"; inv_head_step.
  iMod (gen_heap_update with "Hσ_t Hl") as "[$ Hl]".
  iModIntro. iFrame.
Qed.

Lemma source_red_free v l Ψ :
  l ↦s v -∗ source_red (of_val #()) Ψ -∗
  source_red (Free (Val $ LitV (LitLoc l))) Ψ.
Proof.
  iIntros "Hl Hsim". iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _]".
  iModIntro. iDestruct (gen_heap_valid with "Hσ_s Hl") as %?.
  assert (head_reducible P_s (Free #l) σ_s) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done.
  inv_head_step. iMod (gen_heap_update with "Hσ_s Hl") as "[$ Hl]".
  iModIntro. iFrame.
Qed.

Lemma target_red_load l dq v Ψ :
  l ↦t{dq} v -∗
  (l ↦t{dq} v -∗ target_red (of_val v) Ψ) -∗
  target_red (Load (Val $ LitV $ LitLoc l)) Ψ.
Proof.
  iIntros "Hl Ht". iApply target_red_lift_head_step.
  iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iDestruct (gen_heap_valid with "Hσ_t Hl") as %?. iModIntro.
  iSplit; first by eauto with head_step.
  iIntros (?? Hstep); inv_head_step.
  iModIntro. iFrame. by iApply "Ht".
Qed.

Lemma source_red_load l dq v Ψ :
  l ↦s{dq} v -∗
  (l ↦s{dq} v -∗ source_red (of_val v) Ψ) -∗
  source_red (Load (Val $ LitV $ LitLoc l)) Ψ.
Proof.
  iIntros "Hl Ht". iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _]".
  iDestruct (gen_heap_valid with "Hσ_s Hl") as %?.
  assert (head_reducible P_s (Load #l) σ_s) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iModIntro; iExists e_s', σ_s'. iSplit; first by eauto. inv_head_step.
  iModIntro. iFrame. by iApply "Ht".
Qed.

Lemma target_red_store l v v' Ψ :
  l ↦t v' -∗
  (l ↦t v -∗ target_red (of_val #()) Ψ) -∗
  target_red (Store (Val $ LitV (LitLoc l)) (Val v)) Ψ.
Proof.
  iIntros "Hl Hsim". iApply target_red_lift_head_step.
  iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) !>".
  iDestruct (gen_heap_valid with "Hσ_t Hl") as %?.
  iSplitR; first by eauto with head_step.
  iIntros (e_t' σ_t') "%"; inv_head_step.
  iMod (gen_heap_update with "Hσ_t Hl") as "[$ Hl]".
  iModIntro. iFrame. by iApply "Hsim".
Qed.

Lemma source_red_store l v v' Ψ :
  l ↦s v' -∗
  (l ↦s v -∗ source_red (of_val #()) Ψ) -∗
  source_red (Store (Val $ LitV (LitLoc l)) (Val v)) Ψ.
Proof.
  iIntros "Hl Hsim". iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _] !>".
  iDestruct (gen_heap_valid with "Hσ_s Hl") as %?.
  assert (head_reducible P_s (Store (Val $ LitV (LitLoc l)) (Val v)) σ_s) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done. inv_head_step.
  iMod (gen_heap_update with "Hσ_s Hl") as "[$ Hl]".
  iModIntro. iFrame. by iApply "Hsim".
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
  iIntros (e_t' σ_t') "%"; inv_head_step.
  iModIntro. iFrame.
Qed.

Lemma source_red_call f K_s v Ψ :
  f @s K_s -∗
  source_red (fill K_s (Val v)) Ψ -∗
  source_red (Call (Val $ LitV $ LitFn f) (Val v)) Ψ.
Proof.
  iIntros "Hf Hred". iApply source_red_lift_head_step.
  iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & ?) _] !>".
  iDestruct (gen_prog_valid with "HP_s Hf") as %?.
  assert (head_reducible P_s (Call (Val $ LitV $ LitFn f) (Val v)) σ_s) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done. inv_head_step.
  iModIntro. iFrame.
Qed.

(** Call lemmas for sim *)
Lemma sim_call e_t e_s v_t v_s f :
  to_val e_t = Some v_t →
  to_val e_s = Some v_s →
  ⊢ Ω v_t v_s -∗ Call (#f f) e_t ⪯{Ω} Call (#f f) e_s {{ Ω }}.
Proof.
  intros <-%of_to_val <-%of_to_val.
  (* FIXME use lifting lemma for this *)
  iIntros "H". rewrite /sim /sim_stutter /sim_def sim_expr_unfold. iIntros (????) "[H1 H2]". iModIntro.
  iRight; iRight. iExists f, empty_ectx, v_t, empty_ectx, v_s, σ_s. cbn. iFrame.
  iSplitR; first done. iSplitR. { iPureIntro. constructor. }
  iIntros (v_t' v_s' ) "H". iApply sim_value. iApply "H".
Qed.

(** Coinduction support *)
Lemma sim_while_while b_t b_s c_t c_s Inv Ψ :
  Inv -∗
  □ (Inv -∗
    (if: c_t then b_t ;; while: c_t do b_t od else #())%E ⪯{Ω}
    (if: c_s then b_s ;; while: c_s do b_s od else #())%E
      [{ λ e_t e_s, Ψ e_t e_s ∨ (⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗ Inv) }]) -∗
  (while: c_t do b_t od ⪯{Ω} while: c_s do b_s od [{ Ψ }])%E.
Proof.
  iIntros "Hinv_init #Hstep".
  iApply (sim_lift_head_coind _ (λ e_t e_s, ⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗ Inv)%I with "[] [Hinv_init]"); first last.
  { iFrame. eauto. }
  iModIntro. iIntros (?? ?? ??) "(-> & -> & Hinv) (Hstate & Hnreach)".
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' σ_t') "%Hhead"; inv_head_step.
  assert (head_reducible P_s (while: c_s do b_s od ) σ_s) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iModIntro. iExists e_s', σ_s'. inv_head_step. iFrame. iSplitR; first by eauto with head_step.
  iApply "Hstep". iFrame.
Qed.


Lemma sim_while_rec b_t c_t v_s (K_s : ectx) (Inv : val → iProp Σ) Ψ rec_n :
  Inv v_s -∗
  rec_n @s K_s -∗
  □ (∀ v_s', Inv v_s' -∗
    (if: c_t then b_t ;; while: c_t do b_t od else #())%E ⪯{Ω} (fill K_s v_s')%E
    [{ λ e_t e_s , Ψ e_t e_s ∨ (∃ v_s', ⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = Call #f rec_n (Val v_s')⌝ ∗ Inv v_s') }]) -∗
  (while: c_t do b_t od ⪯{Ω} Call #f rec_n v_s [{ Ψ }])%E.
Proof.
  iIntros "Hinv #Hrec #Hstep". iApply (sim_lift_head_coind _ (λ e_t e_s, (∃ v_s', ⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = Call #f rec_n (Val v_s')⌝ ∗ Inv v_s')%I)); first last.
  { iExists v_s. eauto. }
  iModIntro. iIntros (?? ?? ??) "He (Hstate & Hnreach)". iDestruct "He" as (v_s') "(-> & -> & Hinv)".
  iSpecialize ("Hstep" with "Hinv").
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' σ_t') "%Hhead"; inv_head_step.
  iModIntro. iExists (fill K_s v_s'), σ_s.

  iDestruct "Hstate" as "(? & HP_s & ? & ? &?)".
  iDestruct (gen_prog_valid with "HP_s Hrec") as %?.
  iFrame. by eauto with head_step.
Qed.

Lemma sim_rec_while b_s c_s v_t (K_t : ectx) (Inv : val → iProp Σ) Ψ rec_n :
  Inv v_t -∗
  rec_n @t K_t -∗
  □ (∀ v_t', Inv v_t' -∗
    (fill K_t v_t')%E ⪯{Ω}  (if: c_s then b_s ;; while: c_s do b_s od else #())%E
    [{ λ e_t e_s , Ψ e_t e_s ∨ (∃ v_t', ⌜e_t = Call #f rec_n (Val v_t')⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗  Inv v_t') }]) -∗
  ( Call #f rec_n v_t ⪯{Ω} while: c_s do b_s od [{ Ψ }])%E.
Proof.
  iIntros "Hinv #Hrec #Hstep". iApply (sim_lift_head_coind _ (λ e_t e_s, (∃ v_t', ⌜e_t = Call #f rec_n (Val v_t')⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗  Inv v_t'))%I); first last.
  { iExists v_t. eauto. }
  iModIntro. iIntros (?? ?? ??) "He (Hstate & Hnreach)". iDestruct "He" as (v_s') "(-> & -> & Hinv)".
  iSpecialize ("Hstep" with "Hinv").

  iDestruct "Hstate" as "(HP_t & ? & ? & ? &?)".
  iDestruct (gen_prog_valid with "HP_t Hrec") as %?.
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' σ_t') "%Hhead"; inv_head_step.
  iModIntro.
  assert (head_reducible P_s (while: c_s do b_s od ) σ_s) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. inv_head_step. iFrame. iPureIntro. eauto with head_step.
Qed.

End lifting.
