From iris.base_logic.lib Require Import gset_bij.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
From simuliris.base_logic Require Import gen_sim_heap.
From iris.algebra.lib Require Import gset_bij.


(** * General ghost state construction that provides assertions that particular parts of the source and target heaps are in a bijection *)


Section gset_bij.
  Context `{gset_bijG Σ A B}.
  Implicit Types (L : gset (A * B)) (a : A) (b : B).

  (* TODO: maybe move into Iris?*)
  Lemma gset_bij_own_elem_auth_agree {γ q L} a b :
    gset_bij_own_auth γ q L -∗ gset_bij_own_elem γ a b -∗ ⌜(a, b) ∈ L⌝.
  Proof.
    iIntros "Hauth Helem". rewrite gset_bij_own_auth_eq gset_bij_own_elem_eq.
    (* TODO: is there a more elegant way to do this? *)
    iPoseProof (own_op with "[$Hauth $Helem]") as "Ha".
    iPoseProof (own_valid_r with "Ha") as "[Ha %]".
    iPoseProof (own_op with "Ha") as "[Hauth Helem]".
    iFrame. iPureIntro. revert H2. rewrite bij_both_dfrac_valid.
    intros (_ & _ & ?); done.
  Qed.
End gset_bij.

Class gen_heap_bij_preG `{gen_sim_heapG L_t L_s V_t V_s Σ} := GenHeapBijPreG {
  gen_heap_bij_pre_bijG :> gset_bijG Σ L_t L_s;
}.

Class gen_heap_bijG `{gen_sim_heapG L_t L_s V_t V_s Σ} := GenHeapBijG {
  gen_heap_bij_bijG :> gset_bijG Σ L_t L_s;
  gen_heap_bij_name : gname;
}.
Arguments GenHeapBijG L_t L_s V_t V_s Σ {_ _ _ _ _ _} _.
Arguments gen_heap_bij_name { L_t L_s V_t V_s Σ _ _ _ _ _ _} : assert.

Section definitions.
  Context `{gen_heap_bijG L_t L_s V_t V_s Σ}.

  Local Notation "l '↦t' v" := (mapsto (hG:=gen_heap_inG_target) l (DfracOwn 1) v)
    (at level 20, format "l  ↦t  v") : bi_scope.
  Local Notation "l '↦s' v" := (mapsto (hG:=gen_heap_inG_source) l (DfracOwn 1) v)
    (at level 20, format "l  ↦s  v") : bi_scope.

  Definition gen_heap_bij_auth (L : gset (L_t * L_s)) :=
    gset_bij_own_auth gen_heap_bij_name (DfracOwn 1) L.
  Definition gen_heap_bij_elem (l_t : L_t) (l_s : L_s) :=
    gset_bij_own_elem gen_heap_bij_name l_t l_s.

  Definition gen_heap_bij_inv (val_rel : V_t → V_s → iProp Σ) :=
    (∃ L, gen_heap_bij_auth L ∗
      [∗ set] p ∈ L, ∃ v_t v_s, (fst p) ↦t v_t ∗ (snd p) ↦s v_s ∗ val_rel v_t v_s)%I.
End definitions.

Notation "l_t '↔h' l_s" := (gen_heap_bij_elem l_t l_s) (at level 30) : bi_scope.

Section laws.
  Context `{gen_heap_bijG L_t L_s V_t V_s Σ}.

  Local Notation "l '↦t' v" := (mapsto (hG:=gen_heap_inG_target) l (DfracOwn 1) v)
    (at level 20, format "l  ↦t  v") : bi_scope.
  Local Notation "l '↦s' v" := (mapsto (hG:=gen_heap_inG_source) l (DfracOwn 1) v)
    (at level 20, format "l  ↦s  v") : bi_scope.

  Global Instance gen_heap_bij_elem_persistent l_t l_s :
    Persistent (l_t ↔h l_s).
  Proof. apply _. Qed.

  Lemma gen_heap_bij_access val_rel l_t l_s :
    gen_heap_bij_inv val_rel -∗
    l_t ↔h l_s -∗
    ∃ v_t v_s, l_t ↦t v_t ∗ l_s ↦s v_s ∗ val_rel v_t v_s ∗
      (∀ v_t' v_s', l_t ↦t v_t' -∗
        l_s ↦s v_s' -∗
        val_rel v_t' v_s' -∗
        gen_heap_bij_inv val_rel).
  Proof.
    iIntros "Hinv Hrel". iDestruct "Hinv" as (L) "[Hauth Hheap]".
    iPoseProof (gset_bij_own_elem_auth_agree with "Hauth Hrel") as "%".
    iPoseProof (big_sepS_delete with "Hheap") as "[He Hheap]"; first done.
    iDestruct "He" as (v_t v_s) "(H_t & H_s & Hvrel)".
    iExists v_t, v_s. iFrame.
    iIntros (v_t' v_s') "H_t H_s Hvrel".
    iExists L. iFrame. iApply big_sepS_delete; first done.
    iFrame. iExists v_t', v_s'. iFrame.
  Qed.

  Lemma gen_heap_bij_insert val_rel l_t l_s v_t v_s :
    gen_heap_bij_inv val_rel -∗
    l_t ↦t v_t -∗
    l_s ↦s v_s -∗
    val_rel v_t v_s ==∗
    gen_heap_bij_inv val_rel ∗ l_t ↔h l_s.
  Proof.
    iIntros "Hinv Ht Hs Hrel". iDestruct "Hinv" as (L) "[Hauth Hheap]".
    iAssert ((¬ ⌜set_Exists (λ '(l_t', l_s'), l_t = l_t') L⌝)%I) as "%".
    { iIntros "%". destruct H3 as ([l_t' l_s'] & Hin & <-).
      iPoseProof (big_sepS_elem_of with "Hheap") as (v_t' v_s') "(Hcon & _ & _)"; first by apply Hin.
      iPoseProof (mapsto_valid_2  with "Ht Hcon") as "%"; exfalso.
      (* FIXME: names *)
      destruct H3 as [Hcon _]. by apply dfrac_valid_own_r in Hcon.
    }
    rename H3 into Hext_t.
    iAssert ((¬ ⌜set_Exists (λ '(l_t', l_s'), l_s = l_s') L⌝)%I) as "%".
    { iIntros "%". destruct H3 as ([l_t' l_s'] & Hin & <-).
      iPoseProof (big_sepS_elem_of with "Hheap") as (v_t' v_s') "(_ & Hcon & _)"; first by apply Hin.
      iPoseProof (mapsto_valid_2 with "Hs Hcon") as "%"; exfalso.
      (* FIXME: names *)
      destruct H3 as [Hcon _]. by apply dfrac_valid_own_r in Hcon.
    }
    rename H3 into Hext_s.

    iMod ((gset_bij_own_extend l_t l_s) with "Hauth") as "[Hinv #Helem]".
    - intros l_s' Hl_s'. apply Hext_t. by exists (l_t, l_s').
    - intros l_t' Hl_t'. apply Hext_s. by exists (l_t', l_s).
    - iModIntro. iSplitL; last done.
      iExists ({[(l_t, l_s)]} ∪ L)%I. iFrame.
      iApply big_sepS_insert. { contradict Hext_t. by exists (l_t, l_s). }
      iFrame. iExists v_t, v_s. iFrame.
  Qed.

End laws.

Lemma gen_heap_bij_init_names `{gen_heap_bij_preG L_t L_s V_t V_s Σ} val_rel :
  ⊢ |==> ∃ γ : gname,
    let hG := GenHeapBijG L_t L_s V_t V_s Σ γ in
    gen_heap_bij_inv val_rel.
Proof.
  iMod (gset_bij_own_alloc_empty) as (γ) "Hinv".
  iExists γ. iModIntro. iExists (∅). iSplitL "Hinv"; first by iApply "Hinv".
  by iApply big_sepS_empty.
Qed.

Lemma gen_heap_bij_init `{gen_heap_bij_preG L_t L_s V_t V_s Σ} val_rel :
  ⊢ |==> ∃ _ : gen_heap_bijG, gen_heap_bij_inv val_rel.
Proof.
  iMod (gen_heap_bij_init_names val_rel) as (γ) "Hinit".
  iModIntro. iExists (GenHeapBijG _ _ _ _ _ γ). iFrame.
Qed.
