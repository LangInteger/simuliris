From simuliris.simplang Require Import lang notation tactics class_instances proofmode.
From iris Require Import bi.bi.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require heap_bij.

(** Some very trivial tests for the heap tactics *)


Module fix_bi.
Context `{sheapG Σ}.
Instance : sheapInv Σ := {|
  sheap_inv  := ⌜True⌝%I;
 |}.

Definition val_rel (v1 v2 : val) : iProp Σ := (⌜v1 = v2⌝)%I.

Lemma test_load l l2 :
  l ↦t #4 -∗ l2 ↦s #4 -∗
  ((! #l)%E ⪯{val_rel} ! #l2 {{ val_rel }}).
Proof.
  iIntros "H H1". target_load. source_load. eauto.
Qed.

Lemma test_store l l2 :
  l ↦t #4 -∗ l2 ↦s #4 -∗
  ((#l <- #42)%E ⪯{val_rel} #l2 <- #1337 {{ val_rel }}).
Proof.
  iIntros "H H1". target_store. source_store. eauto.
Qed.

(* FIXME: fix precedences for ⪯ to make the parantheses unnecessary *)
Lemma test_alloc :
  ⊢ (Alloc #2 ;; #()) ⪯{val_rel} (Alloc #4;;#()) {{ val_rel }}.
Proof.
  target_alloc l1 as "H".
  source_alloc l2 as "H2".
  (*to_sim. *)
  (*target_red_pures.  source_red_pures. *)
  sim_pures.
  eauto.
Qed.

Lemma test_free l l2 :
  l ↦t #42 -∗ l2 ↦s #1337 -∗
  Free #l ⪯{val_rel} Free #l2 {{ val_rel }}.
Proof.
  iIntros "H1 H2".
  target_free. source_free. eauto.
Qed.
End fix_bi.

Module bij_test.
  Import heap_bij.
  Context `{sbijG Σ}.

  Definition val_rel (v_t v_s : val) :=
    (match v_t, v_s with
    | LitV (LitLoc l_t), LitV (LitLoc l_s) => l_t ↔h l_s
    | _,_ => ⌜v_t = v_s⌝
    end)%I.
  Instance : sheapInv Σ := heap_bij_inv val_rel.
  Instance val_rel_pers v_t v_s : Persistent (val_rel v_t v_s).
  Proof. destruct v_t as [[] | | | ], v_s as [[] | | | ]; apply _. Qed.


  Lemma test_load l l2 :
    l ↦t #4 -∗ l2 ↦s #4 -∗
    ((! #l)%E ⪯{val_rel} ! #l2 {{ val_rel }}).
  Proof.
    iIntros "H H1". target_load. source_load. eauto.
  Qed.

  Lemma test_store l l2 :
    l ↦t #4 -∗ l2 ↦s #4 -∗
    ((#l <- #42)%E ⪯{val_rel} #l2 <- #1337 {{ val_rel }}).
  Proof.
    iIntros "H H1". target_store. source_store. eauto.
  Qed.

  Lemma test_insert l l2 :
    l ↦t #4 -∗ l2 ↦s #4 -∗
    ((#l <- #42)%E ⪯{val_rel} #l2 <- #42 {{ val_rel }}).
  Proof.
    iIntros "H H1".
    iApply (sim_bij_insert val_rel with "H H1 [# ]"); first done; iIntros "Hb".
    iApply (sim_bij_store with "Hb []"); last by sim_value_head.
    done.
  Qed.

  Lemma test_bij_store (l_t l_s : loc) :
    l_t ↔h l_s -∗
    (#l_t <- #42)%E ⪯{val_rel} (#l_s <- #42)%E {{ val_rel }}.
  Proof.
    iIntros "H". sim_store; first done. done.
  Qed.

  Lemma test_bij_load (l_t l_s : loc) :
    l_t ↔h l_s -∗
    ! #l_t ⪯{val_rel} ! #l_s {{ val_rel }}.
  Proof.
    iIntros "H". sim_load v_t v_s as "Ha". done.
  Qed.

  Lemma test_bij_free (l_t l_s : loc) :
    l_t ↔h l_s -∗
    Free #l_t ⪯{val_rel} Free #l_s {{ val_rel }}.
  Proof.
    iIntros "#H". sim_free. done.
  Qed.
End bij_test.
