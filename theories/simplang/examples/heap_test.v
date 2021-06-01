From simuliris.simplang Require Import lang notation tactics class_instances proofmode.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require heap_bij.

(** Some very trivial tests for the heap tactics *)


Module fix_bi.
Section a.
Context `{sheapGS Σ} (π : thread_id).
Program Instance : sheapInv Σ := {|
  sheap_inv _ _ _ := ⌜True⌝%I;
|}.
Next Obligation. done. Qed.
Global Instance : sheapInvSupportsAll.
Proof. done. Qed.

Definition val_rel (v1 v2 : val) : iProp Σ := (⌜v1 = v2⌝)%I.

Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{π, const val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.
Local Notation "et '⪯' es [{ Φ }]" := (et ⪯{π, const val_rel} es [{Φ}])%I (at level 40, Φ at level 200) : bi_scope.


Lemma test_load l l2 :
  l ↦t #4 -∗ l2 ↦s #4 -∗
  ((! #l)%E ⪯ ! #l2 {{ val_rel }}).
Proof.
  iIntros "H H1". target_load. source_load. sim_val. eauto.
Qed.

Lemma test_store l l2 :
  l ↦t #4 -∗ l2 ↦s #4 -∗
  ((#l <- #42)%E ⪯ #l2 <- #1337 {{ val_rel }}).
Proof.
  iIntros "H H1". target_store. source_store. sim_val. eauto.
Qed.

(* FIXME: fix precedences for ⪯ to make the parantheses unnecessary *)
Lemma test_alloc :
  ⊢ (Alloc #2 ;; #()) ⪯ (Alloc #4;;#()) {{ val_rel }}.
Proof.
  target_alloc l1 as "H" "_".
  source_alloc l2 as "H2" "_".
  sim_pures; sim_val.
  eauto.
Qed.

Lemma test_free l l2 :
  l ↦t #42 -∗ l2 ↦s #1337 -∗ †l …t 1 -∗ †l2 …s 1 -∗
  Free #l ⪯ Free #l2 {{ val_rel }}.
Proof.
  iIntros "H1 H2 H3 H4".
  target_free. source_free. sim_val. eauto.
Qed.

(* FIXME: if we remove the parantheses around the first element, parsing is broken *)
Lemma test_freeN l l2 :
  l ↦t∗ [(#42); #99] -∗ l2 ↦s∗ [(#1337); #420; #666] -∗ †l …t 2 -∗ †l2 …s 3 -∗
  FreeN #2 #l ⪯ FreeN #3 #l2 {{ val_rel }}.
Proof.
  iIntros "H1 H2 H3 H4".
  target_free; first done. source_free; first done. sim_val. eauto.
Qed.
End a.
End fix_bi.

Module bij_test.
  Import heap_bij.
  Context `{heapbijG Σ} (π : thread_id).
  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{π, const val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.
  Local Notation "et '⪯' es [{ Φ }]" := (et ⪯{π, const val_rel} es [{Φ}])%I (at level 40, Φ at level 200) : bi_scope.

  Lemma test_load l l2:
    l ↦t #4 -∗ l2 ↦s #4 -∗
    ((! #l)%E ⪯ ! #l2 {{ val_rel }}).
  Proof.
    iIntros "H H1". target_load. source_load. sim_val. eauto.
  Qed.

  Lemma test_store l l2:
    l ↦t #4 -∗ l2 ↦s #4 -∗
    ((#l <- #42)%E ⪯ #l2 <- #1337 {{ val_rel }}).
  Proof.
    iIntros "H H1". target_store. source_store. sim_val. eauto.
  Qed.

  Lemma test_insert l l2:
    l ↦t #4 -∗ l2 ↦s #4 -∗ †l …t 1 -∗ †l2 …s 1 -∗
    ((#l <- #42)%E ⪯ #l2 <- #42 {{ val_rel }}).
  Proof.
    iIntros "H H1 H2 H3".
    iApply (sim_bij_insert _ l l2 with "H2 H3 H H1 "); first done; iIntros "Hb".
    iApply (sim_bij_store with "Hb []"); first done. by sim_val.
  Qed.

  Lemma test_bij_store (l_t l_s : loc) :
    l_t ↔h l_s -∗
    (#l_t <- #42)%E ⪯ (#l_s <- #42)%E {{ val_rel }}.
  Proof.
    iIntros "H". sim_store; first done. by sim_val.
  Qed.

  Lemma test_bij_load (l_t l_s : loc):
    l_t ↔h l_s -∗
    ! #l_t ⪯ ! #l_s {{ val_rel }}.
  Proof.
    iIntros "H". sim_load v_t v_s as "Ha"; sim_val. done.
  Qed.

  Lemma test_bij_free (l_t l_s : loc):
    l_t ↔h l_s -∗
    Free #l_t ⪯ Free #l_s {{ val_rel }}.
  Proof.
    iIntros "#H". sim_free; sim_val. done.
  Qed.
End bij_test.
