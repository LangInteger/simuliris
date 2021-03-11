From simuliris.simplang Require Import lang notation tactics class_instances proofmode.
From iris Require Import bi.bi.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.

(** Some very trivial tests for the heap tactics *)


Section fix_bi.
Context `{sheapG Σ}.

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
