(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.tree_borrows Require Export defs steps_foreach.
From iris.prelude Require Import options.

Lemma free_mem_lookup l n h :
  (∀ (i: nat), (i < n)%nat → free_mem l n h !! (l +ₗ i) = None) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) →
    free_mem l n h !! l' = h !! l').
Proof.
  revert l. induction n as [|n IH]; intros l; simpl.
  { split; intros ??; by [lia|]. } split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0 lookup_delete //.
    + rewrite lookup_delete_ne.
      * specialize (IH (l +ₗ 1))as [IH _].
        rewrite (_: l +ₗ S i = l +ₗ 1 +ₗ i).
        { apply IH. lia. }
        { rewrite shift_loc_assoc. f_equal. lia. }
      * rewrite -{1}(shift_loc_0 l).
        move => /shift_loc_inj ?. lia.
  - intros l' Lt.
    rewrite lookup_delete_ne.
    + apply IH. intros i Lti.
      rewrite (_: l +ₗ 1 +ₗ i = l +ₗ S i).
      * apply Lt. lia.
      * rewrite shift_loc_assoc. f_equal. lia.
    + rewrite -(shift_loc_0_nat l). intros ?. subst l'. apply (Lt O); [lia|done].
Qed.

Lemma free_mem_lookup_case l' l n h :
  (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∧ free_mem l n h !! l' = h !! l' ∨
  ∃ i : nat, (i < n)%nat ∧ l' = l +ₗ i ∧ free_mem l n h !! (l +ₗ i) = None.
Proof.
  destruct (free_mem_lookup l n h) as [EQ1 EQ2].
  destruct (block_case l l' n) as [NEql|Eql].
  - left. rewrite -EQ2 //.
  - right. destruct Eql as (i & Lt & ?). exists i. do 2 (split; [done|]).
    subst l'. by apply EQ1.
Qed.

Lemma free_mem_dom_inv l' l n h:
  l' ∈ dom (free_mem l n h) →
  l' ∈ dom h ∧
  (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∧ free_mem l n h !! l' = h !! l'.
Proof.
  intros [? EqD]%elem_of_dom.
  destruct (free_mem_lookup_case l' l n h) as [Eqn|(i & Lt & ? & EqN)].
  - split; [|done]. apply elem_of_dom. destruct Eqn as [? Eqn].
    rewrite -Eqn. by eexists.
  - exfalso. subst l'. by rewrite EqD in EqN.
Qed.



Lemma init_mem_lookup_fresh_poison blk off (n:nat) h :
  0 ≤ off ∧ off < n →
  init_mem (blk, 0) n h !! (blk, off) = Some ScPoison.
Proof.
  intros (Hpos & Hlt).
  pose proof (init_mem_lookup (blk, 0) n h) as (Hinit1&_).
  ospecialize (Hinit1 (Z.to_nat off) _); first lia.
  rewrite /= /shift_loc /= Z.add_0_l Z2Nat.id // in Hinit1.
Qed.

Lemma init_mem_lookup_fresh_None blk off (n:nat) h :
  (forall off, (blk, off) ∉ dom h) →
  (off < 0 ∨ n ≤ off) →
  init_mem (blk, 0) n h !! (blk, off) = None.
Proof.
  intros Hfresh Hout.
  pose proof (init_mem_lookup (blk, 0) n h) as (_&Hinit2).
  rewrite (Hinit2 (blk, off)).
  + eapply not_elem_of_dom, Hfresh.
  + intros i Hlt.
    rewrite /= /shift_loc /= Z.add_0_l.
    intros [= ->]. destruct Hout as [Hout|Hout]; lia.
Qed.

Lemma init_mem_lookup_fresh_old blk blk' off (n:nat) h :
  blk ≠ blk' →
  init_mem (blk, 0) n h !! (blk', off) = h !! (blk', off).
Proof.
  intros Hfresh.
  pose proof (init_mem_lookup (blk, 0) n h) as (_&Hinit2).
  apply Hinit2.
  intros ? _ [=]. done.
Qed.


Lemma init_mem_lookup_fresh_inv blk blk' off (n:nat) h k :
  (forall off, (blk, off) ∉ dom h) →
  init_mem (blk, 0) n h !! (blk', off) = k →
  (k = Some ScPoison ∧ blk = blk' ∧ 0 ≤ off ∧ off < n)
∨ (k = None ∧ blk = blk' ∧ (off < 0 ∨ n ≤ off))
∨ (k = h !! (blk', off) ∧ blk ≠ blk').
Proof.
  intros Hfresh Hinit.
  destruct (decide (blk = blk')) as [Heqblk|Hne].
  1: subst blk'; destruct (decide (0 ≤ off)) as [Hpos|Hneg].
  1: destruct (decide (off < n)) as [Hlt|Hge].
  { left. subst k. split_and!; try done. by rewrite init_mem_lookup_fresh_poison. }
  1-2: right; left; split_and!; try done; last lia.
  1-2: subst k; rewrite init_mem_lookup_fresh_None; try done; lia.
  { right. right. split; last done. subst k. by apply init_mem_lookup_fresh_old. }
Qed.

