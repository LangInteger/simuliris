From iris.prelude Require Export prelude.
From iris.prelude Require Import options.
From stdpp Require Import countable numbers gmap.
From simuliris.simplang Require Export base.
(* partly adapted from lambda rust *)

Definition block := positive.
Record loc := Loc { loc_block : block; loc_idx : Z }.
Add Printing Constructor loc.

Global Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Qed.

Global Instance loc_inhabited : Inhabited loc := populate {|loc_block := 1%positive; loc_idx := 0 |}.

Global Instance loc_countable : Countable loc.
Proof. by apply (inj_countable' (λ l, (loc_block l, loc_idx l)) (λ '(i, j), {| loc_block := i; loc_idx := j |})); intros []. Qed.

Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ '(i, j), {| loc_block := i; loc_idx := j |}) (λ l, Some ((loc_block l, loc_idx l))) _.
Next Obligation. intros []. done. Qed.

Definition loc_add (l : loc) (off : Z) : loc :=
  Loc (loc_block l) (loc_idx l + off).

Notation "l +ₗ off" :=
  (loc_add l off) (at level 50, left associativity) : stdpp_scope.

Lemma loc_add_assoc l i j : l +ₗ i +ₗ j = l +ₗ (i + j).
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.

Lemma loc_add_0 l : l +ₗ 0 = l.
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.
Lemma loc_add_block l n : loc_block (l +ₗ n) = loc_block l.
Proof. done. Qed.

Global Instance loc_add_inj l : Inj eq eq (loc_add l).
Proof. destruct l; rewrite /Inj /loc_add /=; intros; simplify_eq; lia. Qed.

Lemma loc_eta l : (Loc (loc_block l) (loc_idx l)) = l.
Proof.  by destruct l. Qed.
Lemma Loc_add b i : Loc b 0 +ₗ i = Loc b i.
Proof. done. Qed.
Definition fresh_block {X} (σ : gmap loc X) (bs : gset block) : block :=
  let loclst : list loc := elements (dom _ σ : gset loc) in
  let blockset : gset block := foldr (λ l, ({[loc_block l]} ∪.)) bs loclst in
  fresh blockset.

Ltac learn_fresh :=
  match goal with |- context [ fresh ?X ] =>
    let H := fresh in
    pose proof is_fresh X as H; move: (fresh X) H
  end.

Lemma is_fresh_block {X} (σ : gmap loc X) bs i :
  σ !! (Loc (fresh_block σ bs) i) = None.
Proof.
  apply not_elem_of_dom.
  rewrite /fresh_block /=. learn_fresh => f Hf Hin. apply Hf.
  rewrite <-elem_of_elements in Hin.
  induction (elements (dom (gset loc) σ)) => //=; set_solver.
Qed.

Lemma is_fresh_block_blocks {X} (σ : gmap loc X) bs :
  fresh_block σ bs ∉ bs.
Proof.
  rewrite /fresh_block. learn_fresh => f Hf.
  induction ((elements (dom (gset loc) σ))) => //. set_solver.
Qed.

Global Opaque fresh_block.
