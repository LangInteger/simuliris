From iris.prelude Require Export prelude.
From iris.prelude Require Import options.
From stdpp Require Import countable numbers gmap.
(* partly adapted from lambda rust *)

Definition block := positive.
Record loc := mkloc { loc_chunk : block; loc_idx : Z }.

Global Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Qed.

Global Instance loc_inhabited : Inhabited loc := populate {|loc_chunk := 1%positive; loc_idx := 0 |}.

Global Instance loc_countable : Countable loc.
Proof. by apply (inj_countable' (λ l, (loc_chunk l, loc_idx l)) (λ '(i, j), {| loc_chunk := i; loc_idx := j |})); intros []. Qed.

Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ '(i, j), {| loc_chunk := i; loc_idx := j |}) (λ l, Some ((loc_chunk l, loc_idx l))) _.
Next Obligation. intros []. done. Qed.

Definition loc_add (l : loc) (off : Z) : loc :=
  {| loc_chunk := loc_chunk l; loc_idx := loc_idx l + off|}.

Notation "l +ₗ off" :=
  (loc_add l off) (at level 50, left associativity) : stdpp_scope.

Lemma loc_add_assoc l i j : l +ₗ i +ₗ j = l +ₗ (i + j).
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.

Lemma loc_add_0 l : l +ₗ 0 = l.
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.
Lemma loc_add_block l n : loc_chunk (l +ₗ n) = loc_chunk l.
Proof. done. Qed.

Global Instance loc_add_inj l : Inj eq eq (loc_add l).
Proof. destruct l; rewrite /Inj /loc_add /=; intros; simplify_eq; lia. Qed.

Lemma loc_eta l : (mkloc (loc_chunk l) (loc_idx l)) = l.
Proof.  by destruct l. Qed.
Lemma mkloc_add b i : mkloc b 0 +ₗ i = mkloc b i.
Proof. rewrite /loc_add; cbn. by replace (0 + i)%Z with i%Z by lia. Qed.
Definition fresh_block {X} (σ : gmap loc X) : block :=
  let loclst : list loc := elements (dom _ σ : gset loc) in
  let blockset : gset block := foldr (λ l, ({[loc_chunk l]} ∪.)) ∅ loclst in
  fresh blockset.

Lemma is_fresh_block {X} (σ : gmap loc X) i : 
  σ !! ({|loc_chunk := fresh_block σ; loc_idx := i |} : loc) = None.
Proof.
  assert (∀ (l : loc) ls (S : gset block),
    l ∈ ls → (loc_chunk l) ∈ foldr (λ l, ({[(loc_chunk l)]} ∪.)) S ls) as help.
  { induction 1; set_solver. }
  rewrite /fresh_block /= -(not_elem_of_dom (D := gset loc)) -elem_of_elements.
  move=> /(help _ _ ∅) /=. apply is_fresh.
Qed.

Global Opaque fresh_block.
