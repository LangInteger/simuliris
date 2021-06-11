From iris.proofmode Require Import tactics.

(* TODO: upstream the following definitions *)
Ltac get_head e :=
  lazymatch e with
  | ?h _ => get_head constr:(h)
  | _    => constr:(e)
  end.

Lemma fst_map_zip {A B C} `{!EqDecision A} `{!Countable A} (m1 : gmap A B) (m2 : gmap A C) :
  (∀ k : A, is_Some (m1 !! k) → is_Some (m2 !! k)) →
  fst <$> map_zip m1 m2 = m1.
Proof. move => ?. by apply: map_fmap_zip_with_l. Qed.

Lemma snd_map_zip {A B C} `{!EqDecision A} `{!Countable A} (m1 : gmap A B) (m2 : gmap A C) :
  (∀ k : A, is_Some (m2 !! k) → is_Some (m1 !! k)) →
  snd <$> map_zip m1 m2 = m2.
Proof. move => ?. by apply: map_fmap_zip_with_r. Qed.

Lemma take_lookup_Some {A} n k (l : list A) x:
  take n l !! k = Some x ↔ l !! k = Some x ∧ k < n.
Proof.
  split.
  - destruct (decide (k < n)).
    + rewrite lookup_take; naive_solver.
    + rewrite lookup_take_ge //. lia.
  - move => [??]. by rewrite lookup_take.
Qed.

Lemma map_seq_insert_0 {A} (ls : list A) i x:
  i < length ls →
  <[i:=x]> (map_seq (M :=gmap _ _) 0 ls) = map_seq 0 (<[i:=x]>ls).
Proof.
  move => ?. apply: map_eq => j. rewrite lookup_map_seq_0.
  destruct (decide (i = j)); simplify_map_eq.
  - by rewrite list_lookup_insert.
  - by rewrite lookup_map_seq_0 list_lookup_insert_ne.
Qed.

Lemma big_sepL2_exist {PROP : bi} {A B C} (l1 : list A) (l2 : list B) (Φ : _ → _ → _ → _ → PROP) `{!BiAffine PROP} :
  ([∗ list] i↦x1;x2∈l1;l2, ∃ x : C, Φ i x1 x2 x) -∗
   ∃ xs : list C, ⌜length xs = length l1⌝ ∗ ([∗ list] i↦x1;x2∈l1;l2, ∃ x : C, ⌜xs !! i = Some x⌝ ∗ Φ i x1 x2 x).
Proof.
  iIntros "Hl".
  iInduction (l1) as [|? l1] "IH" forall (l2 Φ).
  { iDestruct (big_sepL2_nil_inv_l with "Hl") as %->. iExists []. by iSplit. }
  iDestruct (big_sepL2_cons_inv_l with "Hl") as (x2 l2' ->) "[[%x ?] Hl]".
  iDestruct ("IH" with "Hl") as (xs) "[%Heq ?]".
  iExists (x::xs) => /=. iSplit; [by rewrite /= Heq|]. iFrame.
  iExists _. by iFrame.
Qed.
Lemma big_sepL2_to_sepL_r {PROP : bi} {A B} (l1 : list A) (l2 : list B) (Φ : _ → _ → _ → PROP) `{!BiAffine PROP}:
  length l1 = length l2 →
  ([∗ list] i↦x1;x2∈l1;l2, Φ i x1 x2) ⊣⊢
  ([∗ list] i↦x2∈l2, ∃ x1, ⌜l1 !! i = Some x1⌝ ∗  Φ i x1 x2).
Proof.
  elim: l1 l2 Φ. { by case. }
  move => x l1 IH [//|y l2] Φ /= [?]. rewrite IH //. f_equiv.
  iSplit; first by eauto with iFrame. iIntros "[%x1 [% ?]]"; by simplify_eq.
Qed.

Definition exists_dec_unique {A} (x : A) (P : _ → Prop) : (∀ y, P y → P x) → Decision (P x) → Decision (∃ y, P y).
Proof.
  intros Hx Hdec.
  refine (cast_if (decide (P x))).
  - abstract by eexists _.
  - abstract naive_solver.
Defined.

Lemma forall_equiv_dec {X} (P Q : X → Prop) (HPQ : Decision (∀ x, P x → Q x)) (HQP : Decision (∀ x, Q x → P x)) :
  Decision (∀ x, P x ↔ Q x).
Proof. destruct HPQ as [HPQ | HPQ]; destruct HQP as [HQP | HQP]; [left; naive_solver | right; naive_solver..]. Qed.
