(** Lift the simulation relation to open terms.
    This is the "expression relation" of our logical relation. *)

From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst heap_bij.

(** map_ForallI *)
Definition map_ForallI `{Lookup K A M} `(P : K → A → iProp Σ) : M → iProp Σ :=
    (λ m, ∀ i x, ⌜m !! i = Some x⌝ → P i x)%I.
Section map_Forall.
  Context `{FinMap K M}.
  Context {A} {Σ} (P : K → A → iProp Σ).
  Implicit Types m : M A.

  Lemma map_ForallI_empty : ⊢ map_ForallI P (∅ : M A).
  Proof. iIntros (i x). rewrite lookup_empty. by iIntros "%". Qed.
  Lemma map_ForallI_insert_2 m i x :
    ⊢ P i x -∗ map_ForallI P m -∗ map_ForallI P (<[i:=x]>m).
  Proof.
    iIntros "? Hm" (j y); rewrite lookup_insert_Some.
    iIntros "%Hv". destruct Hv as [[-> ->] | [Hneq Hs]]; first done.
    by iApply "Hm".
  Qed.
End map_Forall.

Section open_rel.
  Context `{sbijG Σ}.

  (** Well-formed substitutions in source and target*)

  Definition subst_map_rel (map : gmap string (val * val)) :=
    map_ForallI (λ _ '(v_t, v_s), val_rel v_t v_s) map.

  Global Instance subst_map_rel_pers map : Persistent (subst_map_rel map).
  Proof.
    rewrite /subst_map_rel /map_ForallI.
    apply bi.forall_persistent => x. apply bi.forall_persistent; intros [a b].
    apply _.
  Qed.

  Lemma subst_map_rel_insert map v_t v_s b :
    val_rel v_t v_s -∗
    subst_map_rel map -∗
    subst_map_rel (binder_insert b (v_t, v_s) map).
  Proof.
    iIntros "Hv Hs". destruct b; first done. by iApply (map_ForallI_insert_2 with "[Hv] Hs").
  Qed.

  Lemma subst_map_rel_empty : ⊢ subst_map_rel ∅.
  Proof. apply map_ForallI_empty. Qed.

  (** The "expression relation" of our logical relation:
      The simulation relation must hold after applying an arbitrary well-formed
      closing substitution [map]. *)
  Definition expr_rel e_t e_s : iProp Σ :=
    ∀ π (map : gmap string (val * val)),
      ⌜free_vars e_t ∪ free_vars e_s ⊆ dom (gset _) map⌝ -∗
      subst_map_rel map -∗
      subst_map (fst <$> map) e_t ⪯{π, val_rel} subst_map (snd <$> map) e_s {{ val_rel }}.

  Lemma expr_rel_closed e_t e_s :
    free_vars e_t = ∅ →
    free_vars e_s = ∅ →
    expr_rel e_t e_s ⊣⊢ (∀ π, e_t ⪯{π, val_rel} e_s {{ val_rel }}).
  Proof.
    intros Hclosed_t Hclosed_s. iSplit.
    - iIntros "Hwf" (π). iSpecialize ("Hwf" $! π ∅).
      rewrite ->!fmap_empty, ->!subst_map_empty.
      iApply "Hwf"; last by iApply subst_map_rel_empty.
      iPureIntro. set_solver.
    - iIntros "Hsim" (π xs _) "Hxs".
      rewrite !subst_map_closed //.
  Qed.

  (** Substitute away a single variable in an [expr_rel].
      Use the [expr_rel] tactic below to automatically apply this for all free variables. *)
  Lemma expr_rel_subst x e_t e_s :
    (∀ (v_t v_s : val), val_rel v_t v_s -∗
      expr_rel (subst x v_t e_t) (subst x v_s e_s)) -∗
    expr_rel e_t e_s.
  Proof.
    iIntros "Hsim" (π xs Hdom) "#Hxs".
    destruct (decide (x ∈ free_vars e_t ∪ free_vars e_s)) as [Hin|Hnotin]; last first.
    { iSpecialize ("Hsim" $! #0 #0).
      rewrite ->subst_free_vars by set_solver.
      rewrite ->subst_free_vars by set_solver.
      iApply "Hsim"; eauto. }
    assert (is_Some (xs !! x)) as [[v_t v_s] Hv].
    { apply elem_of_dom. set_solver. }
    iSpecialize ("Hsim" $! v_t v_s with "[]").
    { iApply ("Hxs" $! _ (_, _)). done. }
    iSpecialize ("Hsim" $! π xs with "[] Hxs").
    { iPureIntro. rewrite !free_vars_subst. set_solver. }
    rewrite !subst_map_subst.
    rewrite insert_id.
    2:{ rewrite lookup_fmap Hv //. }
    rewrite insert_id.
    2:{ rewrite lookup_fmap Hv //. }
    done.
  Qed.

End open_rel.

(** Applies expr_rel_subst for each element of [l],
    introduces the new terms under some fresh names,
    calls [cont] on the remaining goal,
    then reverts all the fresh names. *)
Local Ltac expr_rel_subst_l l cont :=
  match l with
  | nil => cont ()
  | ?x :: ?l =>
    iApply (expr_rel_subst x);
    let v_t := fresh "v_t" in
    let v_s := fresh "v_s" in
    let H := iFresh in
    iIntros (v_t v_s) H;
    expr_rel_subst_l l ltac:(fun _ =>
      cont ();
      iRevert (v_t v_s) H
    )
  end.

(** Turns an [expr_rel] goal into a [sim] goal by applying a
    suitable substitution. *)
Ltac expr_rel :=
  iStartProof;
  match goal with
  | |- proofmode.environments.envs_entails _ (expr_rel ?e_t ?e_s) =>
    let free := eval vm_compute in (elements (free_vars e_t ∪ free_vars e_s)) in
    expr_rel_subst_l free ltac:(fun _ => simpl; iApply expr_rel_closed; [compute_done..|])
  end.
