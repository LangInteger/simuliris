(** Lift the simulation relation to open terms.
    This is the "expression relation" of our logical relation. *)

From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst heap_bij.

Section open_rel.
  Context `{sbijG Σ}.

  (** Well-formed substitutions closing source and target, with [X] denoting the
      free variables. *)
  Definition subst_map_rel (X : gset string) (map : gmap string (val * val)) : iProp Σ :=
    [∗ set] x ∈ X,
      match map !! x with
      | Some (v_t, v_s) => val_rel v_t v_s
      | None => False
      end.

  Global Instance subst_map_rel_pers X map : Persistent (subst_map_rel X map).
  Proof.
    rewrite /subst_map_rel. apply big_sepS_persistent=>x.
    destruct (map !! x) as [[v_t v_s]|]; apply _.
  Qed.

  Lemma subst_map_rel_lookup {X map} x :
    x ∈ X →
    subst_map_rel X map -∗
    ∃ v_t v_s, ⌜map !! x = Some (v_t, v_s)⌝ ∗ val_rel v_t v_s.
  Proof.
    iIntros (Hx) "Hrel".
    iDestruct (big_sepS_elem_of _ _ x with "Hrel") as "Hrel"; first done.
    destruct (map !! x) as [[v_t v_s]|]; last done. eauto.
  Qed.

  Lemma subst_map_rel_weaken {X1} X2 map :
    X2 ⊆ X1 →
    subst_map_rel X1 map -∗ subst_map_rel X2 map.
  Proof. iIntros (HX). iApply big_sepS_subseteq. done. Qed.

  (* TODO: use [binder_delete], once we can [delete] on [gset]. *)
  Definition binder_delete_gset (b : binder) (X : gset string) :=
    match b with BAnon => X | BNamed x => X ∖ {[x]} end.

  Lemma subst_map_rel_insert X x v_t v_s map :
    subst_map_rel (binder_delete_gset x X) map -∗
    val_rel v_t v_s -∗
    subst_map_rel X (binder_insert x (v_t, v_s) map).
  Proof.
    iIntros "#Hmap #Hval". destruct x; first done. simpl.
    iApply big_sepS_intro. iIntros "!# %s' %Hs'".
    destruct (decide (s = s')) as [->|Hne].
    - rewrite lookup_insert. done.
    - rewrite lookup_insert_ne //.
      iApply (big_sepS_elem_of with "Hmap"). set_solver.
  Qed.

  Lemma subst_map_rel_empty map :
    ⊢ subst_map_rel ∅ map.
  Proof. iApply big_sepS_empty. done. Qed.

  (** The "expression relation" of our logical relation:
      The simulation relation must hold after applying an arbitrary well-formed
      closing substitution [map]. *)
  Definition expr_rel e_t e_s : iProp Σ :=
    ∀ π (map : gmap string (val * val)),
      subst_map_rel (free_vars e_t ∪ free_vars e_s) map -∗
      subst_map (fst <$> map) e_t ⪯{π, val_rel} subst_map (snd <$> map) e_s {{ val_rel }}.

  Lemma expr_rel_closed e_t e_s :
    free_vars e_t = ∅ →
    free_vars e_s = ∅ →
    expr_rel e_t e_s ⊣⊢ (∀ π, e_t ⪯{π, val_rel} e_s {{ val_rel }}).
  Proof.
    intros Hclosed_t Hclosed_s. iSplit.
    - iIntros "Hwf" (π). iSpecialize ("Hwf" $! π ∅).
      rewrite ->!fmap_empty, ->!subst_map_empty.
      rewrite Hclosed_t Hclosed_s [∅ ∪ _]left_id_L.
      iApply "Hwf". by iApply subst_map_rel_empty.
    - iIntros "Hsim" (π xs) "Hxs".
      rewrite !subst_map_closed //.
  Qed.

  (** Substitute away a single variable in an [expr_rel].
      Use the [expr_rel] tactic below to automatically apply this for all free variables. *)
  Lemma expr_rel_subst x e_t e_s :
    (∀ (v_t v_s : val), val_rel v_t v_s -∗
      expr_rel (subst x v_t e_t) (subst x v_s e_s)) -∗
    expr_rel e_t e_s.
  Proof.
    iIntros "Hsim" (π xs) "#Hxs".
    destruct (decide (x ∈ free_vars e_t ∪ free_vars e_s)) as [Hin|Hnotin]; last first.
    { iSpecialize ("Hsim" $! #0 #0).
      rewrite ->subst_free_vars by set_solver.
      rewrite ->subst_free_vars by set_solver.
      iApply "Hsim"; eauto. }
    iDestruct (subst_map_rel_lookup x with "Hxs") as (v_t v_s Hv) "Hrel"; first done.
    iSpecialize ("Hsim" $! v_t v_s with "Hrel").
    iSpecialize ("Hsim" $! π xs with "[Hxs]").
    { iApply (subst_map_rel_weaken with "Hxs").
      rewrite !free_vars_subst. set_solver. }
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
