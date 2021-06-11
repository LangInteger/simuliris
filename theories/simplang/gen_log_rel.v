From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst primitive_laws gen_val_rel wf.

(** * Logical relation
 This file defines the top-level "logical relation" which lifts the
 simulation relation (the "expression relation") to open terms.
*)

Section open_rel.
  Context `{!sheapGS Σ} `{!sheapInv Σ}.
  Context (loc_rel : loc → loc → iProp Σ) (thread_own : thread_id → iProp Σ).
  Local Notation val_rel := (gen_val_rel loc_rel).

  (** Well-formed substitutions closing source and target, with [X] denoting the
      free variables. *)
  Definition subst_map_rel (X : gset string) (map : gmap string (val * val)) : iProp Σ :=
    [∗ set] x ∈ X,
      match map !! x with
      | Some (v_t, v_s) => val_rel v_t v_s
      | None => False
      end.

  Global Instance subst_map_rel_pers X map `{!∀ vt vs, Persistent (val_rel vt vs)} :
    Persistent (subst_map_rel X map).
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

  Lemma subst_map_rel_insert X x v_t v_s map `{!∀ vt vs, Persistent (val_rel vt vs)} :
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

  (** The core "logical relation" of our system:
      The simulation relation ("expression relation") must hold after applying
      an arbitrary well-formed closing substitution [map]. *)
  Definition gen_log_rel e_t e_s : iProp Σ :=
    □ ∀ π (map : gmap string (val * val)),
      subst_map_rel (free_vars e_t ∪ free_vars e_s) map -∗
      thread_own π -∗
      subst_map (fst <$> map) e_t ⪯{π} subst_map (snd <$> map) e_s {{ λ v_t v_s, thread_own π ∗ val_rel v_t v_s }}.

  Lemma gen_log_rel_closed_1 e_t e_s π :
    free_vars e_t ∪ free_vars e_s = ∅ →
    gen_log_rel e_t e_s ⊢
      thread_own π -∗ e_t ⪯{π} e_s {{ λ v_t v_s, thread_own π ∗ val_rel v_t v_s }}.
  Proof.
    iIntros (Hclosed) "#Hrel". iSpecialize ("Hrel" $! π ∅).
    rewrite ->!fmap_empty, ->!subst_map_empty.
    rewrite Hclosed. iApply "Hrel". by iApply subst_map_rel_empty.
  Qed.

  Lemma gen_log_rel_closed e_t e_s :
    free_vars e_t ∪ free_vars e_s = ∅ →
    gen_log_rel e_t e_s ⊣⊢
      (□ ∀ π, thread_own π -∗ e_t ⪯{π} e_s {{ λ v_t v_s, thread_own π ∗ val_rel v_t v_s }}).
  Proof.
    intros Hclosed. iSplit.
    { iIntros "#Hrel !#" (π). iApply gen_log_rel_closed_1; done. }
    iIntros "#Hsim" (π xs) "!# Hxs".
    rewrite !subst_map_closed //; set_solver.
  Qed.

  (** Substitute away a single variable in an [gen_log_rel].
      Use the [gen_log_rel] tactic below to automatically apply this for all free variables. *)
  Lemma gen_log_rel_subst x e_t e_s `{!∀ vt vs, Persistent (val_rel vt vs)}:
    (□ ∀ (v_t v_s : val), val_rel v_t v_s -∗
      gen_log_rel (subst x v_t e_t) (subst x v_s e_s)) -∗
    gen_log_rel e_t e_s.
  Proof.
    iIntros "#Hsim" (π xs) "!# #Hxs".
    destruct (decide (x ∈ free_vars e_t ∪ free_vars e_s)) as [Hin|Hnotin]; last first.
    { iSpecialize ("Hsim" $! #() #()).
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

(** Applies gen_log_rel_subst for each element of [l],
    introduces the new terms under some fresh names,
    calls [cont] on the remaining goal,
    then reverts all the fresh names. *)
Local Ltac log_rel_subst_l l cont :=
  match l with
  | nil => cont ()
  | ?x :: ?l =>
    iApply (gen_log_rel_subst _ _ x);
    let v_t := fresh "v_t" in
    let v_s := fresh "v_s" in
    let H := iFresh in
    iIntros (v_t v_s) "!#";
    let pat := constr:(intro_patterns.IIntuitionistic (intro_patterns.IIdent H)) in
    iIntros pat;
    log_rel_subst_l l ltac:(fun _ =>
      cont ();
      iRevert (v_t v_s) H
    )
  end.

(** Turns an [gen_log_rel] goal into a [sim] goal by applying a
    suitable substitution. *)
Ltac log_rel :=
  iStartProof;
  lazymatch goal with
  | |- proofmode.environments.envs_entails _ (gen_log_rel ?val_rel ?town ?e_t ?e_s) =>
    let h_t := get_head e_t in try unfold h_t;
    let h_s := get_head e_s in try unfold h_s
  end;
  lazymatch goal with
  | |- proofmode.environments.envs_entails _ (gen_log_rel ?val_rel ?town ?e_t ?e_s) =>
    let e_t' := W.of_expr e_t in
    let e_s' := W.of_expr e_s in
    let free := eval vm_compute in (remove_dups (W.free_vars e_t' ++ W.free_vars e_s')) in
    log_rel_subst_l free ltac:(fun _ =>
        simpl; simpl_subst;
        iApply gen_log_rel_closed; [apply empty_union_L; split; solve_is_closed|])
  end.

Section log_rel_structural.
  Context `{!sheapGS Σ} `{!sheapInv Σ}.
  Context (loc_rel : loc → loc → iProp Σ).
  Context (thread_own : thread_id → iProp Σ).
  Context (expr_head_wf : expr_head → Prop).
  Let log_rel := gen_log_rel loc_rel thread_own.

  (** [log_rel_structural] is the main theorem one wants to prove. It
  implies the reflexivity theorem for expressions, evaluation contexts
  and general contexts.

  The theorem says that for any expressions with equal heads and related
  immediate subexpressions, the expressions themselves must also be related.
   *)
  Definition log_rel_structural : Prop := (∀ e_t e_s,
     let head_t := expr_split_head e_t in
     let head_s := expr_split_head e_s in
     expr_head_wf head_s.1 →
     head_s.1 = head_t.1 →
     ([∗list] e_t';e_s' ∈ head_t.2; head_s.2, log_rel e_t' e_s') -∗
     log_rel e_t e_s).

  Theorem gen_log_rel_refl e :
    log_rel_structural →
    gen_expr_wf expr_head_wf e →
    ⊢ log_rel e e.
  Proof.
    intros He Hwf.
    iInduction e as [ ] "IH" forall (Hwf); destruct Hwf; iApply He; try done; simpl.
    all: try iDestruct ("IH" with "[%]") as "$".
    all: try iDestruct ("IH1" with "[%]") as "$".
    all: try iDestruct ("IH2" with "[%]") as "$".
    all: naive_solver.
  Qed.

  Theorem gen_log_rel_ectx K e_t e_s :
    log_rel_structural →
    gen_ectx_wf expr_head_wf K →
    log_rel e_t e_s -∗
    log_rel (fill K e_t) (fill K e_s).
  Proof.
    intros He Hwf. iInduction (K) as [ | Ki K] "IH" using rev_ind; first by eauto.
    iIntros "Hrel".
    rewrite ->gen_ectx_wf_snoc in Hwf. destruct Hwf as [Kwf [Hewf Hiwf]].
    iSpecialize ("IH" with "[//] Hrel").
    rewrite !fill_app /=.
    destruct Ki; simpl; iApply He => //=; iFrame "IH".
    all: move: Hiwf; rewrite /= ?Forall_cons ?Forall_nil => Hiwf.
    all: repeat iSplit; try done.
    all: iApply gen_log_rel_refl; [done|].
    all: naive_solver.
  Qed.

  Theorem gen_log_rel_ctx C e_t e_s :
    log_rel_structural →
    gen_ctx_wf expr_head_wf C →
    log_rel e_t e_s -∗
    log_rel (fill_ctx C e_t) (fill_ctx C e_s).
  Proof.
    intros He Hwf. iInduction (C) as [ | Ci C] "IH" using rev_ind; first by eauto.
    iIntros "Hrel".
    rewrite ->gen_ctx_wf_snoc in Hwf. destruct Hwf as [Kwf [Hewf Hiwf]].
    iSpecialize ("IH" with "[//] Hrel").
    rewrite !fill_ctx_app /=.
    destruct Ci; simpl; iApply He => //=; iFrame "IH".
    all: move: Hiwf; rewrite /= ?Forall_cons ?Forall_nil => Hiwf.
    all: repeat iSplit; try done.
    all: iApply gen_log_rel_refl; [done|].
    all: naive_solver.
  Qed.
End log_rel_structural.
