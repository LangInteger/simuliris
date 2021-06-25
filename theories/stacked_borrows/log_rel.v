From simuliris.simulation Require Import slsls lifting.
From simuliris.stacked_borrows Require Import proofmode tactics.
From simuliris.stacked_borrows Require Import parallel_subst primitive_laws wf.
From iris.prelude Require Import options.

(** * Logical relation
 This file defines the top-level "logical relation" which lifts the
 simulation relation (the "expression relation") to open terms.
*)

Section open_rel.
  Context `{!sborGS Σ}.

  (** Well-formed substitutions closing source and target, with [X] denoting the
      free variables. *)
  Definition subst_map_rel (X : gset string) (map : gmap string (result * result)) : iProp Σ :=
    [∗ set] x ∈ X,
      match map !! x with
      | Some (v_t, v_s) => rrel v_t v_s
      | None => False
      end.

  Global Instance subst_map_rel_pers X map :
    Persistent (subst_map_rel X map).
  Proof.
    rewrite /subst_map_rel. apply big_sepS_persistent=>x.
    destruct (map !! x) as [[v_t v_s]|]; apply _.
  Qed.

  Lemma subst_map_rel_lookup {X map} x :
    x ∈ X →
    subst_map_rel X map -∗
    ∃ v_t v_s, ⌜map !! x = Some (v_t, v_s)⌝ ∗ rrel v_t v_s.
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
    rrel v_t v_s -∗
    subst_map_rel X (binder_insert x (v_t, v_s) map).
  Proof.
    iIntros "#Hmap #Hval". destruct x as [|s]; first done. simpl.
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
  Definition log_rel e_t e_s : iProp Σ :=
    □ ∀ π (map : gmap string (result * result)),
      subst_map_rel (free_vars e_t ∪ free_vars e_s) map -∗
      subst_map (fst <$> map) e_t ⪯{π} subst_map (snd <$> map) e_s {{ λ v_t v_s : val bor_lang, rrel v_t v_s }}.

  Lemma log_rel_closed_1 e_t e_s π :
    free_vars e_t ∪ free_vars e_s = ∅ →
    log_rel e_t e_s ⊢
      e_t ⪯{π} e_s {{ λ v_t v_s, rrel v_t v_s }}.
  Proof.
    iIntros (Hclosed) "#Hrel". iSpecialize ("Hrel" $! π ∅).
    rewrite ->!fmap_empty, ->!subst_map_empty.
    rewrite Hclosed. iApply "Hrel". by iApply subst_map_rel_empty.
  Qed.

  Lemma log_rel_closed e_t e_s :
    free_vars e_t ∪ free_vars e_s = ∅ →
    log_rel e_t e_s ⊣⊢
      (□ ∀ π, e_t ⪯{π} e_s {{ λ v_t v_s, rrel v_t v_s }}).
  Proof.
    intros Hclosed. iSplit.
    { iIntros "#Hrel !#" (π). iApply log_rel_closed_1; done. }
    iIntros "#Hsim" (π xs) "!# Hxs".
    rewrite !subst_map_closed //; set_solver.
  Qed.

  (** Substitute away a single variable in an [log_rel].
      Use the [log_rel] tactic below to automatically apply this for all free variables. *)
  Lemma log_rel_subst x e_t e_s :
    (□ ∀ (v_t v_s : result), rrel v_t v_s -∗
      log_rel (subst x v_t e_t) (subst x v_s e_s)) -∗
    log_rel e_t e_s.
  Proof.
    iIntros "#Hsim" (π xs) "!# #Hxs".
    destruct (decide (x ∈ free_vars e_t ∪ free_vars e_s)) as [Hin|Hnotin]; last first.
    { iSpecialize ("Hsim" $! (ValR [☠%S]) (ValR [☠%S])).
      rewrite ->subst_free_vars by set_solver.
      rewrite ->subst_free_vars by set_solver.
      iApply "Hsim"; eauto. rewrite rrel_value_rel. iApply value_rel_poison. }
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

Section log_rel_structural.
  Context `{!sborGS Σ}.
  Context (expr_head_wf : expr_head → Prop).

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

  Theorem log_rel_refl e :
    log_rel_structural →
    gen_expr_wf expr_head_wf e →
    ⊢ log_rel e e.
  Proof.
    intros He Hwf.
    iInduction e as [ ] "IH" using expr_ind forall (Hwf) ; destruct Hwf; iApply He; try done; simpl.
    all: try iDestruct ("IH" with "[%]") as "$".
    all: try iDestruct ("IH1" with "[%]") as "$".
    all: try naive_solver.
    (* [Case] left. *)
  Admitted.

  Theorem log_rel_ectx K e_t e_s :
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
    all: try (iApply log_rel_refl; [naive_solver|]).
    all: try naive_solver.
  Admitted.

  Theorem log_rel_ctx C e_t e_s :
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
    all: try (iApply log_rel_refl; [done|]).
    all: try naive_solver.
    - admit.
    - admit.
    - admit.
  Admitted.

  Corollary sim_refl π m1 m2 e Φ :
    dom (gset _) m1 = dom (gset _) m2 →
    free_vars e ⊆ dom (gset _) m1 →
    log_rel_structural →
    gen_expr_wf expr_head_wf e →
    subst_map_rel (dom _ m1) (map_zip m1 m2) -∗
    (∀ v_t v_s, rrel v_t v_s -∗ Φ (of_result v_t) (of_result v_s)) -∗
    subst_map m1 e ⪯{π} subst_map m2 e [{ Φ }].
  Proof.
    iIntros (Hdom Hfree ??) "Hrel HΦ".
    iApply (sim_expr_wand _ _ _ _ π with "[Hrel]").
    - iPoseProof log_rel_refl as "#Hlog"; [done..|].
      iSpecialize ("Hlog" $! _ (map_zip m1 m2)).
      setoid_rewrite fst_map_zip.
      2: { move => ?. by rewrite -!elem_of_dom Hdom. }
      setoid_rewrite snd_map_zip.
      2: { move => ?. by rewrite -!elem_of_dom Hdom. }
      iApply ("Hlog" with "[Hrel]").
      iApply (subst_map_rel_weaken with "Hrel"). set_solver.
    - iIntros (e_t e_s) "(%v_t & %v_s & -> & -> & Hv)". by iApply "HΦ".
  Qed.

End log_rel_structural.
