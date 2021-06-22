From stdpp Require Export gmap.
From simuliris.simplang Require Export lang notation.


(** * Parallel substitution for SimpLang *)
(** Definitions and proofs mostly yoinked from https://gitlab.mpi-sws.org/FP/stacked-borrows/-/blob/master/theories/lang/subst_map.v *)

Fixpoint subst_map (xs : gmap string val) (e : expr) : expr :=
  match e with
  | Var y => if xs !! y is Some v then Val v else Var y
  | Val v => Val v
  | GlobalVar n => GlobalVar n
  | Let x1 e1 e2 => Let x1 (subst_map xs e1) (subst_map (binder_delete x1 xs) e2)
  | UnOp op e => UnOp op (subst_map xs e)
  | BinOp op e1 e2 => BinOp op (subst_map xs e1) (subst_map xs e2)
  | If e0 e1 e2 => If (subst_map xs e0) (subst_map xs e1) (subst_map xs e2)
  | While e0 e1 => While (subst_map xs e0) (subst_map xs e1)
  | Pair e1 e2 => Pair (subst_map xs e1) (subst_map xs e2)
  | Fst e => Fst (subst_map xs e)
  | Snd e => Snd (subst_map xs e)
  | InjL e => InjL (subst_map xs e)
  | InjR e => InjR (subst_map xs e)
  | Match e0 x1 e1 x2 e2 => Match (subst_map xs e0) x1 (subst_map (binder_delete x1 xs) e1)
      x2 (subst_map (binder_delete x2 xs) e2)
  | Fork e => Fork (subst_map xs e)
  | AllocN e1 e2 => AllocN (subst_map xs e1) (subst_map xs e2)
  | FreeN e1 e2 => FreeN (subst_map xs e1) (subst_map xs e2)
  | Load o e => Load o (subst_map xs e)
  | Store o e1 e2 => Store o (subst_map xs e1) (subst_map xs e2)
  | CmpXchg e0 e1 e2 => CmpXchg (subst_map xs e0) (subst_map xs e1) (subst_map xs e2)
  | FAA e1 e2 => FAA (subst_map xs e1) (subst_map xs e2)
  | Call e1 e2 => Call (subst_map xs e1) (subst_map xs e2)
  end.

Lemma subst_map_empty e :
  subst_map ∅ e = e.
Proof.
  induction e; simpl; f_equal; eauto.
  all: match goal with |- context[binder_delete ?x ∅] => destruct x; first done end.
  all: simpl; rewrite delete_empty; done.
Qed.

Lemma subst_map_subst map x (v : val) (e : expr) :
  subst_map map (subst x v e) = subst_map (<[x:=v]>map) e.
Proof.
  revert x v map; induction e; intros xx r map; simpl;
  try (f_equal; eauto).
  all: try match goal with |- context[binder_delete ?x _] => destruct x; simpl; first done end.
  - case_decide.
    + simplify_eq/=. by rewrite lookup_insert.
    + rewrite lookup_insert_ne; done.
  - case_decide.
    + rewrite delete_insert_ne; last by congruence. done.
    + simplify_eq/=. by rewrite delete_insert_delete.
  - case_decide.
    + rewrite delete_insert_ne; last by congruence. done.
    + simplify_eq/=. by rewrite delete_insert_delete.
  - case_decide.
    + rewrite delete_insert_ne; last by congruence. done.
    + simplify_eq/=. by rewrite delete_insert_delete.
Qed.

Lemma subst_subst_map x (v : val) map e :
  subst x v (subst_map (delete x map) e) =
  subst_map (<[x:=v]>map) e.
Proof.
  revert map v x; induction e; intros map v0 xx; simpl;
  try (f_equal; eauto).
  all: try match goal with |- context[binder_delete ?x _] => destruct x; simpl; first by auto end.
  - match goal with |- context[delete _ _ !! ?s] => rename s into x end.
    destruct (decide (xx=x)) as [->|Hne].
    + rewrite lookup_delete // lookup_insert //. simpl.
      rewrite decide_True //.
    + rewrite lookup_delete_ne // lookup_insert_ne //.
      destruct (map !! x) as [rr|].
      * by destruct rr.
      * simpl. rewrite decide_False //.
  - case_decide.
    + rewrite delete_insert_ne //; last congruence. rewrite delete_commute. eauto.
    + simplify_eq. rewrite delete_idemp delete_insert_delete. done.
  - case_decide.
    + rewrite delete_insert_ne //; last congruence. rewrite delete_commute. eauto.
    + simplify_eq. rewrite delete_idemp delete_insert_delete. done.
  - case_decide.
    + rewrite delete_insert_ne //; last congruence. rewrite delete_commute. eauto.
    + simplify_eq. rewrite delete_idemp delete_insert_delete. done.
Qed.

Lemma subst'_subst_map b (v : val) map e :
  subst' b v (subst_map (binder_delete b map) e) =
  subst_map (binder_insert b v map) e.
Proof.
  destruct b; first done.
  exact: subst_subst_map.
Qed.

Lemma subst_map_subst_map xs ys e :
  subst_map xs (subst_map ys e) = subst_map (ys ∪ xs) e.
Proof.
  revert e.
  induction ys as [|x v ys HNone IH] using map_ind => e.
  { by rewrite left_id subst_map_empty. }
  by rewrite -insert_union_l -[in X in _ = X]subst_map_subst -IH subst_map_subst.
Qed.

(** "Free variables" and their interaction with subst_map *)
Local Definition binder_to_ctx (x : binder) : gset string :=
  if x is BNamed s then {[s]} else ∅.

Fixpoint free_vars (e : expr) : gset string :=
  match e with
  | Val v => ∅
  | GlobalVar n => ∅
  | Var x => {[x]}
  | Let x e1 e2 => free_vars e1 ∪ (free_vars e2 ∖ binder_to_ctx x)
  | Match e0 x1 e1 x2 e2 =>
    free_vars e0 ∪
    (free_vars e1 ∖ binder_to_ctx x1) ∪
    (free_vars e2 ∖ binder_to_ctx x2)
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Load _ e =>
     free_vars e
  | Call e1 e2 | While e1 e2 | BinOp _ e1 e2 | Pair e1 e2
  | AllocN e1 e2 | FreeN e1 e2 | Store _ e1 e2 | FAA e1 e2 =>
     free_vars e1 ∪ free_vars e2
  | If e0 e1 e2 | CmpXchg e0 e1 e2 =>
     free_vars e0 ∪ free_vars e1 ∪ free_vars e2
  end.

(* Just fill with any value, it does not make a difference. *)
Definition free_vars_ectx (K : ectx) : gset string :=
  free_vars (fill K #()).

Local Lemma binder_delete_eq x y (xs1 xs2 : gmap string val) :
  (if y is BNamed s then s ≠ x → xs1 !! x = xs2 !! x else xs1 !! x = xs2 !! x) →
  binder_delete y xs1 !! x = binder_delete y xs2 !! x.
Proof.
  destruct y as [|s]; first done. simpl.
  destruct (decide (s = x)) as [->|Hne].
  - rewrite !lookup_delete //.
  - rewrite !lookup_delete_ne //. eauto.
Qed.

Lemma subst_map_free_vars (xs1 xs2 : gmap string val) (e : expr) :
  (∀ x, x ∈ free_vars e → xs1 !! x = xs2 !! x) →
  subst_map xs1 e = subst_map xs2 e.
Proof.
  revert xs1 xs2; induction e=>/= xs1 xs2 Heq;
  solve [
    (* trivial cases *)
    done
  | (* variable case *)
    rewrite Heq; [done|set_solver]
  | (* recursive cases *)
    f_equal;
    repeat lazymatch goal with x : binder |- _ => destruct x end;
    intuition eauto using binder_delete_eq with set_solver
  ].
Qed.

Lemma subst_map_closed xs e :
  free_vars e = ∅ →
  subst_map xs e = e.
Proof.
  intros Hclosed.
  trans (subst_map ∅ e).
  - apply subst_map_free_vars. rewrite Hclosed. done.
  - apply subst_map_empty.
Qed.

Lemma subst_free_vars x v e :
  x ∉ free_vars e →
  subst x v e = e.
Proof.
  intros Hfree.
  rewrite -(subst_map_empty (subst x v e)).
  rewrite subst_map_subst.
  rewrite (subst_map_free_vars _ ∅); first by apply subst_map_empty.
  intros y ?. rewrite lookup_insert_ne //. set_solver.
Qed.

Lemma free_vars_subst x v e :
  free_vars (subst x v e) = free_vars e ∖ {[x]}.
Proof.
  induction e=>/=; repeat case_decide; set_solver.
Qed.

Lemma free_vars_subst_map xs e :
  free_vars (subst_map xs e) = free_vars e ∖ (dom _ xs).
Proof.
  induction xs as [| x v xs HNone IH] using map_ind.
  - rewrite subst_map_empty. set_solver.
  - rewrite -subst_subst_map delete_notin // free_vars_subst IH. set_solver.
Qed.

Lemma free_vars_fill K e :
  free_vars (fill K e) = free_vars_ectx K ∪ free_vars e.
Proof.
  revert e. induction K as [|Ki K IH] using rev_ind; intros e; simpl.
  { simpl. rewrite /free_vars_ectx /= left_id_L. done. }
  rewrite /free_vars_ectx !fill_app /=. destruct Ki; simpl.
  all: rewrite !IH; set_solver+.
Qed.
