From simuliris.simulation Require Import language lifting.

From simuliris.simplang Require Import lang tactics.


(** * Instances of the [PureExec] class *)
(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Section irreducible.
  (*Lemma case_ctx v e1 e2 e1' K K' :*)
    (*fill K (Case (Val v) e1 e2) = fill (K') e1' → K' ≠ [] → K' = [CaseCtx e1 e2] ++ K.*)
  (*Proof.*)
    (*intros H Hn. revert K H; induction K'. *)
    (*- by destruct Hn.*)
    (*- clear Hn. intros K Heq. *)
      (*destruct K'. { apply (fill_inj K) in Heq. cbn in Heq. destruct a; cbn in Heq; inversion Heq; by subst. } *)
      (*exfalso.*)


  Global Instance irreducible_case v e1 e2 :
    PureIrreducible (¬ ∃ v', v = InjLV v' ∨ v = InjRV v') (Case (Val v) e1 e2).
  Proof.
  Admitted.

  Global Instance irreducible_binop v1 v2 o :
    PureIrreducible (¬ (is_Some $ bin_op_eval o v1 v2)) (BinOp o (Val v1) (Val v2)).
  Proof.
  Admitted.

  Global Instance irreducible_unop v o :
    PureIrreducible (¬ (is_Some $ un_op_eval o v)) (UnOp o (Val v)).
  Proof.
  Admitted.

End irreducible.

Section pure_exec.
  Local Ltac solve_exec_safe := intros; subst; do 2 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_recc f x (erec : expr) :
    PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_pairc (v1 v2 : val) :
    PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injlc (v : val) :
    PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injrc (v : val) :
    PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
    PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
  Proof. unfold AsRecV in *. solve_pure_exec. Qed.

  Global Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
  Proof. solve_pure_exec. Qed.
  (* Higher-priority instance for [EqOp]. *)
  Global Instance pure_eqop v1 v2 :
    PureExec (vals_compare_safe v1 v2) 1
      (BinOp EqOp (Val v1) (Val v2))
      (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
  Proof.
    intros Hcompare.
    cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
    { intros. revert Hcompare. solve_pure_exec. }
    rewrite /bin_op_eval /= decide_True //.
  Qed.

  Global Instance pure_if_true e1 e2 :
    PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.
  Global Instance pure_if_false e1 e2 :
    PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst v1 v2 :
    PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_snd v1 v2 :
    PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl v e1 e2 :
    PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_case_inr v e1 e2 :
    PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
  Proof. solve_pure_exec. Qed.
End pure_exec.
