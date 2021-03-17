From simuliris.simulation Require Import language lifting.

From simuliris.simplang Require Import lang tactics.


(** * Instances of the [PureExec] class *)

Section irreducible.
  Lemma language_to_val_eq e :
    language.to_val e = to_val e.
  Proof.
    rewrite /language.to_val /language.to_class; cbn.
    destruct (to_val e) eqn:Heq.
    - by rewrite (to_val_class _ _ Heq).
    - destruct to_class as [ [] | ] eqn:Heq';
        [ by rewrite (to_class_val _ _ Heq') in Heq | done | done].
  Qed.

  (* TODO: the proofs of these lemmas are completely the same.
    Can we factor this into common LTac/nice lemmas? *)
  Global Instance irreducible_match v x1 e1 x2 e2 :
    PureIrreducible (¬ ∃ v', v = InjLV v' ∨ v = InjRV v') (Match (Val v) x1 e1 x2 e2).
  Proof.
    intros P_s σ_s ϕ e_s' σ_s' Hprim.
    eapply prim_head_step in Hprim as Hhead.
    { inversion Hhead; subst; apply ϕ; eauto. }
    intros K e' Heq Hv. clear Hprim ϕ.
    destruct K as [ | Ki K]; first done.
    { exfalso. induction K as [ | Ki' K IH] in e', Ki, Hv, Heq |-*.
      - destruct Ki; inversion Heq; subst; cbn in *; congruence.
      - eapply IH; first by rewrite Heq.
        rewrite language_to_val_eq. apply fill_item_val_none.
        by rewrite -language_to_val_eq.
    }
  Qed.

  Global Instance irreducible_binop v1 v2 o :
    PureIrreducible (¬ (is_Some $ bin_op_eval o v1 v2)) (BinOp o (Val v1) (Val v2)).
  Proof.
    intros P_s σ_s ϕ e_s' σ_s' Hprim.
    eapply prim_head_step in Hprim as Hhead.
    { inversion Hhead; subst; apply ϕ; eauto. }
    intros K e' Heq Hv. clear Hprim ϕ.
    destruct K as [ | Ki K]; first done.
    { exfalso. induction K as [ | Ki' K IH] in e', Ki, Hv, Heq |-*.
      - destruct Ki; inversion Heq; subst; cbn in *; congruence.
      - eapply IH; first by rewrite Heq.
        rewrite language_to_val_eq. apply fill_item_val_none.
        by rewrite -language_to_val_eq.
    }
  Qed.

  Global Instance irreducible_unop v o :
    PureIrreducible (¬ (is_Some $ un_op_eval o v)) (UnOp o (Val v)).
  Proof.
    intros P_s σ_s ϕ e_s' σ_s' Hprim.
    eapply prim_head_step in Hprim as Hhead.
    { inversion Hhead; subst; apply ϕ; eauto. }
    intros K e' Heq Hv. clear Hprim ϕ.
    destruct K as [ | Ki K]; first done.
    { exfalso. induction K as [ | Ki' K IH] in e', Ki, Hv, Heq |-*.
      - destruct Ki; inversion Heq; subst; cbn in *; congruence.
      - eapply IH; first by rewrite Heq.
        rewrite language_to_val_eq. apply fill_item_val_none.
        by rewrite -language_to_val_eq.
    }
  Qed.

End irreducible.

Section pure_exec.
  Local Ltac solve_exec_safe := intros; subst; do 2 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_pairc (v1 v2 : val) :
    PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injlc (v : val) :
    PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injrc (v : val) :
    PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_iota x (e2 : expr) (v1 : val) :
    PureExec True 1 (Let x (Val v1) e2) (subst' x v1 e2).
  Proof. solve_pure_exec. Qed.

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

  Global Instance pure_match_inl v x1 e1 x2 e2 :
    PureExec True 1 (Match (Val $ InjLV v) x1 e1 x2 e2) (subst' x1 v e1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_match_inr v x1 e1 x2 e2 :
    PureExec True 1 (Match (Val $ InjRV v) x1 e1 x2 e2) (subst' x2 v e2).
  Proof. solve_pure_exec. Qed.
End pure_exec.
