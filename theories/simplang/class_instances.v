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

  (* slightly hacky proof tactic for irreducibility.
    basically the same proof script works for all these proofs, but there don't seem to be nice more general lemmas *)
  Ltac prove_irred :=
    let P_s := fresh "P_s" in
    let σ_s := fresh "σ_s" in
    let ϕ := fresh "ϕ" in
    let e_s' := fresh "e_s'" in
    let σ_s' := fresh "σ_s'" in
    let Hhead := fresh "Hhead" in
    let K := fresh "K" in
    let e' := fresh "e'" in
    let Heq := fresh "Heq" in
    let Hv := fresh "Hv" in
    let IH := fresh "IH" in
    let Ki := fresh "Ki" in
    let Ki' := fresh "Ki'" in
    intros ϕ e_s' σ_s' Hhead%prim_head_step;
    [inversion Hhead; subst; try by (apply ϕ; eauto)
    | intros K e' Heq Hv; clear ϕ;
      destruct K as [ | Ki K]; first (done);
      exfalso; induction K as [ | Ki' K IH] in e', Ki, Hv, Heq |-*;
      [destruct Ki; inversion Heq; subst; cbn in *; congruence
      | eapply IH; first (by rewrite Heq);
        rewrite language_to_val_eq; apply fill_item_val_none;
        by rewrite -language_to_val_eq]
    ].

  Global Instance irreducible_match v x1 e1 x2 e2 P σ :
    SIrreducible (¬ ∃ v', v = InjLV v' ∨ v = InjRV v') P (Match (Val v) x1 e1 x2 e2) σ.
  Proof. prove_irred. Qed.

  (** for binary operators, we provide specialized instances for each operator.
    (the full search space is otherwise too large when doing a case analysis over
     the values on both sides to decide whether an expression is stuck or not)
   *)
  Ltac solve_binop v1 v2 :=
    unfold bin_op_eval in *;
    case_decide; try congruence;
    destruct v1 as [[] | | |]; destruct v2 as [[] | | |]; cbn in *;
        try congruence;
        repeat match goal with
        | H: _ ∨ _ |- _ => destruct H
        | H : _ ∧ _ |- _ => destruct H
        end; eauto 8.

  Global Instance irreducible_plus v1 v2 P σ :
    SIrreducible (¬ (∃ n, v1 = LitV $ LitInt n) ∨ ¬ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp PlusOp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.
  Global Instance irreducible_minus v1 v2 P σ :
    SIrreducible (¬ (∃ n, v1 = LitV $ LitInt n) ∨ ¬ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp MinusOp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.
  Global Instance irreducible_rem v1 v2 P σ :
    SIrreducible (¬ (∃ n, v1 = LitV $ LitInt n) ∨ ¬ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp RemOp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.
  Global Instance irreducible_mult v1 v2 P σ :
    SIrreducible (¬ (∃ n, v1 = LitV $ LitInt n) ∨ ¬ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp MultOp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.
  Global Instance irreducible_quot v1 v2 P σ :
    SIrreducible (¬ (∃ n, v1 = LitV $ LitInt n) ∨ ¬ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp QuotOp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.

  Global Instance irreducible_and v1 v2 P σ :
    SIrreducible (¬ (((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n)) ∨ ((∃ b, v1 = LitV $ LitBool b) ∧ ∃ b, v2 = LitV $ LitBool b)))%V
      P (BinOp AndOp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.
  Global Instance irreducible_or v1 v2 P σ :
    SIrreducible (¬ (((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n)) ∨ ((∃ b, v1 = LitV $ LitBool b) ∧ ∃ b, v2 = LitV $ LitBool b)))%V
      P (BinOp OrOp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.
  Global Instance irreducible_xor v1 v2 P σ :
    SIrreducible (¬ (((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n)) ∨ ((∃ b, v1 = LitV $ LitBool b) ∧ ∃ b, v2 = LitV $ LitBool b)))%V
      P (BinOp XorOp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.

  Global Instance irreducible_shiftl v1 v2 P σ :
    SIrreducible ((¬ (∃ n, v1 = LitV $ LitInt n)) ∨ (¬ (∃ n, v2 = LitV $ LitInt n)))%V
      P (BinOp ShiftLOp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.
  Global Instance irreducible_shiftr v1 v2 P σ :
    SIrreducible ((¬ (∃ n, v1 = LitV $ LitInt n)) ∨ (¬ (∃ n, v2 = LitV $ LitInt n)))%V
      P (BinOp ShiftROp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.

  Global Instance irreducible_le v1 v2 P σ :
    SIrreducible (¬ (∃ n, v1 = LitV $ LitInt n) ∨ ¬ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp LeOp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.
  Global Instance irreducible_ge v1 v2 P σ :
    SIrreducible (¬ (∃ n, v1 = LitV $ LitInt n) ∨ ¬ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp LtOp (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.

  Global Instance irreducible_offset v1 v2 P σ :
    SIrreducible (¬ (∃ l, v1 = LitV $ LitLoc l) ∨ ¬ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp OffsetOp  (Val v1) (Val v2)) σ.
  Proof. prove_irred. solve_binop v1 v2. Qed.

  Global Instance irreducible_eq v1 v2 P σ :
    SIrreducible (¬ vals_compare_safe v1 v2)%V
      P (BinOp EqOp (Val v1) (Val v2)) σ.
  Proof.
    prove_irred.
    unfold bin_op_eval in *;
    case_decide; last congruence.
    case_decide; congruence.
  Qed.

  Global Instance irreducible_unop v o P σ :
    SIrreducible (¬ (is_Some $ un_op_eval o v)) P (UnOp o (Val v)) σ.
  Proof. prove_irred. Qed.

  Global Instance irreducible_var (x : string) P σ :
    SIrreducible (True) P (Var x) σ.
  Proof. prove_irred. Qed.

  Global Instance irreducible_call v v2 P σ :
    SIrreducible (¬ ∃ fn, v = LitV $ LitFn fn) P (Call (Val v) (Val v2)) σ.
  Proof. prove_irred. Qed.

  Global Instance irreducible_if v e1 e2 P σ :
    SIrreducible (¬ ∃ b, v = LitV $ LitBool b) P (If (Val v) e1 e2) σ.
  Proof. prove_irred. Qed.

  Global Instance irreducible_fst v P σ :
    SIrreducible (¬ ∃ v1 v2, v = PairV v1 v2) P (Fst (Val v)) σ.
  Proof. prove_irred. Qed.
  Global Instance irreducible_snd v P σ :
    SIrreducible (¬ ∃ v1 v2, v = PairV v1 v2) P (Snd (Val v)) σ.
  Proof. prove_irred. Qed.

  Global Instance irreducible_load σ l P :
    SIrreducible (¬ ∃ v, heap σ !! l = Some (Some v)) P (Load $ Val $ LitV $ LitLoc l) σ.
  Proof. prove_irred. Qed.
  Global Instance irreducible_store σ l P (v : val) :
    SIrreducible (¬ ∃ v, heap σ !! l = Some (Some v)) P (Store (Val $ LitV $ LitLoc l) (Val v)) σ.
  Proof. prove_irred. Qed.
  Global Instance irreducible_free σ l P :
    SIrreducible (¬ ∃ v, heap σ !! l = Some (Some v)) P (Free $ Val $ LitV $ LitLoc l) σ.
  Proof. prove_irred. Qed.
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
