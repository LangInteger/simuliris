From stdpp Require Import gmap.
From simuliris.simulation Require Import language lifting.
From simuliris.simplang Require Export lang.
From simuliris.simplang Require Import tactics.

(** * Instances of the [IrredUnless] class *)

Section irreducible.
  Implicit Types (e : expr) (v : val) (σ : state).

  Lemma language_to_val_eq e :
    language.to_val e = to_val e.
  Proof.
    rewrite /language.to_val /language.to_class; cbn.
    destruct (to_val e) eqn:Heq.
    - by rewrite (to_val_class _ _ Heq).
    - destruct to_class as [ [] | ] eqn:Heq';
        [ by rewrite (to_class_val _ _ Heq') in Heq | done | done].
  Qed.
End irreducible.

Ltac solve_sub_redexes_are_values :=
  let K := fresh "K" in
  let e' := fresh "e'" in
  let Heq := fresh "Heq" in
  let Hv := fresh "Hv" in
  let IH := fresh "IH" in
  let Ki := fresh "Ki" in
  let Ki' := fresh "Ki'" in
  intros K e' Heq Hv;
  destruct K as [ | Ki K]; first (done);
  exfalso; induction K as [ | Ki' K IH] in e', Ki, Hv, Heq |-*;
  [destruct Ki; inversion Heq; subst; cbn in *; congruence
  | eapply IH; first (by rewrite Heq);
    rewrite language_to_val_eq; apply fill_item_val_none;
      by rewrite -language_to_val_eq].

Section irreducible.
  Implicit Types (e : expr) (v : val) (σ : state).

  (* slightly hacky proof tactic for irreducibility, solving goals of the form [SIrreducible _ _ _ _].
    Basically the same proof script works for all these proofs, but there don't seem to be nice more general lemmas. *)
  Ltac prove_irred :=
    let P_s := fresh "P_s" in
    let σ_s := fresh "σ_s" in
    let ϕ := fresh "ϕ" in
    let e_s' := fresh "e_s'" in
    let σ_s' := fresh "σ_s'" in
    let Hhead := fresh "Hhead" in
    intros ϕ e_s' σ_s' efs Hhead%prim_head_step;
    [ (*this need not complete the proof and may generate a proof obligation *)
      inversion Hhead; subst; try by (apply ϕ; eauto)
    | solve_sub_redexes_are_values
    ].

  (** Tactic support for proving goals of the form [IrredUnless] by
    applying the lemma [irred_unless_irred_dec], using [prove_irred],
    and using ad-hoc automation for solving the [Decision] goal. *)
  Ltac discr :=
    repeat match goal with
           | H : ∃ _, _ |- _ => destruct H
           | H: _ ∨ _ |- _ => destruct H
           | H : _ ∧ _ |- _ => destruct H
           end; congruence.

  Ltac decide_goal :=
    try apply _;
    repeat match goal with
           | |- Decision (_ ∧ _) => apply and_dec
           | |- Decision (_ ∨ _) => apply or_dec
           | |- Decision (is_Some _) => apply is_Some_dec
           | |- Decision False => apply False_dec
           | |- Decision True => apply True_dec
           end;
    try match goal with
    | v : val |- _ =>
        match goal with
        | |- context[v] => destruct v as [[] | | | ]
        end
    end; rewrite /Decision; first [left; by eauto | right; intros ?; discr ].

  Ltac prove_irred_unless := apply irred_unless_irred_dec; [decide_goal | prove_irred].

  Global Instance irred_unless_match v x1 e1 x2 e2 P σ :
    IrredUnless (∃ v', v = InjLV v' ∨ v = InjRV v') P (Match (Val v) x1 e1 x2 e2) σ.
  Proof. prove_irred_unless. Qed.

  (** for operators, we provide specialized instances for each operator. *)
  Ltac solve_binop v1 v2 :=
    unfold bin_op_eval in *;
    case_decide; try congruence;
    destruct v1 as [[] | | |]; destruct v2 as [[] | | |]; cbn in *;
        try congruence;
        repeat match goal with
        | H: _ ∨ _ |- _ => destruct H
        | H : _ ∧ _ |- _ => destruct H
        end; eauto 8.
  Ltac solve_unop v :=
    unfold un_op_eval in *;
    try congruence;
    destruct v as [[] | | |]; cbn in *;
        try congruence;
        repeat match goal with
        | H: _ ∨ _ |- _ => destruct H
        | H : _ ∧ _ |- _ => destruct H
        end; eauto 8.

  Global Instance irreducible_plus v1 v2 P σ :
    IrredUnless ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp PlusOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless; solve_binop v1 v2. Qed.
  Global Instance irreducible_minus v1 v2 P σ :
    IrredUnless ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp MinusOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless; solve_binop v1 v2. Qed.
  Global Instance irreducible_rem v1 v2 P σ :
    IrredUnless ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp RemOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. solve_binop v1 v2. Qed.
  Global Instance irreducible_mult v1 v2 P σ :
    IrredUnless ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp MultOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. solve_binop v1 v2. Qed.
  Global Instance irreducible_quot v1 v2 P σ :
    IrredUnless ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp QuotOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. solve_binop v1 v2. Qed.

  Global Instance irreducible_and v1 v2 P σ :
    IrredUnless (((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n)) ∨ ((∃ b, v1 = LitV $ LitBool b) ∧ ∃ b, v2 = LitV $ LitBool b))%V
      P (BinOp AndOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. solve_binop v1 v2. Qed.
  Global Instance irreducible_or v1 v2 P σ :
    IrredUnless (((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n)) ∨ ((∃ b, v1 = LitV $ LitBool b) ∧ ∃ b, v2 = LitV $ LitBool b))%V
      P (BinOp OrOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. solve_binop v1 v2. Qed.
  Global Instance irreducible_xor v1 v2 P σ :
    IrredUnless (((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n)) ∨ ((∃ b, v1 = LitV $ LitBool b) ∧ ∃ b, v2 = LitV $ LitBool b))%V
      P (BinOp XorOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. solve_binop v1 v2. Qed.

  Global Instance irreducible_shiftl v1 v2 P σ :
    IrredUnless ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp ShiftLOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. solve_binop v1 v2. Qed.
  Global Instance irreducible_shiftr v1 v2 P σ :
    IrredUnless ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp ShiftROp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. solve_binop v1 v2. Qed.

  Global Instance irreducible_le v1 v2 P σ :
    IrredUnless ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp LeOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. solve_binop v1 v2. Qed.
  Global Instance irreducible_ge v1 v2 P σ :
    IrredUnless ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp LtOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. solve_binop v1 v2. Qed.

  Global Instance irreducible_offset v1 v2 P σ :
    IrredUnless ((∃ l, v1 = LitV $ LitLoc l) ∧ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp OffsetOp  (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. solve_binop v1 v2. Qed.

  Global Instance irreducible_eq v1 v2 P σ :
    IrredUnless (vals_compare_safe v1 v2)%V
      P (BinOp EqOp (Val v1) (Val v2)) σ.
  Proof.
    apply irred_unless_irred_dec; first by apply _.
    prove_irred.
    unfold bin_op_eval in *;
    case_decide; last congruence.
    case_decide; congruence.
  Qed.

  Global Instance irreducible_neg v P σ :
    IrredUnless ((∃ n, v = LitV $ LitInt n) ∨ (∃ b, v = LitV $ LitBool b)) P (UnOp NegOp (Val v)) σ.
  Proof. prove_irred_unless. solve_unop v. Qed.
  Global Instance irreducible_un_minus v P σ :
    IrredUnless (∃ n, v = LitV $ LitInt n) P (UnOp MinusUnOp (Val v)) σ.
  Proof. prove_irred_unless. solve_unop v. Qed.

  Global Instance irreducible_var (x : string) P σ :
    IrredUnless False P (Var x) σ.
  Proof. prove_irred_unless. Qed.

  Global Instance irreducible_global_var (x : string) P σ :
    IrredUnless (x ∈ σ.(globals)) P (GlobalVar x) σ.
  Proof. prove_irred_unless. Qed.

  Global Instance irreducible_call v v2 P σ :
    IrredUnless (∃ fn, v = LitV $ LitFn fn) P (Call (Val v) (Val v2)) σ.
  Proof. prove_irred_unless. Qed.

  Global Instance irreducible_if v e1 e2 P σ :
    IrredUnless (∃ b, v = LitV $ LitBool b) P (If (Val v) e1 e2) σ.
  Proof. prove_irred_unless. Qed.

  Global Instance irreducible_fst v P σ :
    IrredUnless (∃ v1 v2, v = PairV v1 v2) P (Fst (Val v)) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irreducible_snd v P σ :
    IrredUnless (∃ v1 v2, v = PairV v1 v2) P (Snd (Val v)) σ.
  Proof. prove_irred_unless. Qed.

  Global Instance irreducible_loadSc σ v_l P :
    IrredUnless (∃ l v n, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt n, v)) P (Load ScOrd $ Val v_l) σ.
  Proof.
    apply irred_unless_irred_dec; last by prove_irred.
    destruct v_l as [[ | | | |l| ] | | |]; try decide_goal.
    destruct (heap σ !! l) as [ [[] ] | ] eqn:Heq; decide_goal.
  Qed.
  Global Instance irreducible_loadNa1 σ v_l P :
    IrredUnless (∃ l v n, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt n, v)) P (Load Na1Ord $ Val v_l) σ.
  Proof.
    apply irred_unless_irred_dec; last by prove_irred.
    destruct v_l as [[ | | | |l| ] | | |]; try decide_goal.
    destruct (heap σ !! l) as [ [[] ] | ] eqn:Heq; decide_goal.
  Qed.
  Global Instance irreducible_loadNa2 σ v_l P :
    IrredUnless (∃ l v n, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt (S n), v)) P (Load Na2Ord $ Val v_l) σ.
  Proof.
    apply irred_unless_irred_dec; last by prove_irred.
    destruct v_l as [[ | | | |l| ] | | |]; try decide_goal.
    destruct (heap σ !! l) as [ [[ | []] ] | ] eqn:Heq; decide_goal.
  Qed.

  Global Instance irreducible_storeSc σ v_l P (v : val) :
    IrredUnless (∃ l v, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt 0, v)) P (Store ScOrd (Val $ v_l) (Val v)) σ.
  Proof.
    apply irred_unless_irred_dec; last by prove_irred.
    destruct v_l as [[ | | | |l| ] | | |]; try decide_goal.
    destruct (heap σ !! l) as [ [[ | [] ] ] | ] eqn:Heq; decide_goal.
  Qed.
  Global Instance irreducible_storeNa1 σ v_l P (v : val) :
    IrredUnless (∃ l v, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt 0, v)) P (Store Na1Ord (Val $ v_l) (Val v)) σ.
  Proof.
    apply irred_unless_irred_dec; last by prove_irred.
    destruct v_l as [[ | | | |l| ] | | |]; try decide_goal.
    destruct (heap σ !! l) as [ [[ | [] ] ] | ] eqn:Heq; decide_goal.
  Qed.
  Global Instance irreducible_storeNa2 σ v_l P (v : val) :
    IrredUnless (∃ l v, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (WSt, v)) P (Store Na2Ord (Val $ v_l) (Val v)) σ.
  Proof.
    apply irred_unless_irred_dec; last by prove_irred.
    destruct v_l as [[ | | | |l| ] | | |]; try decide_goal.
    destruct (heap σ !! l) as [ [[ |  ] ] | ] eqn:Heq; decide_goal.
  Qed.
  Global Instance irreducible_freeN σ v_l v_n P :
    IrredUnless (∃ l n, v_l = LitV $ LitLoc l ∧ v_n = LitV $ LitInt n ∧ (0 < n)%Z ∧ block_is_dyn l.(loc_block) ∧
                       (∀ m : Z, is_Some (heap σ !! (l +ₗ m)) ↔ (0 ≤ m < n)%Z))
      P (FreeN (Val v_n) (Val v_l)) σ.
  Proof.
    apply irred_unless_irred_dec; last (prove_irred; by eauto 8).
    destruct v_l as [[ | | | |l| ] | | |]; try decide_goal.
    destruct v_n as [[n | | | | | ]  | | | ]; try decide_goal.
    apply (exists_dec_unique l); [ naive_solver|].
    apply (exists_dec_unique n); [ naive_solver|].
    apply and_dec; [decide_goal|].
    apply and_dec; [decide_goal|].
    apply and_dec; [apply _|].
    apply and_dec; [apply _|].
    apply forall_equiv_dec.
    - destruct (decide (map_Forall (λ l' _,
       (loc_block l' = loc_block l → loc_idx l ≤ loc_idx l' < loc_idx l + n)%Z
                                   ) σ.(heap))) as [Hm|Hm]; last first.
      + right. contradict Hm. apply map_Forall_lookup_2 => i ? Hheap ? /=.
        have Hi : i = (l +ₗ (loc_idx i - loc_idx l)).
        { rewrite /loc_add. destruct i, l => /=; f_equal; [ done | lia]. }
        rewrite Hi in Hheap. eapply mk_is_Some, Hm in Hheap. lia.
      + left. intros m (x & Hsome).
        specialize (map_Forall_lookup_1 _ _ _ _ Hm Hsome eq_refl).
        destruct l; simpl; lia.
    - destruct (decide (n > 0)%Z) as [Hn|]; first last. { left. intros m ?. lia. }
      replace n with (Z.of_nat (Z.to_nat n)) by lia. generalize (Z.to_nat n) as n'. clear n Hn.
      intros n. induction n as [ | n IH]. { left. lia. }
      destruct (σ.(heap) !! (l +ₗ n)) eqn:Hn; first last.
      { right. intros Ha. specialize (Ha n ltac:(lia)). move: Ha. rewrite Hn. intros (? & [=]). }
      destruct IH as [IH | IH].
      + left. intros m Hm. destruct (decide (Z.of_nat n = m)) as [<- | Hneq]; first by eauto.
        apply IH. lia.
      + destruct (decide (0 < n)) as [Hgt | Hlt].
        * right. contradict IH. intros m Hm. apply IH. lia.
        * left. intros m Hm. replace m with (Z.of_nat n) by lia. eauto.
  Qed.

  Global Instance irreducible_allocN σ v_n v P :
    IrredUnless (∃ n, v_n = LitV $ LitInt n ∧ (0 < n)%Z) P (AllocN (Val v_n) (Val v)) σ.
  Proof.
    apply irred_unless_irred_dec; last prove_irred.
    destruct v_n as [[n | | | | | ] | | |]; try decide_goal.
    assert (Decision (0 < n)%Z) as [ | ] by apply _.
    - left. eauto.
    - right. intros (n' & [= <-] & Hn'); lia.
  Qed.

  Global Instance irreducible_storeScNa1 o σ v_l P (v : val) `{!TCFastDone (o ≠ Na2Ord)} :
    IrredUnless (∃ l v, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt 0, v)) P (Store o (Val $ v_l) (Val v)) σ.
  Proof. unfold TCFastDone in *. destruct o; try done; apply _. Qed.
  Global Instance irreducible_loadScNa1 o σ v_l P `{!TCFastDone (o ≠ Na2Ord)}:
    IrredUnless (∃ l v n, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt n, v)) P (Load o $ Val v_l) σ.
  Proof. unfold TCFastDone in *. destruct o; try done; apply _. Qed.

  (** for the usual use case with [sim_irred_unless], we will not actually have the state and program
    in context, thus the application of the above instances will fail.
    Therefore, we provide weaker instances for these cases.
   *)
  Global Instance irreducible_load_weak σ v_l o P :
    IrredUnless (∃ l, v_l = LitV $ LitLoc l) P (Load o $ Val v_l) σ | 10.
  Proof.
    destruct o; (eapply irred_unless_weaken; last (by apply _);
      intros (l & v & ? & ? &?); eauto).
  Qed.
  Global Instance irreducible_store_weak σ v_l o P (v : val) :
    IrredUnless (∃ l, v_l = LitV $ LitLoc l) P (Store o (Val $ v_l) (Val v)) σ | 10.
  Proof.
    destruct o; (eapply irred_unless_weaken; last (by apply _);
      intros (l & ? & ? & ?); eauto).
  Qed.
  Global Instance irreducible_freeN_weak σ v_l v_n P :
    IrredUnless (∃ l n, v_l = LitV $ LitLoc l ∧ v_n = LitV $ LitInt n ∧ (0 < n)%Z ∧ block_is_dyn l.(loc_block)) P (FreeN (Val v_n) (Val v_l)) σ | 10.
  Proof.
    eapply irred_unless_weaken; last apply irreducible_freeN.
    intros (l & ? & ? & ? &? &? &?); eauto 8.
  Qed.
End irreducible.


(** * Instances of the [PureExec] class *)
Section pure_exec.
  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
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
  Lemma pure_while e0 e1 :
    PureExec True 1 (While e0 e1) (If e0 (e1 ;; While e0 e1) (Val $ LitV $ LitUnit)).
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
