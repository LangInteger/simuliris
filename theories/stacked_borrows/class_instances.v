From simuliris.simulation Require Import language lifting.
From simuliris.stacked_borrows Require Export lang.
From simuliris.stacked_borrows Require Import tactics.



(** * Instances of the [PureExec] class *)
Section pure_exec.
  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; do 2 econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; inv_head_step; try done.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].


  (*pure_expr_step*)
  Global Instance pure_iota_val x (e2 : expr) (v1 : value) :
    PureExec True 1 (Let x (Val v1) e2) (subst' x (Val v1) e2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_iota_place x (e2 : expr) l t T :
    PureExec True 1 (Let x (Place l t T) e2) (subst' x (PlaceR l t T) e2).
  Proof. solve_pure_exec. Qed.

  (* TODO: binop evaluation is not pure, due to the semantics of comparing unallocated heap locations.
    What is the reason why the semantics was chosen that way?
    Can we make that nicer? (BinOp evaluation should really be pure... it's absurd that that needs to access the heap)
  *)
  (*Global Instance pure_binop h op l1 l2 l' :*)
    (*PureExec (bin_op_eval h op l1 l2 l') 1 (BinOp op (Val [l1]) (Val [l2])) (Val [l']) | 10.*)
  (*Proof. solve_pure_exec. Qed.*)

  Global Instance pure_proj v i s :
    PureExec (0 ≤ i ∧ v !! (Z.to_nat i) = Some s) 1 (Proj (Val (v : list scalar)) (#[ScInt i])) (#[s]).
  Proof. solve_pure_exec. destruct H, DEFINED; rewrite H2 in H0. naive_solver. Qed.
  Global Instance pure_conc v1 v2 :
    PureExec True 1 (Conc #v1 #v2) (#(v1 ++ v2)).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_ref l t T :
    PureExec True 1 (Ref (Place l t T)) (#[ScPtr l t]).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_deref l t T :
    PureExec True 1 (Deref (#[ScPtr l t]) T) (Place l t T).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_case i el e :
    PureExec (0 ≤ i ∧ el !! Z.to_nat i = Some e) 1 (Case #[i] el) e.
  Proof. solve_pure_exec; naive_solver. Qed.

End pure_exec.

(** IrredUnless *)

Section irreducible.
  Implicit Types (e : expr) (v : value) (r : result) (σ : state).

  Lemma language_to_val_eq e :
    language.to_val e = to_result e.
  Proof.
    rewrite /language.to_val /language.to_class; cbn.
    destruct (to_result e) eqn:Heq.
    - by rewrite (to_result_class _ _ Heq).
    - destruct to_class as [ [] | ] eqn:Heq';
        [ by rewrite (to_class_result _ _ Heq') in Heq | done | done].
  Qed.

  (* slightly hacky proof tactic for irreducibility, solving goals of the form [SIrreducible _ _ _ _].
    Basically the same proof script works for all these proofs, but there don't seem to be nice more general lemmas. *)
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
    intros ϕ e_s' σ_s' efs Hhead%prim_head_step;
    [ (*this need not complete the proof and may generate a proof obligation *)
      inv_head_step; try by (apply ϕ; eauto)
    | intros K e' Heq Hv; clear ϕ;
      destruct K as [ | Ki K]; first (done);
      exfalso; induction K as [ | Ki' K IH] in e', Ki, Hv, Heq |-*;
      [destruct Ki; inversion Heq; subst; cbn in *; congruence
      | eapply IH; first (by rewrite Heq);
        rewrite language_to_val_eq; apply fill_item_no_result;
        by rewrite -language_to_val_eq]
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

  Ltac finish_decision := rewrite /Decision; try first [left; by eauto | right; intros ?; discr ].
  Ltac decide_goal :=
    repeat match goal with
           | |- Decision (_ ∧ _) => apply and_dec
           | |- Decision (_ ∨ _) => apply or_dec
           | |- Decision (is_Some _) => apply is_Some_dec
           | |- Decision False => apply False_dec
           | |- Decision True => apply True_dec
           end;
    repeat match goal with
    | v : value |- _ =>
        match goal with
        | |- context[v] => destruct v as [ | [] []]
        end
    end; finish_decision.

  Ltac prove_irred_unless := apply irred_unless_irred_dec; [decide_goal | prove_irred].

  Global Instance irred_unless_match_val v el P σ  :
    IrredUnless (∃ i e, v = [ScInt i] ∧ 0 ≤ i ∧ el !! Z.to_nat i = Some e) P (Case (Val v) el) σ.
  Proof.
    prove_irred_unless.
    decide_goal.
    destruct (decide (0 ≤ n)) as [ H0 | H0]; first last.
    { right; intros (? & ? & [= ->] & ? & ?); lia. }
    destruct (decide (n < length el)) as [H1 | H1].
    + left. exists n, (el !!! Z.to_nat n). repeat split; [done | ].
      apply list_lookup_alt. split; [ lia | done].
    + right. intros (? & ? & [= ->] & ? & Hs%list_lookup_alt). lia.
  Qed.
  Global Instance irred_unless_match_place l t T el P σ  :
    IrredUnless (False) P (Case (Place l t T) el) σ.
  Proof. prove_irred_unless. Qed.

  Global Instance irred_unless_add v1 v2 P σ :
    IrredUnless (∃ z1 z2, v1 = [ScInt z1] ∧ v2 = [ScInt z2]) P (BinOp AddOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irred_unless_sub v1 v2 P σ :
    IrredUnless (∃ z1 z2, v1 = [ScInt z1] ∧ v2 = [ScInt z2]) P (BinOp SubOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irred_unless_lt v1 v2 P σ :
    IrredUnless (∃ z1 z2, v1 = [ScInt z1] ∧ v2 = [ScInt z2]) P (BinOp LtOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irred_unless_le v1 v2 P σ :
    IrredUnless (∃ z1 z2, v1 = [ScInt z1] ∧ v2 = [ScInt z2]) P (BinOp LeOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. Qed.

  (* TODO: EqOp, OffsetOp *)

  Global Instance irred_proj v v2 P σ :
    IrredUnless (∃ i s, v2 = [ScInt i] ∧ 0 ≤ i ∧ v !! Z.to_nat i = Some s) P (Proj (Val v) (Val v2)) σ.
  Proof.
    apply irred_unless_irred_dec; [| prove_irred].
    destruct v2 as [ | s2 []]; [ decide_goal | | decide_goal].
    destruct s2 as [ | i | | ]; [ decide_goal | | decide_goal..].
    destruct (decide (0 ≤ i)) as [Hi | Hi]; first last.
    { right; intros (? & ? & [= ->] & ? & ?); lia. }
    destruct (decide (i < length v)) as [H1 | H1].
    + left. exists i, (v !!! Z.to_nat i). repeat split; [done | ].
      apply list_lookup_alt. split; [ lia | done].
    + right. intros (? & ? & [= ->] & ? & Hs%list_lookup_alt). lia.
  Qed.
  Global Instance irred_ref_val v P σ :
    IrredUnless False P (Ref (Val v)) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irred_deref_place l t T T' P σ :
    IrredUnless False P (Deref (Place l t T) T') σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irred_deref v T P σ :
    IrredUnless (∃ l t, v = [ScPtr l t]) P (Deref (Val v) T) σ.
  Proof. prove_irred_unless. Qed.

  Global Instance irreducible_call_val v v2 P σ :
    IrredUnless (∃ fn, v = [ScFnPtr fn]) P (Call (Val v) (Val v2)) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irreducible_call_place v l t T P σ :
    IrredUnless (∃ fn, v = [ScFnPtr fn]) P (Call (Val v) (Place l t T)) σ.
  Proof. prove_irred_unless. Qed.


  Global Instance irreducible_endcall P σ :
    IrredUnless (∃ c, head σ.(scs) = Some c) P EndCall σ.
  Proof.
    prove_irred_unless. 2: { apply ϕ; rewrite TOP; exists c; eauto. }
    destruct (hd_error σ.(scs)); by finish_decision.
  Qed.

  (* TODO: heap operations and retagging *)

End irreducible.


