From simuliris.simulation Require Import language lifting.
From simuliris.stacked_borrows Require Export lang.
From simuliris.stacked_borrows Require Import tactics.
(* TODO should we really import things from the simplang folder here?
  require this for the [forall_equiv_dec] lemma *)
From simuliris.simplang Require Import base.
From iris.prelude Require Import options.



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
  Global Instance pure_iota_result x (e2 : expr) (r : result) :
    PureExec True 1 (Let x (of_result r) e2) (subst' x (of_result r) e2).
  Proof. solve_pure_exec. rewrite to_of_result. eauto. Qed.

  (* We do not have a general instance for BinOp as evaluation of EqOp for locations is not pure *)
  Global Instance pure_add z1 z2  :
    PureExec True 1 (BinOp AddOp (#[ScInt z1]) (#[ScInt z2])) (#[ScInt (z1 + z2)]).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_sub z1 z2  :
    PureExec True 1 (BinOp SubOp (#[ScInt z1]) (#[ScInt z2])) (#[ScInt (z1 - z2)]).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_le z1 z2 :
    PureExec True 1 (BinOp LeOp (#[ScInt z1]) (#[ScInt z2])) (#[bool_decide (z1 ≤ z2)]).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_lt z1 z2 :
    PureExec True 1 (BinOp LtOp (#[ScInt z1]) (#[ScInt z2])) (#[bool_decide (z1 < z2)]).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_offset l t z :
    PureExec True 1 (BinOp OffsetOp (#[ScPtr l t]) (#[ScInt z])) (#[ScPtr (l +ₗ z) t]).
  Proof. solve_pure_exec. Qed.

  (* TODO: figure out something useful for EqOp *)
  (*Global Instance pure_eq_refl sc1 sc2 :*)
    (*PureExec 1 (BinOp EqOp (#[sc1]) (#[sc2])) (#[false]).*)

  Global Instance pure_proj v i s :
    PureExec (0 ≤ i ∧ v !! (Z.to_nat i) = Some s) 1 (Proj (Val (v : list scalar)) (#[ScInt i])) (#[s]).
  Proof.
    solve_pure_exec. destruct_and!.
    match goal with H1: ?t = Some _, H2: ?t = Some _ |- _ => rewrite H1 in H2 end.
    naive_solver.
  Qed.
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

  (* not an instance as we usually don't want it to reduce in order to apply coinduction lemmas *)
  Lemma pure_while e1 e2 :
    PureExec True 1 (while: e1 do e2 od) (if: e1 then e2;; while: e1 do e2 od else #[☠]).
  Proof. solve_pure_exec. Qed.

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
      inv_head_step; try by (apply ϕ; eauto 8)
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

  Ltac finish_decision := rewrite /Decision; try first [left; by eauto 8 | right; intros ?; discr ].
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
    rename select Z into n.
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
  Global Instance irred_unless_offset v1 v2 P σ :
    IrredUnless (∃ l t z, v1 = [ScPtr l t] ∧ v2 = [ScInt z]) P (BinOp OffsetOp (Val v1) (Val v2)) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irred_unless_eq v1 v2 P σ :
    IrredUnless (∃ sc1 sc2, v1 = [sc1] ∧ v2 = [sc2] ∧ (scalar_eq σ.(shp) sc1 sc2 ∨ scalar_neq sc1 sc2)) P (BinOp EqOp (Val v1) (Val v2)) σ.
  Proof.
    apply irred_unless_irred_dec; [ | prove_irred].
    destruct v1 as [ | sc1 []]; try finish_decision.
    destruct v2 as [ | sc2 []]; try finish_decision.
    destruct (decide (scalar_eq σ.(shp) sc1 sc2)); first by eauto 8.
    destruct (decide (scalar_neq sc1 sc2)); finish_decision.
  Qed.

  Global Instance irred_proj v v2 P σ :
    IrredUnless (∃ i s, v2 = [ScInt i] ∧ 0 ≤ i ∧ v !! Z.to_nat i = Some s) P (Proj (Val v) (Val v2)) σ.
  Proof.
    apply irred_unless_irred_dec; [| prove_irred].
    destruct v2 as [ | s2 []]; [ decide_goal | | decide_goal].
    destruct s2 as [ | i | | | ]; [ decide_goal | | decide_goal..].
    destruct (decide (0 ≤ i)) as [Hi | Hi]; first last.
    { right; intros (? & ? & [= ->] & ? & ?); lia. }
    destruct (decide (i < length v)) as [H1 | H1].
    + left. exists i, (v !!! Z.to_nat i). repeat split; [done | ].
      apply list_lookup_alt. split; [ lia | done].
    + right. intros (? & ? & [= ->] & ? & Hs%list_lookup_alt). lia.
  Qed.
  Global Instance irred_proj_place l t T v2 P σ : 
    IrredUnless False P (Proj (Place l t T) (Val v2)) σ.
  Proof. prove_irred_unless. Qed.

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


  Global Instance irreducible_endcall P σ v :
    IrredUnless (∃ c, v = [ScCallId c] ∧ c ∈ σ.(scs)) P (EndCall (Val v)) σ.
  Proof.
    prove_irred_unless.
    rename select nat into c.
    destruct (decide (c ∈ σ.(scs))); finish_decision.
  Qed.

  Global Instance irreducible_retag P σ v v' pk T rk :
    IrredUnless (∃ c ot l, v = [ScPtr l ot] ∧ v' = [ScCallId c] ∧ c ∈ σ.(scs) ∧
      is_Some (retag σ.(sst) σ.(snp) σ.(scs) c l ot rk pk T)) P (Retag (Val v) (Val v') pk T rk) σ.
  Proof.
    prove_irred_unless.
    rename select nat into c.
    rename select loc into l.
    rename select tag into tg.
    destruct (decide (c ∈ σ.(scs))); last finish_decision.
    destruct (retag σ.(sst) σ.(snp) σ.(scs) c l tg rk pk T) eqn:Heq.
    + left. eauto 8.
    + right. intros (c' & ot & l' & [= -> ->] & [= ->] & ? &? & ?); congruence.
  Qed.
  Global Instance irreducible_retag_place_l P σ l t T T' v pk rk :
    IrredUnless False P (Retag (Place l t T) (Val v) pk T' rk) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irreducible_retag_place_r P σ l t T T' v pk rk :
    IrredUnless False P (Retag (Val v) (Place l t T) pk T' rk) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irreducible_retag_place_r2 P σ l t T T' l' t' T'' pk rk :
    IrredUnless False P (Retag (Place l' t' T'') (Place l t T) pk T' rk) σ.
  Proof. prove_irred_unless. Qed.

  Global Instance irreducible_copy_val P σ v :
    IrredUnless False P (Copy (Val v)) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irreducible_copy_place P σ l t T :
    IrredUnless ((∃ v, read_mem l (tsize T) σ.(shp) = Some v ∧ is_Some (memory_read σ.(sst) σ.(scs) l t (tsize T)) (* ∧ v <<t σ.(snp) *)) ∨ memory_read σ.(sst) σ.(scs) l t (tsize T) = None) P (Copy (Place l t T)) σ.
  Proof.
    prove_irred_unless.
    2: { destruct memory_read; eauto. }
    destruct (read_mem l (tsize T) σ.(shp)) eqn:Heq1; last finish_decision.
    destruct (memory_read _ _ _ _ _) eqn:Heq2.
    2: { right; intros (v' & [= ->] & (? & [=]) (* & _ *)). }
    finish_decision.
    (*destruct (decide (v <<t σ.(snp))); finish_decision.*)
  Qed.

  Global Instance irreducible_write_val_left1 P σ v v' :
    IrredUnless False P (Write (Val v) (Val v')) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irreducible_write_val_left2 P σ v l t T :
    IrredUnless False P (Write (Val v) (Place l t T)) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irreducible_write_place_right P σ l' t' T' l t T :
    IrredUnless False P (Write (Place l' t' T') (Place l t T)) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irreducible_write P σ l t T v :
    IrredUnless ((∀ (i: nat), (i < length v)%nat → l +ₗ i ∈ dom (gset loc) σ.(shp)) ∧ is_Some (memory_written σ.(sst) σ.(scs) l t (tsize T)) ∧ length v = tsize T) P (Write (Place l t T) (Val v)) σ.
  Proof.
    apply irred_unless_irred_dec; [ | prove_irred].
    destruct (decide (length v = tsize T)) as [Heq|]; last finish_decision.
    destruct (decide (is_Some (memory_written (sst σ) (scs σ) l t (tsize T)))) as [Hsome|]; last finish_decision.
    enough (Decision (∀ i : nat, (i < length v)%nat → l +ₗ i ∈ dom (gset loc) (shp σ))) as [ | ]; [by finish_decision.. | ].
    clear Heq Hsome. generalize (length v) as n.
    intros n. induction n as [ | n IH]. { left. lia. }
    destruct (decide (l +ₗ n ∈ (dom (gset loc) σ.(shp)))); first last.
    { right. intros Ha. specialize (Ha n ltac:(lia)). move: Ha. done. }
    destruct IH as [IH | IH].
    + left. intros m Hm. destruct (decide (Z.of_nat n = m)) as [<- | Hneq]; first by eauto.
      apply IH. lia.
    + destruct (decide (0 < n)) as [Hgt | Hlt].
      * right. contradict IH. intros m Hm. apply IH. lia.
      * left. intros m Hm.  assert (m = 0%nat) as -> by lia. assert (n = 0%nat) as -> by lia. eauto.
  Qed.

  Global Instance irreducible_free_val P σ v :
    IrredUnless False P (Free (Val v)) σ.
  Proof. prove_irred_unless. Qed.
  Global Instance irreducible_free P σ l t T :
    IrredUnless ((∀ m, is_Some (σ.(shp) !! (l +ₗ m)) ↔ 0 ≤ m < tsize T) ∧ is_Some (memory_deallocated σ.(sst) σ.(scs) l t (tsize T))) P (Free (Place l t T)) σ.
  Proof.
    prove_irred_unless. generalize (tsize T) as n => n.
    apply forall_equiv_dec.
    - destruct (decide (map_Forall (λ l' _,
       (l'.1 = l.1 → l.2 ≤ l'.2 < l.2 + n)%Z) σ.(shp))) as [Hm|Hm]; last first.
      + right. contradict Hm. apply map_Forall_lookup_2 => i ? Hheap ? /=.
        have Hi : i = (l +ₗ (i.2 - l.2)).
        { rewrite /shift_loc. destruct i, l => /=; f_equal; [ done | lia]. }
        rewrite Hi in Hheap. eapply mk_is_Some, Hm in Hheap. lia.
      + left. intros m (x & Hsome).
        specialize (map_Forall_lookup_1 _ _ _ _ Hm Hsome eq_refl).
        destruct l; simpl; lia.
    - induction n as [ | n IH]. { left. lia. }
      destruct (σ.(shp) !! (l +ₗ n)) eqn:Hs; first last.
      { right. intros Ha. specialize (Ha n ltac:(lia)). move: Ha. rewrite Hs. intros (? & [=]). }
      destruct IH as [IH | IH].
      + left. intros m Hm. destruct (decide (Z.of_nat n = m)) as [<- | Hneq]; first by eauto.
        apply IH. lia.
      + destruct (decide (0 < n)) as [Hgt | Hlt].
        * right. contradict IH. intros m Hm. apply IH. lia.
        * left. intros m Hm. replace m with (Z.of_nat n) by lia. eauto.
  Qed.

  Global Instance irreducible_write_weak P σ l t T v :
    IrredUnless (length v = tsize T) P (Write (Place l t T) (Val v)) σ | 10.
  Proof.
    eapply irred_unless_weaken; last apply irreducible_write. tauto.
  Qed.
  Global Instance irreducible_retag_weak P σ v v' pk T rk :
    IrredUnless (∃ c ot l, v = [ScPtr l ot] ∧ v' = [ScCallId c]) P (Retag (Val v) (Val v') pk T rk) σ | 10.
  Proof.
    eapply irred_unless_weaken; last apply irreducible_retag.
    intros (c & ot & l & -> & -> & _). eauto.
  Qed.
End irreducible.
