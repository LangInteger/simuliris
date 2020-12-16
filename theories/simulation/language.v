From stdpp Require Import strings gmap.
From iris.prelude Require Export prelude.
From iris.prelude Require Import options.

Section language_mixin.
  Context {expr val ectx state : Type}.

  (** Classifying expressions into values and calls. *)
  Inductive mixin_expr_class :=
  | ExprVal (v : val) : mixin_expr_class
  | ExprCall (fn_name : string) (arg : val) : mixin_expr_class.

  Context (of_class : mixin_expr_class → expr).
  Context (to_class : expr → option mixin_expr_class).

  Definition mixin_to_val (e : expr) : option val :=
    match to_class e with
    | Some (ExprVal v) => Some v
    | _ => None
    end.

  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).

  (** A program is a map from function names to function bodies. *)
  Definition mixin_prog := gmap string ectx.

  Context (head_step : mixin_prog → expr → state → expr → state → Prop).

  Record LanguageMixin := {
    mixin_to_of_class c : to_class (of_class c) = Some c;
    mixin_of_to_class e c : to_class e = Some c → of_class c = e;

    mixin_val_head_step p v σ1 e2 σ2 :
      head_step p (of_class (ExprVal v)) σ1 e2 σ2 → False;
    mixin_call_head_step p f v σ1 e2 σ2 :
      head_step p (of_class (ExprCall f v)) σ1 e2 σ2 →
      ∃ K, p !! f = Some K ∧ e2 = fill K (of_class (ExprVal v)) ∧ σ2 = σ1;

    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    (* FIXME: we will probably also need something for the interaction of [fill]
       with [ExprCall]... maybe we can generalize this and avoid [mixin_to_val]? *)
    mixin_fill_val K e : is_Some (mixin_to_val (fill K e)) → is_Some (mixin_to_val e);

    (** Given a head redex [e1_redex] somewhere in a term, and another
        decomposition of the same term into [fill K' e1'] such that [e1'] is not
        a value, then the head redex context is [e1']'s context [K'] filled with
        another context [K''].  In particular, this implies [e1 = fill K''
        e1_redex] by [fill_inj], i.e., [e1]' contains the head redex.)

        This implies there can be only one head redex, see
        [head_redex_unique]. *)
    mixin_step_by_val p K' K_redex e1' e1_redex σ1 e2 σ2 :
      fill K' e1' = fill K_redex e1_redex →
      mixin_to_val e1' = None →
      head_step p e1_redex σ1 e2 σ2 →
      ∃ K'', K_redex = comp_ectx K' K'';

    (** If [fill K e] takes a head step, then either [e] is a value or [K] is
        the empty evaluation context. In other words, if [e] is not a value
        wrapping it in a context does not add new head redex positions. *)
    mixin_head_ctx_step_val p K e σ1 e2 σ2 :
      head_step p (fill K e) σ1 e2 σ2 → is_Some (mixin_to_val e) ∨ K = empty_ectx;
  }.
End language_mixin.

Arguments mixin_expr_class : clear implicits.
Arguments mixin_prog : clear implicits.

Structure language := Language {
  expr : Type;
  val : Type;
  ectx : Type;
  state : Type;

  of_class : mixin_expr_class val → expr;
  to_class : expr → option (mixin_expr_class val);
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  head_step : mixin_prog ectx → expr → state → expr → state → Prop;

  language_mixin :
    LanguageMixin (val:=val) of_class to_class empty_ectx comp_ectx fill head_step
}.

Declare Scope expr_scope.
Bind Scope expr_scope with expr.

Declare Scope val_scope.
Bind Scope val_scope with val.

Arguments Language {_ _ _ _ _ _ _ _ _ _} _.
Arguments of_class {_} _.
Arguments to_class {_} _.
Arguments empty_ectx {_}.
Arguments comp_ectx {_} _ _.
Arguments fill {_} _ _.
Arguments head_step {_} _ _ _ _ _.

Definition expr_class (Λ : language) := mixin_expr_class Λ.(val).
Definition prog (Λ : language) := (mixin_prog Λ.(ectx)).

Definition to_val {Λ : language} := mixin_to_val Λ.(@to_class).
Definition of_val {Λ : language} (v : val Λ) := of_class (ExprVal v).

(* From an ectx_language, we can construct a language. *)
Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types c : expr_class Λ.
  Implicit Types K : ectx Λ.
  Implicit Types p : prog Λ.
  
  Lemma to_of_class c : to_class (of_class c) = Some c.
  Proof. apply language_mixin. Qed.
  Lemma of_to_class e c : to_class e = Some c → of_class c = e.
  Proof. apply language_mixin. Qed.

  Lemma val_head_step p v σ1 e2 σ2 :
    head_step p (of_class (ExprVal v)) σ1 e2 σ2 → False.
  Proof. apply language_mixin. Qed.
  Lemma call_head_step p f v σ1 e2 σ2 :
    head_step p (of_class (ExprCall f v)) σ1 e2 σ2 →
    ∃ K, p !! f = Some K ∧ e2 = fill K (of_class (ExprVal v)) ∧ σ2 = σ1.
  Proof. apply language_mixin. Qed.

  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply language_mixin. Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply language_mixin. Qed.
  Lemma step_by_val p K' K_redex e1' e1_redex σ1 e2 σ2 :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step p e1_redex σ1 e2 σ2 →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof. apply language_mixin. Qed.
  Lemma head_ctx_step_val p K e σ1 e2 σ2 :
    head_step p (fill K e) σ1 e2 σ2 → is_Some (to_val e) ∨ K = empty_ectx.
  Proof. apply language_mixin. Qed.

  Definition head_reducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ', head_step p e σ e' σ'.
  Definition head_irreducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∀ e' σ', ¬head_step p e σ e' σ'.
  Definition head_stuck (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ head_irreducible p e σ.

  (* All non-value redexes are at the root.  In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Inductive prim_step (p : prog Λ) (e1 : expr Λ) (σ1 : state Λ)
      (e2 : expr Λ) (σ2 : state Λ) : Prop :=
    Prim_step K e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step p e1' σ1 e2' σ2 → prim_step p e1 σ1 e2 σ2.

  Lemma Prim_step' p K e1 σ1 e2 σ2 :
    head_step p e1 σ1 e2 σ2 → prim_step p (fill K e1) σ1 (fill K e2) σ2.
  Proof. econstructor; eauto. Qed.

  Definition reducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ', prim_step p e σ e' σ'.
  Definition irreducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∀ e' σ', ¬prim_step p e σ e' σ'.
  Definition stuck (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ irreducible p e σ.
  Definition not_stuck (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    is_Some (to_val e) ∨ reducible p e σ.

  (** * Some lemmas about this language *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. rewrite /to_val /of_val /mixin_to_val to_of_class //. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    rewrite /to_val /of_val /mixin_to_val => Hval. apply of_to_class.
    destruct (to_class e) as [[]|]; simplify_option_eq; done.
  Qed.
  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.
  Lemma val_head_stuck p e σ e' σ' : head_step p e σ e' σ' → to_val e = None.
  Proof.
    destruct (to_val e) as [v|] eqn:Hval; last done.
    rewrite -(of_to_val e v) //. intros []%val_head_step.
  Qed.
  Lemma val_stuck p e σ e' σ' : prim_step p e σ e' σ' → to_val e = None.
  Proof.
    intros [??? -> -> ?%val_head_stuck].
    apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
  Qed.

  Lemma not_reducible p e σ : ¬reducible p e σ ↔ irreducible p e σ.
  Proof. unfold reducible, irreducible. naive_solver. Qed.
  Lemma reducible_not_val p e σ : reducible p e σ → to_val e = None.
  Proof. intros (?&?&?); eauto using val_stuck. Qed.
  Lemma val_irreducible p e σ : is_Some (to_val e) → irreducible p e σ.
  Proof. intros [??] ?? ?%val_stuck. by destruct (to_val e). Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.
  Lemma not_not_stuck p e σ : ¬not_stuck p e σ ↔ stuck p e σ.
  Proof.
    rewrite /stuck /not_stuck -not_eq_None_Some -not_reducible.
    destruct (decide (to_val e = None)); naive_solver.
  Qed.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma not_head_reducible p e σ : ¬head_reducible p e σ ↔ head_irreducible p e σ.
  Proof. unfold head_reducible, head_irreducible. naive_solver. Qed.

  (** The decomposition into head redex and context is unique.

      In all sensible instances, [comp_ectx K' empty_ectx] will be the same as
      [K'], so the conclusion is [K = K' ∧ e = e'], but we do not require a law
      to actually prove that so we cannot use that fact here. *)
  Lemma head_redex_unique p K K' e e' σ :
    fill K e = fill K' e' →
    head_reducible p e σ →
    head_reducible p e' σ →
    K = comp_ectx K' empty_ectx ∧ e = e'.
  Proof.
    intros Heq (e2 & σ2 & Hred) (e2' & σ2' & Hred').
    edestruct (step_by_val p K' K e' e) as [K'' HK];
      [by eauto using val_head_stuck..|].
    subst K. move: Heq. rewrite -fill_comp. intros <-%(inj (fill _)).
    destruct (head_ctx_step_val _ _ _ _ _ _ Hred') as [[]%not_eq_None_Some|HK''].
    { by eapply val_head_stuck. }
    subst K''. rewrite fill_empty. done.
  Qed.

  Lemma head_prim_step p e1 σ1 e2 σ2 :
    head_step p e1 σ1 e2 σ2 → prim_step p e1 σ1 e2 σ2.
  Proof. apply Prim_step with empty_ectx; by rewrite ?fill_empty. Qed.

  Lemma head_step_not_stuck p e σ e' σ' :
    head_step p e σ e' σ' → not_stuck p e σ.
  Proof. rewrite /not_stuck /reducible /=. eauto 10 using head_prim_step. Qed.

  Lemma fill_prim_step p K e1 σ1 e2 σ2 :
    prim_step p e1 σ1 e2 σ2 → prim_step p (fill K e1) σ1 (fill K e2) σ2.
  Proof.
    destruct 1 as [K' e1' e2' -> ->].
    rewrite !fill_comp. by econstructor.
  Qed.
  Lemma fill_reducible p K e σ : reducible p e σ → reducible p (fill K e) σ.
  Proof.
    intros (e'&σ'&?). exists (fill K e'), σ'. by apply fill_prim_step.
  Qed.
  Lemma head_prim_reducible p e σ : head_reducible p e σ → reducible p e σ.
  Proof. intros (e'&σ'&?). eexists e', σ'. by apply head_prim_step. Qed.
  Lemma head_prim_fill_reducible p e K σ :
    head_reducible p e σ → reducible p (fill K e) σ.
  Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
  Lemma head_prim_irreducible p e σ : irreducible p e σ → head_irreducible p e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.

  Lemma prim_head_reducible p e σ :
    reducible p e σ → sub_redexes_are_values e → head_reducible p e σ.
  Proof.
    intros (e'&σ'&[K e1' e2' -> -> Hstep]) ?.
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty /head_reducible; eauto.
  Qed.
  Lemma prim_head_irreducible p e σ :
    head_irreducible p e σ → sub_redexes_are_values e → irreducible p e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma head_stuck_stuck p e σ :
    head_stuck p e σ → sub_redexes_are_values e → stuck p e σ.
  Proof.
    intros [] ?. split; first done. by apply prim_head_irreducible.
  Qed.

  Lemma head_reducible_prim_step_ctx p K e1 σ1 e2 σ2 :
    head_reducible p e1 σ1 →
    prim_step p (fill K e1) σ1 e2 σ2 →
    ∃ e2', e2 = fill K e2' ∧ head_step p e1 σ1 e2' σ2.
  Proof.
    intros (e2''&σ2''&HhstepK) [K' e1' e2' HKe1 -> Hstep].
    edestruct (step_by_val p K) as [K'' ?];
      eauto using val_head_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp; split; first done.
    apply head_ctx_step_val in HhstepK as [[v ?]|?]; simplify_eq.
    { apply val_head_stuck in Hstep; simplify_eq. }
    by rewrite !fill_empty.
  Qed.

  Lemma head_reducible_prim_step p e1 σ1 e2 σ2 :
    head_reducible p e1 σ1 →
    prim_step p e1 σ1 e2 σ2 →
    head_step p e1 σ1 e2 σ2.
  Proof.
    intros.
    edestruct (head_reducible_prim_step_ctx p empty_ectx) as (?&?&?);
      rewrite ?fill_empty; eauto.
    by simplify_eq; rewrite fill_empty.
  Qed.
End language.
