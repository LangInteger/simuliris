From stdpp Require Import relations strings gmap.
From iris.prelude Require Export prelude.
From iris.prelude Require Import options.
From simuliris.simulation Require Import relations.

Section language_mixin.
  Context {expr val ectx state : Type}.

  (** Classifying expressions into values and calls. *)
  Inductive mixin_expr_class :=
  | ExprVal (v : val) : mixin_expr_class
  | ExprCall (fn_name : string) (arg : val) : mixin_expr_class.

  Context (of_class : mixin_expr_class → expr).
  Context (to_class : expr → option mixin_expr_class).

  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).

  (** A program is a map from function names to function bodies. *)
  Definition mixin_prog := gmap string ectx.

  Context (head_step : mixin_prog → expr → state → expr → state → list expr → Prop).

  Record LanguageMixin := {
    mixin_to_of_class c : to_class (of_class c) = Some c;
    mixin_of_to_class e c : to_class e = Some c → of_class c = e;

    (** mixin_val_head_step is not an iff because the backward direction is trivial *)
    mixin_val_head_step p v σ1 e2 σ2 efs :
      head_step p (of_class (ExprVal v)) σ1 e2 σ2 efs → False;
    mixin_call_head_step p f v σ1 e2 σ2 efs :
      head_step p (of_class (ExprCall f v)) σ1 e2 σ2 efs ↔
      ∃ K, p !! f = Some K ∧ e2 = fill K (of_class (ExprVal v)) ∧ σ2 = σ1 ∧ efs = [];

    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    (* The the things in a class contain only values in redex positions (or the
       redex is the topmost one). *)
    mixin_fill_class K e :
      is_Some (to_class (fill K e)) → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v);

    (** Given a head redex [e1_redex] somewhere in a term, and another
        decomposition of the same term into [fill K' e1'] such that [e1'] is not
        a value, then the head redex context is [e1']'s context [K'] filled with
        another context [K''].  In particular, this implies [e1 = fill K''
        e1_redex] by [fill_inj], i.e., [e1]' contains the head redex.)

        This implies there can be only one head redex, see
        [head_redex_unique]. *)
    mixin_step_by_val p K' K_redex e1' e1_redex σ1 e2 σ2 efs :
      fill K' e1' = fill K_redex e1_redex →
      match to_class e1' with Some (ExprVal _) => False | _ => True end →
      head_step p e1_redex σ1 e2 σ2 efs →
      ∃ K'', K_redex = comp_ectx K' K'';

    (** If [fill K e] takes a head step, then either [e] is a value or [K] is
        the empty evaluation context. In other words, if [e] is not a value
        wrapping it in a context does not add new head redex positions. *)
    (* FIXME: This is the exact same conclusion as [mixin_fill_class]... is
       there some pattern or reduncancy here? *)
    mixin_head_ctx_step_val p K e σ1 e2 σ2 efs :
      head_step p (fill K e) σ1 e2 σ2 efs → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v);
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
  head_step : mixin_prog ectx → expr → state → expr → state → list expr → Prop;

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
Arguments head_step {_} _ _ _ _ _ _.

Definition expr_class (Λ : language) := mixin_expr_class Λ.(val).
Definition prog (Λ : language) := (mixin_prog Λ.(ectx)).

Definition to_val {Λ : language} (e : expr Λ) :=
  match to_class e with
  | Some (ExprVal v) => Some v
  | _ => None
  end.
Definition of_val {Λ : language} (v : val Λ) := of_class (ExprVal v).

Definition to_call {Λ : language} (e : expr Λ) :=
  match to_class e with
  | Some (ExprCall f v) => Some (f, v)
  | _ => None
  end.
Definition of_call {Λ : language} f (v : val Λ) := of_class (ExprCall f v).

(* From an ectx_language, we can construct a language. *)
Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types c : expr_class Λ.
  Implicit Types K : ectx Λ.
  Implicit Types p : prog Λ.
  Implicit Types efs : list (expr Λ).

  Lemma to_of_class c : to_class (of_class c) = Some c.
  Proof. apply language_mixin. Qed.
  Lemma of_to_class e c : to_class e = Some c → of_class c = e.
  Proof. apply language_mixin. Qed.

  Lemma to_val_of_call f v : to_val (of_call f v) = None.
  Proof. rewrite /to_val /of_call to_of_class. done. Qed.
  Lemma to_call_of_val v : to_call (of_val v) = None.
  Proof. rewrite /to_call /of_val to_of_class. done. Qed.
  Lemma is_val_is_class e : is_Some (to_val e) → is_Some (to_class e).
  Proof. rewrite /to_val /is_Some. destruct (to_class e) as [[|]|]; naive_solver. Qed.
  Lemma is_call_is_class e : is_Some (to_call e) → is_Some (to_class e).
  Proof. rewrite /to_call /is_Some. destruct (to_class e) as [[|]|]; naive_solver. Qed.

  Lemma val_head_step p v σ1 e2 σ2 efs :
    head_step p (of_class (ExprVal v)) σ1 e2 σ2 efs → False.
  Proof. apply language_mixin. Qed.
  Lemma call_head_step p f v σ1 e2 σ2 efs :
    head_step p (of_class (ExprCall f v)) σ1 e2 σ2 efs ↔
    ∃ K, p !! f = Some K ∧ e2 = fill K (of_class (ExprVal v)) ∧ σ2 = σ1 ∧ efs = nil.
  Proof. apply language_mixin. Qed.

  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply language_mixin. Qed.
  Lemma fill_class' K e :
    is_Some (to_class (fill K e)) → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v).
  Proof. apply language_mixin. Qed.
  Lemma step_by_val' p K' K_redex e1' e1_redex σ1 e2 σ2 efs :
      fill K' e1' = fill K_redex e1_redex →
      match to_class e1' with Some (ExprVal _) => False | _ => True end →
      head_step p e1_redex σ1 e2 σ2 efs →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof. apply language_mixin. Qed.
  Lemma head_ctx_step_val' p K e σ1 e2 σ2 efs :
    head_step p (fill K e) σ1 e2 σ2 efs → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v).
  Proof. apply language_mixin. Qed.

  Lemma fill_class K e :
    is_Some (to_class (fill K e)) → K = empty_ectx ∨ is_Some (to_val e).
  Proof.
    intros [?|[v Hv]]%fill_class'; first by left. right.
    rewrite /to_val Hv. eauto.
  Qed.
  Lemma step_by_val p K' K_redex e1' e1_redex σ1 e2 σ2 efs :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step p e1_redex σ1 e2 σ2 efs →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof.
    rewrite /to_val => ? He1'. eapply step_by_val'; first done.
    destruct (to_class e1') as [[]|]; done.
  Qed.
  Lemma head_ctx_step_val p K e σ1 e2 σ2 efs :
    head_step p (fill K e) σ1 e2 σ2 efs → K = empty_ectx ∨ is_Some (to_val e).
  Proof.
    intros [?|[v Hv]]%head_ctx_step_val'; first by left. right.
    rewrite /to_val Hv. eauto.
  Qed.
  Lemma call_head_step_inv p f v σ1 e2 σ2 efs :
    head_step p (of_class (ExprCall f v)) σ1 e2 σ2 efs →
    ∃ K, p !! f = Some K ∧ e2 = fill K (of_class (ExprVal v)) ∧ σ2 = σ1 ∧ efs = [].
  Proof. eapply call_head_step. Qed.
  Lemma call_head_step_intro p f v K σ1 efs :
    p !! f = Some K →
    head_step p (of_call f v) σ1 (fill K (of_val v)) σ1 [].
  Proof. intros ?. eapply call_head_step; eexists; eauto. Qed.

  Definition head_reducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ' efs, head_step p e σ e' σ' efs.
  Definition head_irreducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∀ e' σ' efs, ¬head_step p e σ e' σ' efs.
  Definition head_stuck (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ head_irreducible p e σ.

  (* All non-value redexes are at the root.  In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Inductive prim_step (p : prog Λ) : expr Λ → state Λ → expr Λ → state Λ → list (expr Λ) → Prop :=
    Prim_step K e1 e2 σ1 σ2 e1' e2' efs:
      e1 = fill K e1' → e2 = fill K e2' →
      head_step p e1' σ1 e2' σ2 efs → prim_step p e1 σ1 e2 σ2 efs.

  Lemma Prim_step' p K e1 σ1 e2 σ2 efs :
    head_step p e1 σ1 e2 σ2 efs → prim_step p (fill K e1) σ1 (fill K e2) σ2 efs.
  Proof. econstructor; eauto. Qed.

  Definition reducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ' efs, prim_step p e σ e' σ' efs.
  Definition irreducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∀ e' σ' efs, ¬prim_step p e σ e' σ' efs.
  Definition stuck (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ irreducible p e σ.
  Definition not_stuck (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    is_Some (to_val e) ∨ reducible p e σ.

  (** * Some lemmas about this language *)
  Lemma prim_step_inv p e1 e2 σ1 σ2 efs:
    prim_step p e1 σ1 e2 σ2 efs →
    ∃ K e1' e2', e1 = fill K e1' ∧ e2 = fill K e2' ∧ head_step p e1' σ1 e2' σ2 efs.
  Proof. inversion 1; subst; do 3 eexists; eauto. Qed.
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. rewrite /to_val /of_val to_of_class //. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    rewrite /to_val /of_val => Hval. apply of_to_class.
    destruct (to_class e) as [[]|]; simplify_option_eq; done.
  Qed.
  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.
  Lemma val_head_stuck p e σ e' σ' efs: head_step p e σ e' σ' efs → to_val e = None.
  Proof.
    destruct (to_val e) as [v|] eqn:Hval; last done.
    rewrite -(of_to_val e v) //. intros []%val_head_step.
  Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof.
    intros Hval. destruct (fill_class K e) as [HK|He].
    - apply is_val_is_class. done.
    - subst K. move: Hval. rewrite fill_empty. done.
    - done.
  Qed.
  Lemma val_stuck p e σ e' σ' efs: prim_step p e σ e' σ' efs → to_val e = None.
  Proof.
    intros (?&?&? & -> & -> & ?%val_head_stuck)%prim_step_inv.
    apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
  Qed.

  Lemma to_of_call f v : to_call (of_call f v) = Some (f, v).
  Proof. rewrite /to_call /of_call to_of_class //. Qed.
  Lemma of_to_call e f v : to_call e = Some (f, v) → of_call f v = e.
  Proof.
    rewrite /to_call /of_call => Hval. apply of_to_class.
    destruct (to_class e) as [[] | ]; simplify_option_eq; done.
  Qed.
  Lemma of_to_call_flip f v e : of_call f v = e → to_call e = Some (f, v).
  Proof. intros <-. apply to_of_call. Qed.

  Lemma not_reducible p e σ : ¬reducible p e σ ↔ irreducible p e σ.
  Proof. unfold reducible, irreducible. naive_solver. Qed.
  Lemma reducible_not_val p e σ : reducible p e σ → to_val e = None.
  Proof. intros (?&?&?&?); eauto using val_stuck. Qed.
  Lemma val_irreducible p e σ : is_Some (to_val e) → irreducible p e σ.
  Proof. intros [??] ?? ??%val_stuck. by destruct (to_val e). Qed.
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
    intros Heq (e2 & σ2 & efs & Hred) (e2' & σ2' & efs' & Hred').
    edestruct (step_by_val p K' K e' e) as [K'' HK];
      [by eauto using val_head_stuck..|].
    subst K. move: Heq. rewrite -fill_comp. intros <-%(inj (fill _)).
    destruct (head_ctx_step_val _ _ _ _ _ _ _ Hred') as [HK''|[]%not_eq_None_Some].
    - subst K''. rewrite fill_empty. done.
    - by eapply val_head_stuck.
  Qed.

  Lemma head_prim_step p e1 σ1 e2 σ2 efs :
    head_step p e1 σ1 e2 σ2 efs → prim_step p e1 σ1 e2 σ2 efs.
  Proof. apply Prim_step with empty_ectx; by rewrite ?fill_empty. Qed.

  Lemma head_step_not_stuck p e σ e' σ' efs:
    head_step p e σ e' σ' efs → not_stuck p e σ.
  Proof. rewrite /not_stuck /reducible /=. eauto 10 using head_prim_step. Qed.

  Lemma fill_prim_step p K e1 σ1 e2 σ2 efs :
    prim_step p e1 σ1 e2 σ2 efs → prim_step p (fill K e1) σ1 (fill K e2) σ2 efs.
  Proof.
    intros (K' & e1' & e2' & -> & -> & ?) % prim_step_inv.
    rewrite !fill_comp. by econstructor.
  Qed.
  Lemma fill_reducible p K e σ : reducible p e σ → reducible p (fill K e) σ.
  Proof.
    intros (e'&σ'&efs&?). exists (fill K e'), σ', efs. by apply fill_prim_step.
  Qed.
  Lemma head_prim_reducible p e σ : head_reducible p e σ → reducible p e σ.
  Proof. intros (e'&σ'&efs&?). eexists e', σ', efs. by apply head_prim_step. Qed.
  Lemma head_prim_fill_reducible p e K σ :
    head_reducible p e σ → reducible p (fill K e) σ.
  Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
  Lemma head_prim_irreducible p e σ : irreducible p e σ → head_irreducible p e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.

  Lemma prim_head_step p e σ e' σ' efs:
    prim_step p e σ e' σ' efs → sub_redexes_are_values e → head_step p e σ e' σ' efs.
  Proof.
    intros Hprim ?. destruct (prim_step_inv _ _ _ _ _ _ Hprim) as (K & e1' & e2' & -> & -> & Hstep).
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite !fill_empty /head_reducible; eauto.
  Qed.
  Lemma prim_head_reducible p e σ :
    reducible p e σ → sub_redexes_are_values e → head_reducible p e σ.
  Proof. intros (e'&σ'&efs&Hprim) ?. do 3 eexists; by eapply prim_head_step. Qed.
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

  Lemma head_reducible_prim_step_ctx p K e1 σ1 e2 σ2 efs :
    head_reducible p e1 σ1 →
    prim_step p (fill K e1) σ1 e2 σ2 efs →
    ∃ e2', e2 = fill K e2' ∧ head_step p e1 σ1 e2' σ2 efs.
  Proof.
    intros (e2''&σ2''&efs'&HhstepK) (K' & e1' & e2' & HKe1 & -> & Hstep) % prim_step_inv.
    edestruct (step_by_val p K) as [K'' ?];
      eauto using val_head_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp; split; first done.
    apply head_ctx_step_val in HhstepK as [?|[v ?]]; simplify_eq.
    - by rewrite !fill_empty.
    - apply val_head_stuck in Hstep; simplify_eq.
  Qed.

  Lemma head_reducible_prim_step p e1 σ1 e2 σ2 efs :
    head_reducible p e1 σ1 →
    prim_step p e1 σ1 e2 σ2 efs →
    head_step p e1 σ1 e2 σ2 efs.
  Proof.
    intros.
    edestruct (head_reducible_prim_step_ctx p empty_ectx) as (?&?&?);
      rewrite ?fill_empty; eauto.
    by simplify_eq; rewrite fill_empty.
  Qed.

  Lemma fill_stuck (P : prog Λ) e σ K : stuck P e σ → stuck P (fill K e) σ.
  Proof.
    intros Hstuck; split.
    + apply fill_not_val, Hstuck.
    + intros e'' σ'' efs (K_redex &e1 &e2 &Heq &-> &Hhead)%prim_step_inv.
      edestruct (step_by_val P K K_redex _ _ _ _ _ _ Heq ltac:(apply Hstuck) Hhead) as (K'' & ->).
      rewrite -fill_comp in Heq. apply fill_inj in Heq as ->.
      eapply (proj2 Hstuck). econstructor; eauto.
  Qed.

  Lemma prim_step_call_inv p K f v e' σ σ' efs :
    prim_step p (fill K (of_call f v)) σ e' σ' efs →
    ∃ K_f, p !! f = Some K_f ∧ e' = fill K (fill K_f (of_val v)) ∧ σ' = σ ∧ efs = [].
  Proof.
    intros (K' & e1 & e2 & Hctx & -> & Hstep)%prim_step_inv.
    eapply step_by_val in Hstep as H'; eauto; last apply to_val_of_call.
    destruct H' as [K'' Hctx']; subst K'.
    rewrite -fill_comp in Hctx. eapply fill_inj in Hctx.
    destruct (fill_class K'' e1) as [->|Hval].
    - apply is_call_is_class. erewrite of_to_call_flip; eauto.
    - rewrite fill_empty in Hctx. subst e1.
      apply call_head_step_inv in Hstep as (K_f & ? & -> & -> & ->).
      exists K_f. rewrite -fill_comp fill_empty. naive_solver.
    - unfold is_Some in Hval. erewrite val_head_stuck in Hval; naive_solver.
  Qed.

  Lemma val_prim_step p v σ e' σ' efs :
   ¬ prim_step p (of_val v) σ e' σ' efs.
  Proof.
    intros (K & e1' & e2' & Heq & -> & Hstep') % prim_step_inv.
    edestruct (fill_val K e1') as (v1''& ?).
    { rewrite -Heq. rewrite to_of_val. by exists v. }
    eapply val_head_step.
    erewrite <-(of_to_val e1') in Hstep'; eauto.
  Qed.

  Lemma fill_reducible_prim_step p e e' σ σ' K efs :
    reducible p e σ → prim_step p (fill K e) σ e' σ' efs → ∃ e'', e' = fill K e'' ∧ prim_step p e σ e'' σ' efs.
  Proof.
    intros (e1 & σ1 & efs' & (K'' & e1'' & e2'' & ->  & -> & Hhead) % prim_step_inv) Hprim.
    rewrite fill_comp in Hprim.
    eapply head_reducible_prim_step_ctx in Hprim as (e1' & -> & Hhead'); last by rewrite /head_reducible; eauto.
    eexists. rewrite -fill_comp; by eauto using Prim_step'.
  Qed.

  (** Lifting of steps to thread pools *)
  Implicit Types (T: list (expr Λ)).  (* thread pools *)
  Implicit Types (I J: list nat).       (* traces *)
  Implicit Types (O: gset nat).       (* trace sets *)

  Inductive pool_step (p: prog Λ): list (expr Λ) → state Λ → nat → list (expr Λ) → state Λ → Prop :=
    | Pool_step i T_l e e' T_r efs σ σ':
        prim_step p e σ e' σ' efs →
        i = length T_l →
        pool_step p (T_l ++ e :: T_r) σ i (T_l ++ e' :: T_r ++ efs) σ'.

  Inductive pool_steps (p: prog Λ): list (expr Λ) → state Λ → list nat → list (expr Λ) → state Λ → Prop :=
    | Pool_steps_refl T σ: pool_steps p T σ [] T σ
    | Pool_steps_step T T' T'' σ σ' σ'' i I:
      pool_step p T σ i T' σ' →
      pool_steps p T' σ' I T'' σ'' →
      pool_steps p T σ (i:: I) T'' σ''.


  Lemma pool_step_iff p T σ i T' σ':
    pool_step p T σ i T' σ' ↔
    (∃ e e' efs, prim_step p e σ e' σ' efs ∧ T !! i = Some e ∧ T' = <[i := e']> T ++ efs).
  Proof.
    split.
    - destruct 1 as [i T_l e e' T_r efs σ σ' Hstep Hlen]; subst.
      exists e, e', efs. split; first done.
      rewrite list_lookup_middle; last done.
      split; first done.
      replace (length T_l) with (length T_l + 0) by lia.
      rewrite insert_app_r; simpl.
      by rewrite -app_assoc.
    - intros (e & e' & efs & Hstep & Hlook & ->).
      replace T with (take i T ++ e :: drop (S i) T); last by eapply take_drop_middle.
      assert (i = length (take i T)).
      { rewrite take_length_le; first lia. eapply lookup_lt_Some in Hlook. lia. }
      replace i with (length (take i T) + 0) at 4 by lia.
      rewrite insert_app_r. simpl.
      rewrite -app_assoc; simpl.
      econstructor; auto.
  Qed.

  Lemma pool_step_value_preservation p v T σ i j T' σ':
    pool_step p T σ j T' σ' →
    T !! i = Some (of_val v) →
    T' !! i = Some (of_val v).
  Proof.
    rewrite pool_step_iff.
    destruct 1 as (e1 & e2 & efs & Hstep & Hpre & Hpost).
    intros Hlook. destruct (decide (i = j)); subst.
    - pose proof val_prim_step. by naive_solver.
    - eapply lookup_app_l_Some.
      rewrite list_lookup_insert_ne; done.
  Qed.

  Lemma pool_steps_value_preservation p v T σ i J T' σ':
    pool_steps p T σ J T' σ' →
    T !! i = Some (of_val v) →
    T' !! i = Some (of_val v).
  Proof.
    induction 1; eauto using pool_step_value_preservation.
  Qed.

  Lemma pool_steps_single p T σ i T' σ':
    pool_step p T σ i T' σ' ↔
    pool_steps p T σ [i] T' σ'.
  Proof.
    split.
    - intros Hstep; eauto using pool_steps.
    - inversion 1 as [|??????????Hsteps]; subst; inversion Hsteps; by subst.
  Qed.

  Lemma pool_steps_trans p T T' T'' σ σ' σ'' I J:
    pool_steps p T σ I T' σ' →
    pool_steps p T' σ' J T'' σ'' →
    pool_steps p T σ (I ++ J) T'' σ''.
  Proof.
    induction 1; simpl; eauto using pool_steps.
  Qed.


  (** Threads in a thread pool *)
  Definition threads T :=
    list_to_set (C := gset nat) (seq 0 (length T)).

  Lemma threads_spec T i:
    i ∈ threads T ↔ ∃ e, T !! i = Some e.
  Proof.
    rewrite elem_of_list_to_set elem_of_seq.
    split.
    - intros [_ Hlt]. eapply lookup_lt_is_Some_2. lia.
    - intros ? % lookup_lt_is_Some_1. lia.
  Qed.

  Lemma threads_insert T i e:
    threads T ⊆ threads (<[i:=e]> T).
  Proof.
    intros j [e' Hlook]%threads_spec.
    eapply threads_spec.
    destruct (decide (i = j)).
    - subst; exists e.
      eapply list_lookup_insert, lookup_lt_Some, Hlook.
    - rewrite list_lookup_insert_ne; last done. by exists e'.
  Qed.

  Lemma threads_app T T':
    threads T ⊆ threads (T ++ T').
  Proof.
    intros j (e & Hlook)%threads_spec.
    eapply threads_spec. exists e.
    eapply lookup_app_l_Some, Hlook.
  Qed.

  (* a prim_step does the following mutation to the thread pool *)
  Lemma threads_prim_step e' T' i T :
    threads T ⊆ threads (<[i := e']> T ++ T').
  Proof.
    etrans; last eapply threads_app.
    eapply threads_insert.
  Qed.

  Lemma threads_pool_step p T σ i T' σ' :
    pool_step p T σ i T' σ' →
    threads T ⊆ threads T'.
  Proof.
    rewrite pool_step_iff; intros (e & e' & efs & Hstep & Hlook & ->).
    eapply threads_prim_step.
  Qed.

  Lemma threads_pool_steps p T σ I T' σ' :
    pool_steps p T σ I T' σ' →
    threads T ⊆ threads T'.
  Proof.
    induction 1; first done.
    etrans; first eapply threads_pool_step; eauto.
  Qed.


  Definition sub_pool T1 T2 := T1 ⊆+ T2.

  Lemma sub_pool_insert T1 T2  i j  e e':
    sub_pool T1 T2 →
    T1 !! i = Some e →
    T2 !! j = Some e →
    sub_pool (<[i := e']> T1) (<[j := e']> T2).
  Proof.
    intros Hsub H1 H2.
    eapply lookup_lt_Some in H1 as Hlt1.
    eapply lookup_lt_Some in H2 as Hlt2.
    eapply take_drop_middle in H1.
    eapply take_drop_middle in H2.
    rewrite -H1 -H2.
    rewrite !insert_app_r_alt; [|(rewrite take_length; lia)..].
    rewrite !take_length.
    replace (i - i `min` length T1) with 0 by lia.
    replace (j - j `min` length T2) with 0 by lia. simpl.
    rewrite -H1 -H2 in Hsub. revert Hsub.
    rewrite /sub_pool !cons_middle.
    rewrite !(Permutation_app_comm [e]) !(Permutation_app_comm [e']).
    rewrite !app_assoc.
    intros ?%submseteq_app_inv_r; by eapply submseteq_skips_r.
  Qed.

  Lemma sub_pool_lookup T1 T2 i e:
    sub_pool T1 T2 →
    T1 !! i = Some e →
    ∃ j, T2 !! j = Some e.
  Proof.
    intros Hsub Hlook. eapply elem_of_list_lookup_1, elem_of_submseteq;
    eauto using elem_of_list_lookup_2.
  Qed.

  Lemma sub_pool_singleton e i T :
    T !! i = Some e →
    sub_pool [e] T.
  Proof.
    intros Hlook. rewrite /sub_pool.
    eapply take_drop_middle in Hlook; rewrite -Hlook.
    eapply submseteq_cons_middle, submseteq_nil_l.
  Qed.





  (* TODO: do we even need these definitions? *)
  Definition reducible_pool p T σ := ∃ i T' σ', pool_step p T σ i T' σ'.
  Definition irreducible_pool p T σ := ∀ i T' σ', ¬ pool_step p T σ i T' σ'.


  Lemma reducible_pool_reducible p T σ:
    reducible_pool p T σ ↔ (∃ i e, T !! i = Some e ∧ reducible p e σ).
  Proof.
    split.
    - intros (i & T' & σ' & (e & e' & efs & Hstep & Hlook & Heq)%pool_step_iff).
      subst T'; rewrite /reducible; eauto 10.
    - intros (i & e & Hlook & (e' & σ' & efs & Hprim)); exists i, (<[i := e']> T ++ efs), σ'.
      eapply pool_step_iff; eauto 10.
  Qed.

  Lemma irreducible_pool_irreducible p T σ:
    irreducible_pool p T σ ↔ (∀ i e, T !! i = Some e → irreducible p e σ).
  Proof.
    split.
    - intros Hirred i e Hlook e' σ' efs Hstep. eapply Hirred, pool_step_iff; eauto 10.
    - intros Hirred i T' σ' (e & e' & efs & Hstep & Hlook & ->)%pool_step_iff.
      eapply Hirred; eauto.
  Qed.

  (** Reaching Stuck States/Safety *)
  (* a thread pool has undefined behavior, if one of its threads has undefined behavior. *)
  Definition stuck_pool p T σ := (∃ e i, T !! i = Some e ∧ stuck p e σ).
  Definition pool_reach_stuck p T σ :=
    ∃ T' σ' I, pool_steps p T σ I T' σ' ∧ stuck_pool p T' σ'.
  Definition pool_safe p T σ := ¬ pool_reach_stuck p T σ.


  Lemma pool_step_sub_pool p T1 T1' σ i T2 σ' :
    pool_step p T1 σ i T1' σ' →
    sub_pool T1 T2 →
    ∃ T2' j, sub_pool T1' T2' ∧ pool_step p T2 σ j T2' σ'.
  Proof.
    intros (e & e' & efs & Hstep & Hlook & ->)%pool_step_iff Hsub.
    eapply sub_pool_lookup in Hsub as Hidx; last done.
    destruct Hidx as (j & Hlook').
    exists (<[j := e']> T2 ++ efs), j.
    split; last (apply pool_step_iff; eauto 10).
    eapply submseteq_app; last done.
    eapply sub_pool_insert; eauto.
  Qed.

  Lemma pool_steps_sub_pool p T1 T1' σ I T2 σ' :
    pool_steps p T1 σ I T1' σ' →
    sub_pool T1 T2 →
    ∃ T2' J, sub_pool T1' T2' ∧ pool_steps p T2 σ J T2' σ'.
  Proof.
    induction 1 as [|T1 T1' T1'' σ σ' σ'' i I Hstep Hsteps IH] in T2; first by eauto using pool_steps.
    intros Hsub; eapply pool_step_sub_pool in Hstep as (T2' & j & Hpool & Hstep); last done.
    edestruct IH as (? & ? & ? & ?); eauto 10 using pool_steps.
  Qed.

  Lemma pool_reach_stuck_subs p T1 T2 σ:
    pool_reach_stuck p T1 σ →
    sub_pool T1 T2 →
    pool_reach_stuck p T2 σ.
  Proof.
    intros (T1' & σ' & I & Hsteps & Hstuck) Hsub.
    eapply pool_steps_sub_pool in Hsteps as (T2' & J & Hsub' & Hsteps'); last done.
    exists T2', σ', J; split; first done.
    destruct Hstuck as (e & i & Hlook & Hstuck).
    eapply sub_pool_lookup in Hsub' as (j & Hlook'); last done.
    exists e, j; split; eauto.
  Qed.


  Lemma pool_step_singleton p e σ i σ' T:
    pool_step p [e] σ i T σ' ↔
    (∃ e' efs, prim_step p e σ e' σ' efs ∧ T = e' :: efs ∧ i = 0).
  Proof.
    rewrite pool_step_iff. destruct i; simpl; naive_solver.
  Qed.

  Lemma pool_steps_values p T σ I T' σ' :
    pool_steps p T σ I T' σ' →
    (∀ e, e ∈ T → is_Some (to_val e)) →
    T' = T ∧ σ = σ' ∧ I = [].
  Proof.
    destruct 1 as [|T T' T'' σ σ' σ'' i I Hstep Hsteps]; eauto.
    intros Hvals.
    eapply pool_step_iff in Hstep as (e & e' & efs & Hstep & Hlook & Hupd).
    feed pose proof (Hvals e) as Irr; first by eapply elem_of_list_lookup_2.
    exfalso; eapply val_irreducible; eauto.
  Qed.

  Lemma pool_step_fill_context p e K i j σ σ' T T':
    pool_step p T σ j T' σ' →
    T !! i = Some e →
    ∃ e', T' !! i = Some e' ∧
    pool_step p (<[i := fill K e]> T) σ j (<[i := fill K e']> T') σ'.
  Proof.
    rewrite pool_step_iff; intros (e1 & e2 & efs & Hprim & Hlook & Hupd) Hlook1.
    destruct (decide (i = j)).
    - subst. assert (<[j:=e2]> T !! j = Some e2) as Hlook2.
      { eapply list_lookup_insert, lookup_lt_Some, Hlook. }
      exists e2; split; first eapply lookup_app_l_Some, Hlook2.
      rewrite insert_app_l; last by eapply lookup_lt_Some, Hlook2.
      rewrite list_insert_insert. assert (e1 = e) as -> by naive_solver.
      eapply pool_step_iff; exists (fill K e), (fill K e2), efs.
      split; first by eapply fill_prim_step.
      split; first eapply list_lookup_insert, lookup_lt_Some, Hlook.
      by rewrite list_insert_insert.
    - exists e. rewrite Hupd.
      rewrite (lookup_app_l_Some _ _ _ e);
        last by rewrite list_lookup_insert_ne //.
      rewrite insert_app_l;
        last (eapply lookup_lt_Some; rewrite list_lookup_insert_ne //).
      split; first done.
      rewrite list_insert_commute //.
      eapply pool_step_iff; exists e1, e2, efs.
      split; first done.
      split; first rewrite list_lookup_insert_ne //.
      done.
  Qed.

  Lemma pool_steps_fill_context p e K i I σ σ' T T':
    pool_steps p T σ I T' σ' →
    T !! i = Some e →
    ∃ e', T' !! i = Some e' ∧
    pool_steps p (<[i := fill K e]> T) σ I (<[i := fill K e']> T') σ'.
  Proof.
    induction 1 as [T σ|T T' T'' σ σ' σ'' j I Hstep Hsteps IH] in e.
    - eauto 10 using pool_steps.
    - intros Hlook.
      eapply pool_step_fill_context in Hlook as (e' & Hlook' & Hstep'); last done.
      eapply IH in Hlook' as (e'' & Hlook'' & Hstep'').
      eauto 10 using pool_steps.
  Qed.

  Lemma fill_reach_stuck_pool p T i e σ K :
    T !! i = Some e →
    pool_reach_stuck p T σ →
    pool_reach_stuck p (<[i := fill K e]> T) σ.
  Proof.
    intros Hlook (T' & σ' & I & Hsteps & Hstuck).
    eapply pool_steps_fill_context with (K := K) in Hsteps as (e' & Hlook' & Hsteps); last done.
    exists (<[i:=fill K e']> T'), σ', I; split; first done.
    destruct Hstuck as (e'' & j & Hlook'' & Hstuck).
    destruct (decide (i = j)).
    - subst. exists (fill K e'), j. assert (e'' = e') as -> by naive_solver.
      split; first eapply list_lookup_insert, lookup_lt_Some, Hlook'.
      eapply fill_stuck, Hstuck.
    - exists e'', j. rewrite list_lookup_insert_ne //.
  Qed.

  Lemma pool_steps_reach_stuck p T I T' σ σ':
    pool_steps p T σ I T' σ' → pool_reach_stuck p T' σ' → pool_reach_stuck p T σ.
  Proof.
    intros H (e'' & σ'' & J & Hstep & Hstuck).
    exists e'', σ'', (I ++ J). split; last assumption.
    by eapply pool_steps_trans.
  Qed.

  Lemma pool_steps_safe p T I T' σ σ':
    pool_steps p T σ I T' σ' → pool_safe p T σ → pool_safe p T' σ'.
  Proof.
    intros H1 H2 H3; by eapply H2, pool_steps_reach_stuck.
  Qed.

  Lemma pool_safe_call_in_prg p K T T' i I σ σ' f v:
    pool_safe p T σ →
    pool_steps p T σ I T' σ' →
    T' !! i = Some (fill K (of_call f v)) →
    ∃ K', p !! f = Some K'.
  Proof.
    destruct (p !! f) eqn: Hloook; eauto.
    intros Hsafe Hsteps Hlook. exfalso; eapply Hsafe.
    exists T', σ', I; split; first done.
    exists (fill K (of_call f v)), i.
    split; first done. eapply fill_stuck.
    split; first eapply to_val_of_call.
    intros  e'' σ'' efs Hstep.
    pose proof (prim_step_call_inv p empty_ectx f v e'' σ' σ'' efs) as Hinv.
    rewrite fill_empty in Hinv.
    eapply Hinv in Hstep as (K_f & Hprg & _); naive_solver.
  Qed.


  (* we define the unary versions of the above pool notions and lemmas *)
  Definition reach_stuck p e σ := pool_reach_stuck p [e] σ.
  Definition safe p e σ := ¬ reach_stuck p e σ.
  Definition no_fork p e σ e' σ' := prim_step p e σ e' σ' [].
  Inductive no_forks (p: prog Λ): expr Λ → state Λ → expr Λ → state Λ → Prop :=
    | no_forks_refl e σ: no_forks p e σ e σ
    | no_forks_step e e' e'' σ σ' σ'':
      no_fork p e σ e' σ' →
      no_forks p e' σ' e'' σ'' →
      no_forks p e σ e'' σ''.

  Lemma pool_reach_stuck_reach_stuck p e σ i T:
    reach_stuck p e σ →
    T !! i = Some e →
    pool_reach_stuck p T σ.
  Proof.
    intros Hstuck Hlook. eapply pool_reach_stuck_subs; first apply Hstuck.
    by eapply sub_pool_singleton.
  Qed.

  Lemma pool_safe_threads_safe p T σ i e:
    pool_safe p T σ →
    T !! i = Some e →
    safe p e σ.
  Proof.
    intros Hsafe Hlook Hstuck.
    by eapply Hsafe, pool_reach_stuck_reach_stuck.
  Qed.

  Lemma fill_no_fork p e e' σ σ' K :
    no_fork p e σ e' σ' → no_fork p (fill K e) σ (fill K e') σ'.
  Proof.
    intros ?; by eapply fill_prim_step.
  Qed.

  Lemma fill_no_forks p e e' σ σ' K :
    no_forks p e σ e' σ' → no_forks p (fill K e) σ (fill K e') σ'.
  Proof.
    induction 1; eauto using no_forks, fill_no_fork.
  Qed.

  Lemma fill_reach_stuck p e σ K :
    reach_stuck p e σ → reach_stuck p (fill K e) σ.
  Proof.
    intros Hreach; eapply fill_reach_stuck_pool with (T := [e]) (i := 0); done.
  Qed.

  Lemma no_forks_pool_steps p e σ e' σ':
    no_forks p e σ e' σ' →
    (∃ I, pool_steps p [e] σ I [e'] σ').
  Proof.
    induction 1 as [|e e' e'' σ σ' σ'' no_fork _ IH]; eauto using pool_steps.
    destruct IH as (I & Hsteps). exists (0 :: I).
    econstructor; first eapply pool_step_singleton; eauto 10.
  Qed.

  Lemma safe_call_in_prg p K e σ σ' f v:
    safe p e σ → no_forks p e σ (fill K (of_call f v)) σ' → ∃ K, p !! f = Some K.
  Proof.
    intros H1 (I & Hsteps)%no_forks_pool_steps.
    eapply pool_safe_call_in_prg with (i := 0) in Hsteps; eauto.
  Qed.

  Lemma no_forks_val p v σ e' σ' :
    no_forks p (of_val v) σ e' σ' → e' = of_val v ∧ σ' = σ.
  Proof.
    intros (I & Hsteps)%no_forks_pool_steps.
    eapply pool_steps_values in Hsteps; first naive_solver.
    intros e Hel. assert (e = of_val v) as -> by set_solver.
    rewrite to_of_val; eauto.
  Qed.

  Lemma val_safe p v σ : safe p (of_val v) σ.
  Proof.
    intros (T'&σ'& I & Hsteps & Hstuck).
    eapply pool_steps_values in Hsteps as (-> & -> & ->); last first.
    { intros e Hel. assert (e = of_val v) as -> by set_solver.
      rewrite to_of_val; eauto. }
    destruct Hstuck as (e & [] & Hlook & Hstuck); last naive_solver.
    destruct Hstuck as [Hstuck _]; simpl in Hlook.
    assert (e = of_val v) as -> by congruence.
    rewrite to_of_val in Hstuck. naive_solver.
  Qed.

End language.
