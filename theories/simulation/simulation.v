
From iris.bi Require Import bi lib.fixpoint.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import relations language.
From iris.prelude Require Import options.
Import bi.

(* parameterized over value relation that restricts values passed to functions *)
Class simulirisG (PROP : bi) (Λ : language) := {
  (* state interpretation *)
  state_interp : prog Λ → state Λ → prog Λ → state Λ → list (expr Λ) → PROP;
  state_interp_pure_prim_step P_t σ_t P_s σ_s e_s T π e_s':
    T !! π = Some e_s →
    (∀ σ_s, prim_step P_s e_s σ_s e_s' σ_s []) →
    state_interp P_t σ_t P_s σ_s T -∗
    state_interp P_t σ_t P_s σ_s (<[π:=e_s']>T)
}.
#[global]
Hint Mode simulirisG + - : typeclass_instances.

Definition progs_are {Λ PROP} `{simulirisG PROP Λ} (P_t P_s : prog Λ) : PROP :=
  (□ ∀ P_t' P_s' σ_t σ_s T_s, state_interp P_t' σ_t P_s' σ_s T_s → ⌜P_t' = P_t⌝ ∧ ⌜P_s' = P_s⌝)%I.
#[global]
Hint Mode progs_are - - - + + : typeclass_instances.
Typeclasses Opaque progs_are.

Global Instance progs_are_persistent {Λ} {PROP} `{s : simulirisG PROP Λ}
    (P_s P_t : prog Λ) :
  Persistent (@progs_are Λ PROP s P_s P_t).
Proof. rewrite /progs_are; apply _. Qed.

(** Typeclass for the simulation relation so we can use the definitions with
   greatest+least fp (stuttering) or just greatest fp (no stuttering). *)
Class Sim {PROP : bi} {Λ : language} (s : simulirisG PROP Λ) :=
  sim : (val Λ → val Λ → PROP) → (val Λ → val Λ → PROP) → thread_id → expr Λ → expr Λ → PROP.
#[global]
Hint Mode Sim - - - : typeclass_instances.

Class SimE {PROP : bi} {Λ : language} (s : simulirisG PROP Λ) :=
  sim_expr : (val Λ → val Λ → PROP) → (expr Λ → expr Λ → PROP) → thread_id → expr Λ → expr Λ → PROP.
#[global]
Hint Mode SimE - - - : typeclass_instances.

(* FIXME what are good levels for et, es? *)
Notation "et '⪯{' π , Ω '}' es {{ Φ }}" := (sim Ω Φ π et es) (at level 40, Φ at level 200,
  format "et  '⪯{' π ,  Ω '}'  es  {{  Φ  }}") : bi_scope.

(* FIXME: the notation with binder doesn't work; left-factoring seems to fail.
Notation "et  '⪯'  es  {{  v_t  v_s ,  P  }}" := (sim et es (λ v_t v_s, P)) (at level 40, v_t, v_s at level 200, P at level 200) : bi_scope. *)


(* TODO: different symbols (no brackets) for expr thing *)
Notation "et '⪯{' π , Ω '}' es [{ Φ }]" := (sim_expr Ω Φ π et es) (at level 40, Φ at level 200,
  format "et  '⪯{' π ,  Ω '}'  es  [{  Φ  }]") : bi_scope.




(* discrete OFE instance for expr and thread_id *)
Definition exprO {Λ : language} := leibnizO (expr Λ).
Instance expr_equiv {Λ} : Equiv (expr Λ). apply exprO. Defined.

Definition thread_idO := leibnizO thread_id.
Instance thread_id_equiv : Equiv thread_id. apply thread_idO. Defined.

(** * SLSLS, Separation Logic Stuttering Local Simulation *)
Section fix_lang.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language}.
  Context (Ω : val Λ → val Λ → PROP).
  Context {s : simulirisG PROP Λ}.

  Set Default Proof Using "Type*".

  Implicit Types (e_s e_t e: expr Λ).

  Definition sim_ectx `{!Sim s} π K_t K_s Φ :=
    (∀ v_t v_s, Ω v_t v_s -∗ sim Ω Φ π (fill K_t (of_val v_t)) (fill K_s (of_val v_s)))%I.
  Definition sim_expr_ectx `{!SimE s} π K_t K_s Φ :=
    (∀ v_t v_s, Ω v_t v_s -∗ sim_expr Ω Φ π (fill K_t (of_val v_t)) (fill K_s (of_val v_s)))%I.
End fix_lang.
