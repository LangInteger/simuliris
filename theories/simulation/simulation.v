
From iris.bi Require Import bi lib.fixpoint.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import relations language.
From iris.prelude Require Import options.
Import bi.

(* parameterized over value relation that restricts values passed to functions *)
Class SimulLang (PROP : bi) (Λ : language) := {
  (* state interpretation *)
  state_interp : prog Λ → state Λ → prog Λ → state Λ → PROP;
}.
#[global]
Hint Mode SimulLang + - : typeclass_instances.

Definition progs_are {Λ PROP} `{SimulLang PROP Λ} (P_t P_s : prog Λ) : PROP :=
  (□ ∀ P_t' P_s' σ_t σ_s, state_interp P_t' σ_t P_s' σ_s → ⌜P_t' = P_t⌝ ∧ ⌜P_s' = P_s⌝)%I.
#[global]
Hint Mode progs_are - - - + + : typeclass_instances.
Typeclasses Opaque progs_are.

Global Instance progs_are_persistent {Λ} {PROP} `{s : SimulLang PROP Λ}
    (P_s P_t : prog Λ) :
  Persistent (@progs_are Λ PROP s P_s P_t).
Proof. rewrite /progs_are; apply _. Qed.

(** Typeclass for the simulation relation so we can use the definitions with
   greatest+least fp (stuttering) or just greatest fp (no stuttering). *)
Class Sim {PROP : bi} {Λ : language} (s : SimulLang PROP Λ) :=
  sim : (val Λ → val Λ → PROP) → (val Λ → val Λ → PROP) → expr Λ → expr Λ → PROP.
#[global]
Hint Mode Sim - - - : typeclass_instances.

Class SimE {PROP : bi} {Λ : language} (s : SimulLang PROP Λ) :=
  sim_expr : (val Λ → val Λ → PROP) → (expr Λ → expr Λ → PROP) → expr Λ → expr Λ → PROP.
#[global]
Hint Mode SimE - - - : typeclass_instances.

(* FIXME what are good levels for et, es? *)
Notation "et '⪯{' Ω '}' es {{ Φ }}" := (sim Ω Φ et es) (at level 40, Φ at level 200,
  format "et  '⪯{' Ω '}'  es  {{  Φ  }}") : bi_scope.

(* FIXME: the notation with binder doesn't work; left-factoring seems to fail.
Notation "et  '⪯'  es  {{  v_t  v_s ,  P  }}" := (sim et es (λ v_t v_s, P)) (at level 40, v_t, v_s at level 200, P at level 200) : bi_scope. *)


(* TODO: different symbols (no brackets) for expr thing *)
Notation "et '⪯{' Ω '}' es [{ Φ }]" := (sim_expr Ω Φ et es) (at level 40, Φ at level 200,
  format "et  '⪯{' Ω '}'  es  [{  Φ  }]") : bi_scope.




(* discrete OFE instance for expr *)
Definition exprO {Λ : language} := leibnizO (expr Λ).
Instance expr_equiv {Λ} : Equiv (expr Λ). apply exprO. Defined.

(** * SLSLS, Separation Logic Stuttering Local Simulation *)
Section fix_lang.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language}.
  Context (Ω : val Λ → val Λ → PROP).
  Context {s : SimulLang PROP Λ}.

  Set Default Proof Using "Type*".

  Implicit Types (e_s e_t e: expr Λ).

  Definition sim_ectx `{!Sim s} K_t K_s Φ :=
    (∀ v_t v_s, Ω v_t v_s -∗ sim Ω Φ (fill K_t (of_val v_t)) (fill K_s (of_val v_s)))%I.
  Definition sim_expr_ectx `{!SimE s} K_t K_s Φ :=
    (∀ v_t v_s, Ω v_t v_s -∗ sim_expr Ω Φ (fill K_t (of_val v_t)) (fill K_s (of_val v_s)))%I.
End fix_lang.

