
From iris.bi Require Import bi lib.fixpoint.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import relations language.
From iris.prelude Require Import options.
Import bi.

(* parameterized over "external" relation that restricts values passed to and
from external function calls *)
(* TODO: Hint Mode? *)
Class simulirisGS (PROP : bi) (Λ : language) := SimulirisGS {
  (* state interpretation *)
  state_interp : prog Λ → state Λ → prog Λ → state Λ → list (expr Λ) → PROP;
  state_interp_pure_prim_step P_t σ_t P_s σ_s e_s T π e_s':
    T !! π = Some e_s →
    (∀ σ_s, prim_step P_s e_s σ_s e_s' σ_s []) →
    state_interp P_t σ_t P_s σ_s T -∗
    state_interp P_t σ_t P_s σ_s (<[π:=e_s']>T);
  (* external function call relation *)
  ext_rel : thread_id → val Λ → val Λ → PROP;
}.

Definition progs_are {Λ PROP} `{simulirisGS PROP Λ} (P_t P_s : prog Λ) : PROP :=
  (□ ∀ P_t' P_s' σ_t σ_s T_s, state_interp P_t' σ_t P_s' σ_s T_s → ⌜P_t' = P_t⌝ ∧ ⌜P_s' = P_s⌝)%I.
#[global]
Hint Mode progs_are - - - + + : typeclass_instances.
Typeclasses Opaque progs_are.

Global Instance progs_are_persistent {Λ} {PROP} `{s : simulirisGS PROP Λ}
    (P_s P_t : prog Λ) :
  Persistent (@progs_are Λ PROP s P_s P_t).
Proof. rewrite /progs_are; apply _. Qed.

(** Typeclass for the simulation relation so we can use the definitions with
   greatest+least fp (stuttering) or just greatest fp (no stuttering). *)
Class Sim {PROP : bi} {Λ : language} (s : simulirisGS PROP Λ) :=
  sim : (val Λ → val Λ → PROP) → thread_id → expr Λ → expr Λ → PROP.
#[global]
Hint Mode Sim - - - : typeclass_instances.

Class SimE {PROP : bi} {Λ : language} (s : simulirisGS PROP Λ) :=
  sim_expr : (expr Λ → expr Λ → PROP) → thread_id → expr Λ → expr Λ → PROP.
#[global]
Hint Mode SimE - - - : typeclass_instances.

(* FIXME what are good levels for et, es? *)
Notation "et '⪯{' π '}' es {{ Φ }}" := (sim Φ π et es) (at level 40, Φ at level 200,
  format "et  '⪯{' π '}'  es  {{  Φ  }}") : bi_scope.

(* FIXME: the notation with binder doesn't work; left-factoring seems to fail.
Notation "et  '⪯'  es  {{  v_t  v_s ,  P  }}" := (sim et es (λ v_t v_s, P)) (at level 40, v_t, v_s at level 200, P at level 200) : bi_scope. *)


(* TODO: different symbols (no brackets) for expr thing *)
Notation "et '⪯{' π '}' es [{ Φ }]" := (sim_expr Φ π et es) (at level 40, Φ at level 200,
  format "et  '⪯{' π '}'  es  [{  Φ  }]") : bi_scope.




(* discrete OFE instance for expr and thread_id *)
Definition exprO {Λ : language} := leibnizO (expr Λ).
Instance expr_equiv {Λ} : Equiv (expr Λ). apply exprO. Defined.

Definition thread_idO := leibnizO thread_id.
Instance thread_id_equiv : Equiv thread_id. apply thread_idO. Defined.

(** * SLSLS, Separation Logic Stuttering Local Simulation *)
Section fix_lang.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language}.
  Context {s : simulirisGS PROP Λ}.

  Set Default Proof Using "Type*".

  Implicit Types (e_s e_t e: expr Λ).

  Definition sim_ectx `{!Sim s} π K_t K_s Φ :=
    (∀ v_t v_s, ext_rel π v_t v_s -∗ sim Φ π (fill K_t (of_val v_t)) (fill K_s (of_val v_s)))%I.
  Definition sim_expr_ectx `{!SimE s} π K_t K_s Φ :=
    (∀ v_t v_s, ext_rel π v_t v_s -∗ sim_expr Φ π (fill K_t (of_val v_t)) (fill K_s (of_val v_s)))%I.
End fix_lang.
