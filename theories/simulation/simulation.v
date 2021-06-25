
From iris.bi Require Import bi lib.fixpoint.
From iris.prelude Require Import prelude.
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

(** Typeclass for the simulation relation so we can use the definitions with
   greatest+least fp (stuttering) or just greatest fp (no stuttering). *)
Class Sim (PROP : bi) (Λ : language) {s : simulirisGS PROP Λ} :=
  sim : (val Λ → val Λ → PROP) → thread_id → expr Λ → expr Λ → PROP.
#[global]
Hint Mode Sim - - - : typeclass_instances.

Class SimE (PROP : bi) (Λ : language) {s : simulirisGS PROP Λ} :=
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



Section fix_lang.
  Context {PROP : bi}.
  Context {Λ : language}.
  Context `{!simulirisGS PROP Λ}.

  Definition progs_are (P_t P_s : prog Λ) : PROP :=
    (□ ∀ P_t' P_s' σ_t σ_s T_s, state_interp P_t' σ_t P_s' σ_s T_s → ⌜P_t' = P_t⌝ ∧ ⌜P_s' = P_s⌝)%I.

  Global Instance progs_are_persistent (P_s P_t : prog Λ) :
    Persistent (progs_are P_s P_t).
  Proof. rewrite /progs_are; apply _. Qed.

  (** Lift simulation to whole-program relation *)
  Definition prog_rel `{!Sim PROP Λ} (P_t P_s : prog Λ) : PROP :=
    (□ ∀ f x_s e_s, ⌜P_s !! f = Some (x_s, e_s)⌝ →
       ∃ x_t e_t, ⌜P_t !! f = Some (x_t, e_t)⌝ ∗
         ∀ v_t v_s π, ext_rel π v_t v_s -∗
           (subst_map {[x_t:=v_t]} e_t) ⪯{π} (subst_map {[x_s:=v_s]} e_s) {{ ext_rel π }})%I.

  Global Instance prog_rel_persistent `{!Sim PROP Λ} P_t P_s : Persistent (prog_rel P_t P_s).
  Proof. rewrite /prog_rel; apply _. Qed.
End fix_lang.

Global Hint Mode progs_are - - - + + : typeclass_instances.
Typeclasses Opaque prog_rel.
