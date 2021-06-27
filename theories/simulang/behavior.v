From stdpp Require Import gmap.
From iris.prelude Require Import prelude.
From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import behavior.
From simuliris.simulang Require Import lang notation wf gen_val_rel.

From iris.prelude Require Import options.

(** Define "observable behavior" and contextual refinement. *)

(** We currently don't allow global variables that initially contain
pointers. However, this is not a real restriction as [main] can
store pointers in global variables. (In fact, it would be good
enough to 0-initialize all global variables.) *)
Definition init_state (σ_t σ_s : state) : Prop :=
  ∃ gs, map_Forall (λ _ v, val_wf v) gs ∧ σ_t = state_init gs ∧ σ_s = state_init gs.

Fixpoint obs_val (v_t v_s : val) {struct v_s} : Prop :=
  match v_t, v_s with
  | LitV (LitLoc l_t), LitV (LitLoc l_s) =>
    True (* the details of locations are not observable *)
  | LitV l_t, LitV l_s =>
    l_t = l_s
  | PairV v1_t v2_t, PairV v1_s v2_s =>
    obs_val v1_t v1_s ∧ obs_val v2_t v2_s
  | InjLV v_t, InjLV v_s =>
    obs_val v_t v_s
  | InjRV v_t, InjRV v_s =>
    obs_val v_t v_s
  | _,_ => False
  end.

(** The simulang instance of [beh_rel]. *)
Definition beh_rel := beh_rel init_state "main" #() obs_val.

(** Default well-formedness for SimuLang. *)
Definition simulang_wf (e : expr_head) : Prop :=
  match e with
  | ValHead v => val_wf v
  (* Na2Ord is an intermediate (administrative) ordering that should only
       arise during execution and programs should not use it directly. *)
  | LoadHead o => o ≠ Na2Ord
  | StoreHead o => o ≠ Na2Ord
  | _ => True
  end.

Notation expr_wf := (gen_expr_wf simulang_wf).
Notation ectx_wf := (gen_ectx_wf simulang_wf).
Notation ctx_wf := (gen_ctx_wf simulang_wf).

(** Contextual refinement. *)
Definition ctx_rel (e_t e_s : expr) :=
  ∀ (C : ctx) (fname x : string) (p : prog),
    (* The other functions need to be well-formed and closed *)
    map_Forall (λ _ '(arg, body), expr_wf body ∧ free_vars body ⊆ {[arg]}) p →
    (* The context needs to be well-formed *)
    ctx_wf C →
    (* The context needs to close our expressions *)
    free_vars (fill_ctx C e_t) ∪ free_vars (fill_ctx C e_s) ⊆ {[x]} →
    (* Then we demand [beh_rel] if putting our expressions into a context to
       obtain a whole function and that function into a program *)
    beh_rel (<[fname := (x, fill_ctx C e_t)]> p) (<[fname := (x, fill_ctx C e_s)]> p).
