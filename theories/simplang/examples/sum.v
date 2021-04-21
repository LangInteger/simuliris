From simuliris.simplang Require Import lang notation tactics class_instances proofmode.
From iris Require Import bi.bi.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.


Section fix_bi.
Context `{sheapG Σ}.
Instance : sheapInv Σ := {|
  sheap_inv := ⌜True⌝%I;
 |}.


(* Sums are encoded as injL x -> (1, x); injR x -> (2, x); the tag encodes the constructor.  *)

Definition inj1_enc : ectx := (λ: "x", (#1, "x"))%E.
Definition inj2_enc : ectx := (λ: "x", (#2, "x"))%E.

Definition diverge : ectx := (λ: "x", Call "diverge" "x")%E.

(** the value relation determining which values can be passed to a function *)
Inductive val_rel_pure : val → val → Prop :=
  | val_rel_lit l : val_rel_pure (LitV l) (LitV l)
  | val_rel_injL v1 v2 : val_rel_pure v1 v2 → val_rel_pure ((#1, v1)%V) (InjLV v2)
  | val_rel_injR v1 v2 : val_rel_pure v1 v2 → val_rel_pure ((#2, v1)%V) (InjRV v2)
  | val_rel_pair v1 v2 v1' v2' :
      val_rel_pure v1 v1' →
      val_rel_pure v2 v2' →
      val_rel_pure ((v1, v2)%V) ((v1', v2')%V).
Local Hint Constructors val_rel_pure : core.
Definition val_rel v1 v2 : iProp Σ := (⌜val_rel_pure v1 v2⌝)%I.

Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

Definition mul2_source :=
  (λ: "x",
    match: "x" with
      InjL "x" => "x" * #2
    | InjR "x" => "x" + #2
    end)%E.

Definition mul2_target :=
  (λ: "x",
    if: Fst "x" = #1 then (Snd "x") * #2
      else if: Fst "x" = #2
        then (Snd "x") + #2
        else Call "diverge" #())%E.

Definition source_prog : gmap string ectx := {[ "inj1_enc" := inj1_enc; "diverge" := diverge; "mul2" := mul2_source ]}.
Definition target_prog : gmap string ectx := {[ "diverge" := diverge; "mul2" := mul2_target]}.

Lemma mul2_sim:
  ⊢ ∀ v_t v_s, val_rel v_t v_s -∗
    fill mul2_target (of_val v_t) ⪯ fill mul2_source (of_val v_s) {{ λ v_t' v_s', val_rel v_t' v_s' }}.
Proof.
  iIntros (?? Hval). rewrite /mul2_target /mul2_source.
  sim_pures.
  (* generate additional conditions on the shape of the source expression *)
  iApply sim_irred_unless; first done.
  iIntros "%Ha"; destruct Ha as (v' & [-> | ->]).
  - inversion Hval; subst.
    sim_pures.
    iApply sim_irred_unless; first done. iIntros "%Ha"; destruct Ha as [(n & ->) _].
    inversion H2; subst.
    by sim_pures.
  - inversion Hval; subst.
    sim_pures.
    iApply sim_irred_unless; first done. iIntros "%Ha"; destruct Ha as [(n & ->) _].
    inversion H2; subst.
    by sim_pures.
Qed.

Definition source_client := (λ: "x", Call (##"mul2") (InjL "x"))%E.
Definition target_client := (λ: "x", Call (## "mul2") (Call (##"inj1_enc") "x"))%E.

Lemma client_sim (n : Z) :
  "target_client" @t target_client -∗
  "source_client" @s source_client -∗
  "inj1_enc" @t inj1_enc -∗
  Call (##"target_client") #n ⪯ Call (##"source_client") #n {{ λ v_t v_s, val_rel v_t v_s }}.
Proof.
  iIntros "Htarget Hsource Hinj1_t".
  target_call. target_call. source_call. sim_pures.
  iApply sim_call; eauto.
Qed.
End fix_bi.
