From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.


(** * Ghost state constructions for keeping track of the programs
  It provides a persistent token f @ K asserting that there is a function f with body K.
*)

Class gen_progGpreS (F C : Type) (Σ : gFunctors) `{Countable F} := {
  gen_prog_preG_inG :> ghost_mapG Σ F C;
}.

Class gen_progGS_named (F C : Type) (Σ : gFunctors) (gen_prog_name : gname) `{Countable F} := GenProgGSNamed {
  gen_prog_preNameG :> gen_progGpreS F C Σ
}.

Class gen_sim_progGS (F C_t C_s : Type) (Σ : gFunctors) `{Countable F} := GenSimProgG {
  gen_prog_name_target : gname;
  gen_prog_name_source : gname;
  gen_prog_inG_source :> gen_progGS_named F C_s Σ gen_prog_name_source;
  gen_prog_inG_target :> gen_progGS_named F C_t Σ gen_prog_name_target;
}.

Global Arguments GenSimProgG F C_t C_s Σ {_ _} _ _ {_ _}.
Global Arguments gen_prog_name_source {F C_t C_s Σ _ _} _ : assert.
Global Arguments gen_prog_name_target {F C_t C_s Σ _ _} _ : assert.

Section definitions.
  Context `{Countable F, gen_prog_name : gname, hG : !gen_progGS_named F C Σ gen_prog_name }.

  Definition gen_prog_interp (P : gmap F C) : iProp Σ :=
    ghost_map_auth gen_prog_name 1 P.

  Definition hasfun_def (fname : F) (K: C) : iProp Σ :=
    fname ↪[gen_prog_name]□ K.
  Definition hasfun_aux : seal (@hasfun_def). Proof. by eexists. Qed.
  Definition hasfun := hasfun_aux.(unseal).
  Definition hasfun_eq : @hasfun = @hasfun_def := hasfun_aux.(seal_eq).
End definitions.

Local Notation "f @ K" := (hasfun f K)
  (at level 20, format "f  @  K") : bi_scope.

Section gen_prog.
  Context {F C} `{Countable L, gen_prog_name : gname, gen_progGS_named F C Σ gen_prog_name}.
  Implicit Types P Q : iProp Σ.
  Implicit Types p : gmap F C.

  (** General properties of hasfun *)
  Global Instance hasfun_timeless f K : Timeless (f @ K).
  Proof. rewrite hasfun_eq. apply _. Qed.
  Global Instance hasfun_persistent f K : Persistent (f @ K).
  Proof. rewrite hasfun_eq. apply _. Qed.

  Lemma hasfun_agree f K1 K2 : f @ K1 -∗ f @ K2 -∗ ⌜K1 = K2⌝.
  Proof. rewrite hasfun_eq. iApply ghost_map_elem_agree. Qed.

  Lemma gen_prog_valid p f K : gen_prog_interp p -∗ f @ K -∗ ⌜p !! f = Some K⌝.
  Proof.
    iIntros "Hp Hl". rewrite /gen_prog_interp hasfun_eq.
    by iDestruct (ghost_map_lookup with "Hp Hl") as %?.
  Qed.

  (** The following lemmas should usually only be needed for initial allocation,
    as functions will not be added at intermediate points. *)
  Lemma gen_prog_alloc p f K :
    p !! f = None →
    gen_prog_interp p ==∗ gen_prog_interp (<[f:=K]>p) ∗ f @ K.
  Proof.
    iIntros (Hpl). rewrite /gen_prog_interp hasfun_eq /hasfun_def /=.
    iIntros "Hp".
    iMod (ghost_map_insert_persist f with "Hp") as "[Hp Hf]"; first done.
    iModIntro. by iFrame "Hf".
  Qed.

  Lemma gen_prog_alloc_big p p' :
    p' ##ₘ p →
    gen_prog_interp p ==∗
    gen_prog_interp (p' ∪ p) ∗ ([∗ map] f ↦ K ∈ p', f @ K).
  Proof.
    revert p; induction p' as [| f K p' Hf IH] using map_ind; iIntros (p Hdisj) "Hp".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hp") as "[Hp'p Hp']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (gen_prog_alloc with "Hp'p") as "($ & $)";
      first by apply lookup_union_None.
  Qed.
End gen_prog.

Lemma gen_prog_init_names `{Countable F, !gen_progGpreS F C Σ} p :
  ⊢ |==> ∃ γp : gname,
    let hG := GenProgGSNamed F C Σ γp in
    gen_prog_interp p ∗ ([∗ map] f ↦ K ∈ p, f @ K).
Proof.
  iMod (ghost_map_alloc_empty (K:=F) (V:=C)) as (γp) "Hp".
  iExists γp.
  iAssert (gen_prog_interp (hG:=GenProgGSNamed _ _ _ γp _ _ _) ∅) with "[Hp]" as "Hinterp";
    first by iFrame "Hp".
  iMod (gen_prog_alloc_big with "Hinterp") as "(Hinterp & $)".
  { apply map_disjoint_empty_r. }
  rewrite right_id_L. done.
Qed.

Lemma gen_prog_init `{Countable F, !gen_progGpreS F C_t Σ, !gen_progGpreS F C_s Σ} P_t P_s :
  ⊢ |==> ∃ _ : gen_sim_progGS F C_t C_s Σ,
    (gen_prog_interp (hG:=gen_prog_inG_target) P_t ∗
    ([∗ map] f ↦ K ∈ P_t, hasfun (hG:=gen_prog_inG_target) f K)) ∗
    (gen_prog_interp (hG:=gen_prog_inG_source) P_s ∗
    ([∗ map] f ↦ K ∈ P_s, hasfun (hG:=gen_prog_inG_source) f K)).
Proof.
  iMod (gen_prog_init_names P_t) as (γt) "Hinit_t".
  iMod (gen_prog_init_names P_s) as (γs) "Hinit_s".
  iExists (GenSimProgG _ _ _ _ γt γs). iModIntro; iFrame.
Qed.
