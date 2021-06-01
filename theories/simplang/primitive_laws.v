(** This file proves the basic laws of the SimpLang program logic by applying
the Simuliris lifting lemmas. *)

From iris.proofmode Require Export tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.simplang Require Export class_instances tactics notation ghost_state.
From iris.prelude Require Import options.

Class sheapGS (Σ: gFunctors) := SHeapGS {
  sheapG_gen_heapG :> heapGS Σ;
  sheapG_gen_progG :> gen_sim_progGS string ectx ectx Σ;
  sheapG_allocN_source : heap_names;
  sheapG_allocN_target : heap_names;
}.

(** This class is instantiated per proof (usually at the beginning of the file).
   It states additional components of the state interpretation, i.e.,
   invariants on the relation of source and target programs and states.
 *)
Class sheapInv (Σ : gFunctors) := SHeapRel {
  sheap_inv : prog → state → prog → state → list expr → iProp Σ;
  sheap_inv_pure_prim_step P_t σ_t P_s σ_s e_s T π e_s':
    T !! π = Some e_s →
    (∀ σ_s, prim_step P_s e_s σ_s e_s' σ_s []) →
    sheap_inv P_t σ_t P_s σ_s T -∗
    sheap_inv P_t σ_t P_s σ_s (<[π:=e_s']>T)
}.

Class sheapInvConst `{!sheapInv Σ} := {
  sheap_inv_const P_t1 σ_t1 P_s1 σ_s1 T1 P_t2 σ_t2 P_s2 σ_s2 T2:
    sheap_inv P_t1 σ_t1 P_s1 σ_s1 T1 -∗ sheap_inv P_t2 σ_t2 P_s2 σ_s2 T2
}.

Global Program Instance sheapG_simulirisG `{!sheapGS Σ} `{!sheapInv Σ} : simulirisG (iPropI Σ) simp_lang := {
  state_interp P_t σ_t P_s σ_s T_s :=
    (gen_prog_interp (hG := gen_prog_inG_target) P_t ∗
     gen_prog_interp (hG := gen_prog_inG_source) P_s ∗
     heap_ctx sheapG_allocN_target σ_t.(heap) σ_t.(used_blocks) ∗
     heap_ctx sheapG_allocN_source σ_s.(heap) σ_s.(used_blocks) ∗
     sheap_inv P_t σ_t P_s σ_s T_s
    )%I;
}.
Next Obligation.
  iIntros (?????????????) "($&$&$&$&?)".
  by iApply sheap_inv_pure_prim_step.
Qed.

(* TODO: add dfrac notions back if the heap supports them*)
Notation "l '↦t[' st ']{#' q } v" := (heap_mapsto sheapG_allocN_target l st q v%V)
  (at level 20, format "l  ↦t[ st ]{# q }  v") : bi_scope.
Notation "l '↦t[' st ] v" := (heap_mapsto sheapG_allocN_target l st 1 v%V)
  (at level 20, format "l  ↦t[ st ]  v") : bi_scope.
Notation "l '↦t{#' q } v" := (heap_mapsto sheapG_allocN_target l (RSt 0) q v%V)
  (at level 20, format "l  ↦t{# q }  v") : bi_scope.
Notation "l '↦t' v" := (heap_mapsto sheapG_allocN_target l (RSt 0) 1 v%V)
  (at level 20, format "l  ↦t  v") : bi_scope.
Notation "l '↦s[' st ']{#' q } v" := (heap_mapsto sheapG_allocN_source l st q v%V)
  (at level 20, format "l  ↦s[ st ]{# q }  v") : bi_scope.
Notation "l '↦s[' st ] v" := (heap_mapsto sheapG_allocN_source l st 1 v%V)
  (at level 20, format "l  ↦s[ st ]  v") : bi_scope.
Notation "l '↦s{#' q } v" := (heap_mapsto sheapG_allocN_source l (RSt 0) q v%V)
  (at level 20, format "l  ↦s{# q }  v") : bi_scope.
Notation "l '↦s' v" := (heap_mapsto sheapG_allocN_source l (RSt 0) 1 v%V)
  (at level 20, format "l  ↦s  v") : bi_scope.

Notation "l ↦t∗[ st ]{# q } vs" := (heap_mapsto_vec_st sheapG_allocN_target l st q vs)
  (at level 20, format "l  ↦t∗[ st ]{# q }  vs") : bi_scope.
Notation "l ↦t∗[ st ] vs" := (heap_mapsto_vec_st sheapG_allocN_target l st 1 vs)
  (at level 20, format "l  ↦t∗[ st ]  vs") : bi_scope.
Notation "l ↦t∗{# q } vs" := (heap_mapsto_vec sheapG_allocN_target l q vs)
  (at level 20, format "l  ↦t∗{# q }  vs") : bi_scope.
Notation "l ↦t∗ vs" := (heap_mapsto_vec sheapG_allocN_target l 1 vs)
  (at level 20, format "l  ↦t∗  vs") : bi_scope.
Notation "l ↦s∗[ st ]{# q } vs" := (heap_mapsto_vec_st sheapG_allocN_source l st q vs)
  (at level 20, format "l  ↦s∗[ st ]{# q }  vs") : bi_scope.
Notation "l ↦s∗[ st ] vs" := (heap_mapsto_vec_st sheapG_allocN_source l st 1 vs)
  (at level 20, format "l  ↦s∗[ st ]  vs") : bi_scope.
Notation "l ↦s∗{# q } vs" := (heap_mapsto_vec sheapG_allocN_source l q vs)
  (at level 20, format "l  ↦s∗{# q }  vs") : bi_scope.
Notation "l ↦s∗ vs" := (heap_mapsto_vec sheapG_allocN_source l 1 vs)
  (at level 20, format "l  ↦s∗  vs") : bi_scope.

(** Program assertions *)
Notation "f '@t' Kt" := (hasfun (hG:=gen_prog_inG_target) f Kt)
  (at level 20, format "f  @t  Kt") : bi_scope.
Notation "f '@s' Ks" := (hasfun (hG:=gen_prog_inG_source) f Ks)
  (at level 20, format "f  @s  Ks") : bi_scope.

(** Allocation size notation *)
Notation "† l '…?t' n" := (heap_freeable sheapG_allocN_target l 1 n)
  (at level 20, format "† l …?t  n") : bi_scope.
Notation "† l '…t' n" := (heap_freeable sheapG_allocN_target l 1 (Some n))
  (at level 20, format "† l …t  n") : bi_scope.
Notation "† l '…t' -" := (heap_freeable sheapG_allocN_target l 1 None)
  (at level 20, format "† l …t  -") : bi_scope.
Notation "† l '…?s' n" := (heap_freeable sheapG_allocN_source l 1 n)
  (at level 20, format "† l …?s  n") : bi_scope.
Notation "† l '…s' n" := (heap_freeable sheapG_allocN_source l 1 (Some n))
  (at level 20, format "† l …s  n") : bi_scope.
Notation "† l '…s' -" := (heap_freeable sheapG_allocN_source l 1 None)
  (at level 20, format "† l …s  -") : bi_scope.


Section lifting.
Context `{!sheapGS Σ} `{!sheapInv Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → val → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types v v_s v_t : val.
Implicit Types l : loc.
Implicit Types f : fname.
Implicit Types π : thread_id.

Context (Ω : thread_id → val → val → iProp Σ) (π : thread_id).
Local Notation "et '⪯' es [{ Φ }]" := (et ⪯{π, Ω} es [{Φ}])%I (at level 40, Φ at level 200) : bi_scope.

(** Program for target *)
Lemma hasfun_target_agree f K_t1 K_t2 : f @t K_t1 -∗ f @t K_t2 -∗ ⌜K_t1 = K_t2⌝.
Proof. apply hasfun_agree. Qed.

(** Program for source *)
Lemma hasfun_source_agree f K_s1 K_s2 : f @s K_s1 -∗ f @s K_s2 -∗ ⌜K_s1 = K_s2⌝.
Proof. apply hasfun_agree. Qed.


(** operational heap lemmas *)

Lemma target_red_allocN n v Ψ `{!sheapInvConst}:
  (0 < n)%Z →
  (∀ l, l ↦t∗ (replicate (Z.to_nat n) v) -∗
    † l …t (Z.to_nat n) -∗ target_red (of_val #l) Ψ) -∗
  target_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Ψ.
Proof.
  iIntros (Hn) "Hloc". iApply target_red_lift_head_step.
  iIntros (P_s σ_s P_t σ_t T_s) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)". iModIntro.
  iSplitR. { eauto using alloc_fresh with head_step. }
  iIntros (e_t' efs_t σ_t') "%"; inv_head_step.
  set (l := Loc b 0).
  iMod (heap_alloc _ _ l with "Hσ_t") as "($&Hn&Hm)"; [done..|].
  iModIntro. iFrame. iSplitR; first done.
  iSplitL "Hinv". { by iApply sheap_inv_const. }
  by iApply ("Hloc" with "Hm Hn").
Qed.

Lemma source_red_allocN n v Ψ `{!sheapInvConst}:
  (0 < n)%Z →
  (∀ l, l ↦s∗ (replicate (Z.to_nat n) v) -∗
  † l …s Z.to_nat n -∗ source_red (of_val #l) π Ψ) -∗
  source_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) π Ψ.
Proof.
  iIntros (Hn) "Hloc". iApply source_red_lift_head_step.
  iIntros (P_s σ_s P_t σ_t T_s K_s) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _]".
  iExists _, _. iSplitR. { simpl. eauto using alloc_fresh with lia head_step. }
  simpl.
  iMod (heap_alloc _ _ (Loc (fresh_block (heap σ_s) (used_blocks σ_s)) 0) with "Hσ_s") as "($&Hn&Hm)"; [done|done| | |].
  { apply is_fresh_block_blocks. }
  { move => ?. apply is_fresh_block. }
  iModIntro. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_const. }
  by iApply ("Hloc" with "Hm Hn").
Qed.

Lemma target_red_alloc v Ψ `{!sheapInvConst}:
  (∀ l, l ↦t v -∗ † l …t 1 -∗ target_red (of_val #l) Ψ) -∗
  target_red (Alloc (Val v)) Ψ.
Proof.
  iIntros "Ht". iApply (target_red_allocN); first lia.
  have ->: (Z.to_nat 1 = 1) by lia. simpl.
  iIntros (l). rewrite heap_mapsto_vec_singleton. iApply "Ht".
Qed.

Lemma source_red_alloc v Ψ `{!sheapInvConst}:
  (∀ l, l ↦s v -∗ † l …s 1 -∗ source_red (of_val #l) π Ψ) -∗
  source_red (Alloc (Val v)) π Ψ.
Proof.
  iIntros "Ht". iApply (source_red_allocN); first lia.
  have ->: (Z.to_nat 1 = 1) by lia. simpl.
  iIntros (l). rewrite heap_mapsto_vec_singleton. iApply "Ht".
Qed.

Lemma target_red_freeN vs l (n : Z) Ψ `{!sheapInvConst} :
  n = length vs →
  l ↦t∗ vs -∗
  † l …t Z.to_nat n -∗
  († l …t - -∗ target_red (of_val #()) Ψ) -∗
  target_red (FreeN (Val $ LitV $ LitInt n) (Val $ LitV (LitLoc l))) Ψ.
Proof.
  iIntros (->) "Hl Hn Hsim". iApply target_red_lift_head_step. rewrite Nat2Z.id.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  rewrite heap_mapsto_vec_to_st.
  iMod (heap_free with "Hσ_t Hl Hn") as (??) "[? ?]"; [ done| ].
  iSplitR; first by eauto with lia head_step.
  iIntros "!>" (e_t' efs σ_t') "%"; inv_head_step.
  iModIntro. iFrame. iSplitR; first done.
  iSplitL "Hinv". { by iApply sheap_inv_const. }
    by iApply "Hsim".
Qed.

Lemma target_red_free v l Ψ `{!sheapInvConst} :
  l ↦t v -∗
  † l …t 1 -∗
  († l …t - -∗ target_red (of_val #()) Ψ) -∗
  target_red (FreeN (Val $ LitV $ LitInt 1) (Val $ LitV (LitLoc l))) Ψ.
Proof.
  iIntros "Hl Hn". replace (1) with (Z.to_nat 1) by lia.
  iApply (target_red_freeN [v] with "[Hl] [Hn]"); [ done..| |done].
  by rewrite heap_mapsto_vec_singleton.
Qed.

Lemma source_red_freeN vs l (n : Z) Ψ `{!sheapInvConst} :
  n = length vs →
  l ↦s∗ vs -∗
  † l …s (Z.to_nat n) -∗
  († l …s - -∗ source_red (of_val #()) π Ψ) -∗
  source_red (FreeN (Val $ LitV $ LitInt n) (Val $ LitV (LitLoc l))) π Ψ.
Proof.
  iIntros (->) "Hl Hn Hsim". iApply source_red_lift_head_step. rewrite Nat2Z.id.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _]".
  rewrite heap_mapsto_vec_to_st.
  iMod (heap_free with "Hσ_s Hl Hn") as (??) "[? ?]"; [ done | ].
  iExists (Val #()), (state_upd_heap (free_mem l _) σ_s).
  iSplitR; first eauto with lia head_step.
  { iPureIntro. econstructor; eauto with lia. }
  iModIntro. iModIntro. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_const. }
    by iApply "Hsim".
Qed.

Lemma source_red_free v l Ψ `{!sheapInvConst} :
  l ↦s v -∗
  † l …s 1 -∗
  († l …s - -∗ source_red (of_val #()) π Ψ) -∗
  source_red (FreeN (Val $ LitV $ LitInt 1) (Val $ LitV (LitLoc l))) π Ψ.
Proof.
  iIntros "Hl Hn". replace (1) with (Z.to_nat 1) by lia.
  iApply (source_red_freeN [v] with "[Hl] Hn"); [ done.. |].
  by rewrite heap_mapsto_vec_singleton.
Qed.

Lemma target_red_load_sc l q v Ψ :
  l ↦t{#q} v -∗
  (l ↦t{#q} v -∗ target_red (of_val v) Ψ) -∗
  target_red (Load ScOrd (Val $ LitV $ LitLoc l)) Ψ.
Proof.
  iIntros "Hl Ht". iApply target_red_lift_head_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iDestruct (heap_read with "Hσ_t Hl") as %[??]. iModIntro.
  iSplit; first by eauto with head_step.
  iIntros (??? Hstep); inv_head_step.
  iModIntro. iFrame. iSplit;[done|]. by iApply "Ht".
Qed.

Lemma target_red_load_na l q v Ψ `{!sheapInvConst} :
  l ↦t{#q} v -∗
  (l ↦t{#q} v -∗ target_red (of_val v) Ψ) -∗
  target_red (Load Na1Ord (Val $ LitV $ LitLoc l)) Ψ.
Proof.
  iIntros "Hl Ht". iApply target_red_lift_head_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iMod (heap_read_na with "Hσ_t Hl") as (n ?) "[Hσ_t Hcont]". iModIntro.
  iSplit; first by eauto with head_step.
  iIntros (??? Hstep) "!>"; inv_head_step.
  iFrame. iSplitR; [done|].
  iSplitL "Hinv". { by iApply sheap_inv_const. }

  iApply target_red_lift_head_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iMod ("Hcont" with "Hσ_t") as (? ?) "[Hσ_t Hm]". iModIntro.
  iSplit; first by eauto with head_step.
  iIntros (??? Hstep) "!>"; inv_head_step.
  iFrame. iSplitR; [done|].
  iSplitL "Hinv". { by iApply sheap_inv_const. }
  by iApply "Ht".
Qed.

Lemma source_red_load_sc l q v Ψ `{!sheapInvConst} :
  l ↦s{#q} v -∗
  (l ↦s{#q} v -∗ source_red (of_val v) π Ψ) -∗
  source_red (Load ScOrd (Val $ LitV $ LitLoc l)) π Ψ.
Proof.
  iIntros "Hl Ht". iApply source_red_lift_head_step.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _]".
  iDestruct (heap_read with "Hσ_s Hl") as %[??]. iModIntro.
  assert (∃ e_s' σ_s', head_step P_s (Load ScOrd #l) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplit; first by eauto. inv_head_step.
  iModIntro. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_const. }
    by iApply "Ht".
Qed.

Lemma source_red_load_na l v Ψ q `{!sheapInvConst} :
  l ↦s{#q} v -∗
  (l ↦s{#q} v -∗ source_red (of_val v) π Ψ) -∗
  source_red (Load Na1Ord (Val $ LitV $ LitLoc l)) π Ψ.
Proof.
  iIntros "Hl Ht". iApply source_red_lift_head_step.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _]".
  iMod (heap_read_na with "Hσ_s Hl") as (n ?) "[Hσ_s Hcont]". iModIntro.
  assert (∃ e_s' σ_s', head_step P_s (Load Na1Ord #l) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplit; first by eauto. inv_head_step.
  iModIntro. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_const. }

  iApply source_red_lift_head_step.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _]".
  iMod ("Hcont" with "Hσ_s") as (? ?) "[Hσ_s Hm]". iModIntro.
  assert (∃ e_s' σ_s', head_step P_s0 (Load Na2Ord #l) σ_s0 e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with lia head_step. }
  iExists e_s', σ_s'. iSplit; first by eauto. inv_head_step.
  iModIntro. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_const. }
  by iApply "Ht".
Qed.

Lemma target_red_store_sc l v v' Ψ `{!sheapInvConst} :
  l ↦t v' -∗
  (l ↦t v -∗ target_red (of_val #()) Ψ) -∗
  target_red (Store ScOrd (Val $ LitV (LitLoc l)) (Val v)) Ψ.
Proof.
  iIntros "Hl Hsim". iApply target_red_lift_head_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) !>".
  iDestruct (heap_read_1 with "Hσ_t Hl") as %?.
  iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%"; inv_head_step.
  iMod (heap_write with "Hσ_t Hl") as "[$ ?]".
  iFrame. iModIntro. iSplitR; first done.
  iSplitL "Hinv". { by iApply sheap_inv_const. }
    by iApply "Hsim".
Qed.

Lemma target_red_store_na l v v' Ψ `{!sheapInvConst} :
  l ↦t v' -∗
  (l ↦t v -∗ target_red (of_val #()) Ψ) -∗
  target_red (Store Na1Ord (Val $ LitV (LitLoc l)) (Val v)) Ψ.
Proof.
  iIntros "Hl Hsim". iApply target_red_lift_head_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iMod (heap_write_na with "Hσ_t Hl") as (?) "[Hσ_t Hcont]". iModIntro.
  iSplit; first by eauto with head_step.
  iIntros (??? Hstep) "!>"; inv_head_step.
  iFrame. iSplitR; [done|].
  iSplitL "Hinv". { by iApply sheap_inv_const. }

  iApply target_red_lift_head_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iMod ("Hcont" with "Hσ_t") as (?) "[Hσ_t Hm]". iModIntro.
  iSplit; first by eauto with head_step.
  iIntros (??? Hstep) "!>"; inv_head_step.
  iFrame. iSplitR; [done|].
  iSplitL "Hinv". { by iApply sheap_inv_const. }
  by iApply "Hsim".
Qed.

Lemma source_red_store_sc l v v' Ψ `{!sheapInvConst} :
  l ↦s v' -∗
  (l ↦s v -∗ source_red (of_val #()) π Ψ) -∗
  source_red (Store ScOrd (Val $ LitV (LitLoc l)) (Val v)) π Ψ.
Proof.
  iIntros "Hl Hsim". iApply source_red_lift_head_step.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _] !>".
  iDestruct (heap_read_1 with "Hσ_s Hl") as %?.
  assert (∃ e_s' σ_s', head_step P_s (Store ScOrd (Val $ LitV (LitLoc l)) (Val v)) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done. inv_head_step.
  iMod (heap_write with "Hσ_s Hl") as "[$ ?]".
  iFrame. iModIntro.
  iSplitL "Hinv". { by iApply sheap_inv_const. }
  by iApply "Hsim".
Qed.

Lemma source_red_store_na l v v' Ψ `{!sheapInvConst} :
  l ↦s v' -∗
  (l ↦s v -∗ source_red (of_val #()) π Ψ) -∗
  source_red (Store Na1Ord (Val $ LitV (LitLoc l)) (Val v)) π Ψ.
Proof.
  iIntros "Hl Hsim". iApply source_red_lift_head_step.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _]".
  iMod (heap_write_na with "Hσ_s Hl") as (?) "[Hσ_s Hcont]". iModIntro.
  assert (∃ e_s' σ_s', head_step P_s (Store Na1Ord (Val $ LitV (LitLoc l)) (Val v)) σ_s e_s' σ_s' [])
    as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done. inv_head_step.
  iModIntro. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_const. }

  iApply source_red_lift_head_step.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) _]".
  iMod ("Hcont" with "Hσ_s") as (?) "[Hσ_s Hm]". iModIntro.
  assert (∃ e_s' σ_s', head_step P_s0 (Store Na2Ord (Val $ LitV (LitLoc l)) (Val v)) σ_s0 e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. iSplitR; first done. inv_head_step.
  iModIntro. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_const. }
  by iApply "Hsim".
Qed.

(** operational lemmas for calls *)
Lemma target_red_call f K_t v Ψ :
  f @t K_t -∗
  target_red (fill K_t (Val v)) Ψ -∗
  target_red (Call (Val $ LitV $ LitFn f) (Val v)) Ψ.
Proof.
  iIntros "Hf Hred". iApply target_red_lift_head_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & ?) !>".
  iDestruct (gen_prog_valid with "HP_t Hf") as %?.
  iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%"; inv_head_step.
  iModIntro. by iFrame.
Qed.

Lemma source_red_call f K_s v Ψ :
  f @s K_s -∗
  source_red (fill K_s (Val v)) π Ψ -∗
  source_red (Call (Val $ LitV $ LitFn f) (Val v)) π Ψ.
Proof.
  iIntros "Hf Hred". iApply source_red_lift_head_step.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & ?) [% %]] !>".
  iDestruct (gen_prog_valid with "HP_s Hf") as %?.
  iExists _, _. iSplit. { simpl. eauto with head_step. }
  iModIntro. iFrame.
  iApply sheap_inv_pure_prim_step; [done| |done] => ?.
  apply: fill_prim_step. apply: head_prim_step. by constructor.
Qed.

(** Call lemmas for sim *)
Lemma sim_call e_t e_s v_t v_s f :
  to_val e_t = Some v_t →
  to_val e_s = Some v_s →
  ⊢ Ω π v_t v_s -∗ Call (## f) e_t ⪯{π, Ω} Call (## f) e_s {{ Ω π }}.
Proof.
  intros <-%of_to_val <-%of_to_val.
  (* FIXME use lifting lemma for this *)
  iIntros "H". rewrite /sim /sim_stutter /sim_def sim_expr_unfold. iIntros (??????) "[(?&?&?&?&Hinv) [% %]]". iModIntro.
  iRight; iRight. iExists f, empty_ectx, v_t, empty_ectx, v_s, σ_s.
  rewrite list_insert_id /= //. iFrame.
  iSplitR; first done. iSplitR. { iPureIntro. constructor. }
  iIntros (v_t' v_s' ) "H". iApply sim_value. iApply "H".
Qed.

(** fork *)
Lemma sim_fork e_t e_s Ψ `{!sheapInvConst} :
  #() ⪯ #() [{ Ψ }] -∗
  (∀ π', e_t ⪯{π', Ω} e_s [{ lift_post (Ω π') }]) -∗
  Fork e_t ⪯ Fork e_s [{ Ψ }].
Proof.
  iIntros "Hval Hsim". iApply sim_lift_head_step_both.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) %Hnstuck] !>".
  iSplitR. { eauto with head_step. }
  iIntros (e_t' efs_t σ_t') "%"; inv_head_step.
  iModIntro. iExists _, _, _. iSplitR. { eauto with head_step. }
  simpl. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_const. }
  iSplitL; [|done]. iApply "Hsim".
Qed.

(** Coinduction support *)

Lemma sim_while_while b_t b_s c_t c_s inv Ψ :
  inv -∗
  □ (inv -∗
    (if: c_t then b_t ;; while: c_t do b_t od else #())%E ⪯{π, Ω}
    (if: c_s then b_s ;; while: c_s do b_s od else #())%E
      [{ λ e_t e_s, Ψ e_t e_s ∨ (⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗ inv) }]) -∗
  (while: c_t do b_t od ⪯{π, Ω} while: c_s do b_s od [{ Ψ }])%E.
Proof.
  iIntros "Hinv_init #Hstep".
  iApply (sim_lift_head_coind _ _ (λ e_t e_s, ⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗ inv)%I with "[] [Hinv_init]"); first last.
  { iFrame. eauto. }
  iModIntro. iIntros (?? ?? ?? ??) "(-> & -> & Hinv) ((?&?&?&?&Hsi) & [% %])".
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%Hhead"; inv_head_step.
  assert (∃ e_s' σ_s', head_step P_s (while: c_s do b_s od ) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iModIntro. iExists e_s', σ_s'. inv_head_step. iFrame. iSplit;[done|].
  iSplitR; first by eauto with head_step.
  iSplitL "Hsi". {
    iApply sheap_inv_pure_prim_step; [done| |done] => ?.
    apply: fill_prim_step. apply: head_prim_step. by constructor.
  }
  iApply "Hstep". iFrame.
Qed.


Lemma sim_while_rec b_t c_t v_s (K_s : ectx) (inv : val → iProp Σ) Ψ rec_n :
  inv v_s -∗
  rec_n @s K_s -∗
  □ (∀ v_s', inv v_s' -∗
    (if: c_t then b_t ;; while: c_t do b_t od else #())%E ⪯{π, Ω} (fill K_s v_s')%E
    [{ λ e_t e_s , Ψ e_t e_s ∨ (∃ v_s', ⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = Call ##rec_n (Val v_s')⌝ ∗ inv v_s') }]) -∗
  (while: c_t do b_t od ⪯{π, Ω} Call ## rec_n v_s [{ Ψ }])%E.
Proof.
  iIntros "Hinv #Hrec #Hstep". iApply (sim_lift_head_coind _ _ (λ e_t e_s, (∃ v_s', ⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = Call ##rec_n (Val v_s')⌝ ∗ inv v_s')%I)); first last.
  { iExists v_s. eauto. }
  iModIntro. iIntros (?? ?? ?? ??) "He ((?&HP_s&?&?&?) & [% %])". iDestruct "He" as (v_s') "(-> & -> & Hinv)".
  iSpecialize ("Hstep" with "Hinv").
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%Hhead"; inv_head_step.
  iModIntro. iExists (fill K_s v_s'), σ_s.

  iDestruct (gen_prog_valid with "HP_s Hrec") as %?.
  iFrame. iSplitR; [done|].
  iSplitR; [by eauto with head_step|].
  iApply sheap_inv_pure_prim_step; [done| |done] => ?.
  apply: fill_prim_step. apply: head_prim_step. by constructor.
Qed.

Lemma sim_rec_while b_s c_s v_t (K_t : ectx) (inv : val → iProp Σ) Ψ rec_n :
  inv v_t -∗
  rec_n @t K_t -∗
  □ (∀ v_t', inv v_t' -∗
    (fill K_t v_t')%E ⪯{π, Ω}  (if: c_s then b_s ;; while: c_s do b_s od else #())%E
    [{ λ e_t e_s , Ψ e_t e_s ∨ (∃ v_t', ⌜e_t = Call ##rec_n (Val v_t')⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗  inv v_t') }]) -∗
  ( Call ##rec_n v_t ⪯{π, Ω} while: c_s do b_s od [{ Ψ }])%E.
Proof.
  iIntros "Hinv #Hrec #Hstep". iApply (sim_lift_head_coind _ _ (λ e_t e_s, (∃ v_t', ⌜e_t = Call ##rec_n (Val v_t')⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗  inv v_t'))%I); first last.
  { iExists v_t. eauto. }
  iModIntro. iIntros (?? ?? ?? ??) "He ((HP_t & ? & ? & ? &?) & [% %])". iDestruct "He" as (v_s') "(-> & -> & Hinv)".
  iSpecialize ("Hstep" with "Hinv").

  iDestruct (gen_prog_valid with "HP_t Hrec") as %?.
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%Hhead"; inv_head_step.
  iModIntro.
  assert (∃ e_s' σ_s', head_step P_s (while: c_s do b_s od ) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. inv_head_step. iFrame. iSplitR; [done|].
  iSplitR; [by eauto with head_step|].
  iApply sheap_inv_pure_prim_step; [done| |done] => ?.
  apply: fill_prim_step. apply: head_prim_step. by constructor.
Qed.

Lemma sim_rec_rec v_t v_s (K_t K_s : ectx) (inv : val → val → iProp Σ) Ψ rec_t rec_s :
  inv v_t v_s -∗
  rec_t @t K_t -∗
  rec_s @s K_s -∗
  □ (∀ v_t' v_s', inv v_t' v_s' -∗
    (fill K_t v_t')%E ⪯{π, Ω} (fill K_s v_s')%E
    [{ λ e_t e_s , Ψ e_t e_s ∨ (∃ v_t' v_s', ⌜e_t = Call ##rec_t (Val v_t')⌝ ∗ ⌜e_s = Call ##rec_s (Val v_s')⌝ ∗ inv v_t' v_s') }]) -∗
  ( Call ##rec_t v_t ⪯{π, Ω} Call ##rec_s v_s [{ Ψ }])%E.
Proof.
  iIntros "Hinv #Hrec_t #Hrec_s #Hstep".
  iApply (sim_lift_head_coind _ _ (λ e_t e_s, (∃ v_t' v_s', ⌜e_t = Call ##rec_t (Val v_t')⌝ ∗ ⌜e_s = Call ##rec_s (Val v_s')⌝ ∗ inv v_t' v_s'))%I); first last.
  { iExists v_t, v_s. eauto. }
  iModIntro. iIntros (?? ?? ?? ??) "He ((HP_t & HP_s & ? & ? &?) & [% %])".
  iDestruct "He" as (v_t' v_s') "(-> & -> & Hinv)".
  iSpecialize ("Hstep" with "Hinv").

  iDestruct (gen_prog_valid with "HP_t Hrec_t") as %?.
  iDestruct (gen_prog_valid with "HP_s Hrec_s") as %?.
  iModIntro. iSplitR; first by eauto with head_step.
  iIntros (e_t' efs σ_t') "%Hhead"; inv_head_step.
  iModIntro.
  assert (∃ e_s' σ_s', head_step P_s (Call ##rec_s v_s') σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with head_step. }
  iExists e_s', σ_s'. inv_head_step. iFrame.
  iSplitR; [done|].
  iSplitR; [by eauto with head_step|].
  iApply sheap_inv_pure_prim_step; [done| |done] => ?.
  apply: fill_prim_step. apply: head_prim_step. by constructor.
Qed.
End lifting.
