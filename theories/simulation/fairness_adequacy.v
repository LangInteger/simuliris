From stdpp Require Import gmap.
From iris.bi Require Import bi.
From iris.algebra Require Import gset gmap list.
From iris.proofmode Require Import tactics.
From simuliris.logic Require Import fixpoints.
From simuliris.simulation Require Import relations language fairness.
From simuliris.simulation Require Export slsls.
From iris.prelude Require Import options.
Import bi.

Section fix_lang.
Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
Context {Λ : language}.
Context {s : SimulLang PROP Λ} {Ω: val Λ → val Λ → PROP}.

Set Default Proof Using "Type*".

Implicit Types
  (e_s e_t e: expr Λ)
  (p_s p_t p: prog Λ)
  (P: list (expr Λ * expr Λ))
  (O: gset nat)
  (I J: list nat)
  (D: gmap nat nat)
  (i j k: nat)
  (σ_s σ_t σ : state Λ).

(* Language Setup *)
Notation "P '.(tgt)'" := (P.*1) (at level 5).
Notation "P '.(src)'" := (P.*2) (at level 5).


Definition all_values O P :=
  (∀ i , i ∈ O → ∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ is_Some (to_val e_t) ∧ is_Some (to_val e_s)).

Definition must_step_inner (post: list (expr Λ * expr Λ) → PROP) (must_step: list (expr Λ * expr Λ) → gset nat → gmap nat nat → PROP) (P: list (expr Λ * expr Λ)) (O: gset nat) (D: gmap nat nat) : PROP :=
  (∀ p_t σ_t p_s σ_s, state_interp p_t σ_t p_s σ_s ∗ ⌜pool_safe p_s P.(src) σ_s⌝ ∗ ⌜delays_for P.(tgt) D⌝ ==∗
    (* the base case where every term in O must be a value *)
    (⌜all_values O P⌝ ∗ state_interp p_t σ_t p_s σ_s ∗ post P) ∨
    (* the target can be stuttered for any finite number of steps *)
    (∃ P' σ_s' I, ⌜pool_steps p_s P.(src) σ_s I P'.(src) σ_s'⌝ ∗ ⌜P'.(tgt) = P.(tgt)⌝ ∗ state_interp p_t σ_t p_s σ_s' ∗ must_step P' (O ∖ list_to_set I) D) ∨
    (* the target can step, and every fair step can be replayed (or stuttered) in the source *)
    (
      (* we do not need reducibility of the target for fairness ⌜reducible_pool p_t P.(tgt) σ_t⌝ ∗ *)
      ∀ T_t' D' i σ_t', ⌜fair_pool_step p_t P.(tgt) D σ_t i T_t' D' σ_t'⌝ ==∗
      ∃ P' σ_s' I,
        ⌜P'.(tgt) = T_t'⌝ ∗
        ⌜pool_steps p_s P.(src) σ_s I P'.(src) σ_s'⌝ ∗
        state_interp p_t σ_t' p_s σ_s' ∗
        must_step P' (O ∖ list_to_set I) D'
    ))%I.

Definition must_step (post: list (expr Λ * expr Λ) → PROP) :=
  uncurry3 (bi_least_fixpoint (λ (must_step: prodO (prodO (listO (prodO exprO exprO)) (gsetO natO)) (gmapO natO natO) → PROP), curry3 (must_step_inner post (uncurry3 must_step)))).

Definition sim_pool_inner (sim_pool: list (expr Λ * expr Λ) → PROP) (P: list (expr Λ * expr Λ)) :=
  (∀ D, must_step sim_pool P (threads P.(tgt)) D)%I.

Definition sim_pool :=
  bi_greatest_fixpoint (sim_pool_inner: (listO (prodO exprO exprO) → PROP) → (listO (prodO exprO exprO) → PROP)).


Lemma must_step_inner_mono (sim_pool sim_pool': list (expr Λ * expr Λ) → PROP) (rec rec': list (expr Λ * expr Λ) → gset nat → gmap nat nat → PROP) P O D:
  (∀ P, sim_pool P -∗ sim_pool' P) -∗
  (∀ P O D, rec P O D -∗ (∀ P, sim_pool P -∗ sim_pool' P) -∗ rec' P O D) -∗
  must_step_inner sim_pool rec P O D -∗
  must_step_inner sim_pool' rec' P O D.
Proof.
  iIntros "Hpool Hrec"; rewrite /must_step_inner.
  iIntros "Hinner". iIntros (p_t σ_t p_s σ_s) "H".
  iMod ("Hinner" with "H") as "[Val|[Stutter|Step]]".
  - iModIntro. iLeft. iDestruct "Val" as "($ & $ & Hsim)". by iApply "Hpool".
  - iRight. iLeft. iDestruct "Stutter" as (P' σ I Hsteps Heq) "(HP' & Hr)".
    iModIntro. iExists P', σ, I. do 2 (iSplit; first done).
    iFrame. by iApply ("Hrec" with "Hr").
  - iRight. iRight. iModIntro. iIntros (T_t' D' i σ_t' Hstep).
    iMod ("Step" with "[//]") as (P' σ_s' I) "(Heq & Hstep & SI & Hr)".
    iModIntro. iExists P', σ_s', I. iFrame. by iApply ("Hrec" with "Hr").
Qed.

(* free NonExpansive instances *)
Local Instance free_discrete_prod_ne (Φ: prodO (prodO (listO (prodO (@exprO Λ) (@exprO Λ))) (gsetO natO)) (gmapO natO natO) → PROP):
  NonExpansive Φ.
Proof.
  by intros n [[? ?] ?] [[? ?] ?] ->%discrete_iff%leibniz_equiv; last apply _.
Qed.

Local Instance free_discrete_expr_ne (Φ: listO (prodO (@exprO Λ) (@exprO Λ)) → PROP):
  NonExpansive Φ.
Proof.
  by intros n ? ? ->%discrete_iff%leibniz_equiv; last apply _.
Qed.


Local Instance must_step_body_mono post: BiMonoPred ((λ (must_step: prodO (prodO (listO (prodO exprO exprO)) (gsetO natO)) (gmapO natO natO) → PROP), curry3 (must_step_inner post (uncurry3 must_step)))).
Proof.
  split.
  - intros M1 M2 Hne1 Hne2. iIntros "#H" ([[P O] D]). simpl.
    iApply must_step_inner_mono; first by iIntros (?) "$".
    iIntros (???) "H' _"; rewrite /uncurry3. by iApply "H".
  - intros Φ Hne. apply _.
Qed.

Lemma must_step_mono (sim_pool sim_pool': list (expr Λ * expr Λ) → PROP) P O D:
  (∀ P, sim_pool P -∗ sim_pool' P) -∗
  must_step sim_pool P O D -∗ must_step sim_pool' P O D.
Proof.
  rewrite /must_step {1 3}/uncurry3.
  iIntros "Hmon Hmust". iRevert "Hmon".
  iApply (least_fixpoint_ind _ (λ x, (∀ P, sim_pool P -∗ sim_pool' P) -∗ bi_least_fixpoint
    (λ must_step0 : prodO (prodO (listO (prodO exprO exprO)) (gsetO natO))
                      (gmapO natO natO) → PROP,
      curry3 (must_step_inner sim_pool' (uncurry3 must_step0)))
    x)%I with "[] Hmust").
  iModIntro. clear P O D. iIntros ([[P O] D]) "Hinner Hmon".
  rewrite least_fixpoint_unfold {1 3}/curry3.
  iApply (must_step_inner_mono with "Hmon [] Hinner").
  clear P O D. iIntros (P O D) "Hpost Hmon"; rewrite /uncurry3.
  by iApply "Hpost".
Qed.

Lemma sim_pool_body_mono: BiMonoPred (sim_pool_inner: (listO (prodO exprO exprO) → PROP) → (listO (prodO exprO exprO) → PROP)).
Proof.
  split.
  - intros M1 M2 Hne1 Hne2. iIntros "#H" (L).
    rewrite /sim_pool_inner. iIntros "Hi" (D).
    iApply (must_step_mono with "H Hi").
  - intros ??. apply _.
Qed.

Lemma must_step_ind F sim_pool P O D:
  □ (∀ P O D, must_step_inner sim_pool F P O D -∗ F P O D) -∗
  must_step sim_pool P O D -∗ F P O D.
Proof.
  iIntros "#IH HM". iApply (least_fixpoint_ind _ (curry3 F: prodO (prodO (listO (prodO exprO exprO)) (gsetO natO)) (gmapO natO natO) → PROP) with "[] HM").
  iModIntro. clear P O D. iIntros ([[P O] D]). simpl.
  iIntros "H". iApply "IH". by rewrite {4}(uncurry3_curry3 (F: listO (prodO (@exprO Λ) (@exprO Λ)) -d> gsetO natO -d> gmapO natO natO -d> PROP)).
Qed.

Lemma must_step_unfold R P O D:
  must_step R P O D ≡ must_step_inner R (must_step R) P O D.
Proof.
  rewrite {1}/must_step {1}/uncurry3.
  rewrite least_fixpoint_unfold {1}/curry3 //.
Qed.


Lemma sim_pool_coind F P:
  □ (∀ P D, F P -∗ must_step F P (threads P.(tgt)) D) -∗
  F P -∗ sim_pool P.
Proof.
  iIntros "#IH HF". rewrite /sim_pool.
  iApply (greatest_fixpoint_coind _ (F: listO (prodO (@exprO Λ) (@exprO Λ)) → PROP) with "[] HF").
  iModIntro. iIntros (L) "HF". rewrite /sim_pool_inner.
  iIntros (D). by iApply "IH".
Qed.

(* proof structure:
  co-induction on the outer fixpoint
    we need to show that sim_expr_all is a post-fixpoint.
    induction on the set of threads
    + base case trivial
    + step case: let i be the new thread and IH the inductive hypothesis.
      induction on the least fixpoint of i
      * value case:
          - target is a value, source steps to a value.
            we can remove i and we are done with IH
      * step case:
          (we can step ∧ (we stuttered or we took a proper step))
          induction on the delay unil thread i is stepped again
          let j be the next thread that steps
          -- if j = i and we stuttered the source, then the claim follows from the lfp
          -- if j = i and we did not stutter, we can remove i and the claim follows
          -- if j ≠ i, then any step will decrease the delay of i.
             The claim follows with the IH for d.
*)


Definition sim_expr_all (P: list (expr Λ * expr Λ)) := ([∗ list] p ∈ P, sim_expr Ω (lift_post Ω) (fst p) (snd p))%I.
Notation must_step_all := (must_step sim_expr_all).


Lemma must_step_all_add_values P O O' D:
  (∀ i, i ∈ O' → i ∈ O ∨ ∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ is_Some (to_val e_t) ∧ is_Some (to_val e_s)) →
  must_step_all P O D -∗
  must_step_all P O' D.
Proof.
  intros Hall. iIntros "Hlocal". iRevert (O' Hall).
  iApply (must_step_ind (λ P O D, ∀ O' : gset nat,
  ⌜∀ i, i ∈ O' → i ∈ O ∨ (∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ is_Some (to_val e_t) ∧ is_Some (to_val e_s))⌝
  → must_step_all P O' D)%I with "[] Hlocal").
  iModIntro. clear P O D. iIntros (P O D) "Hinner".
  iIntros (O' Hel). rewrite must_step_unfold.
  iIntros (p_t σ_t p_s σ_s) "H".
  iMod ("Hinner" with "H") as "[Base|[Stutter|Step]]"; iModIntro.
  - iLeft. iDestruct "Base" as "(%Base & $)". iPureIntro.
    intros i Hi. destruct (Hel _ Hi) as [?|(? & ? & Hlook & ? & ?)]; eauto.
  - iRight. iLeft. iDestruct "Stutter" as (P' σ_s' I) "(%Hsteps & %Htgt & Hstate & IH)".
    iExists P', σ_s', I. iFrame. do 2 (iSplitR "IH"; first done).
    iApply "IH". iPureIntro. intros i [Hi Hni]%elem_of_difference.
    destruct (Hel _ Hi) as [|Hvals]; first set_solver.
    right. destruct Hvals as (e_t & e_s & Hlook & [v_t val_t] & [v_s val_s]).
    exists e_t, e_s. split; last eauto.
    eapply (pool_steps_value_preservation _ _ _ _ i) in Hsteps; last first.
    { rewrite list_lookup_fmap Hlook //= -(of_to_val _ _  val_s) //. }
    assert (P'.(tgt) !! i = Some e_t) as Htgt_look.
    { rewrite Htgt list_lookup_fmap Hlook //. }
    rewrite (of_to_val _ _ val_s) in Hsteps.
    revert Hsteps Htgt_look.
    rewrite !list_lookup_fmap.
    destruct (P' !! i) as [[]|]; simpl; naive_solver.
  - iRight. iRight. iIntros (T_t' D' i σ_t' Hfair).
    iMod ("Step" with "[//]") as (P' σ_s' I Heq Hsteps) "(SI & IH)".
    iExists P', σ_s', I. iFrame. iModIntro. do 2 (iSplit; first done).
    iApply "IH". iPureIntro. intros j Hj. eapply elem_of_difference in Hj as [Hj HI].
    destruct (Hel _ Hj) as [?|Hvals].
    { left; eapply elem_of_difference; eauto. }
    right. destruct Hvals as (e_t & e_s & Hlook & [v_t val_t] & [v_s val_s]).
    exists e_t, e_s; split; last eauto.
    eapply (pool_steps_value_preservation _ _ _ _ j) in Hsteps; last first.
    { rewrite list_lookup_fmap Hlook //= -(of_to_val _ _  val_s) //. }
    rewrite -Heq in Hfair. eapply fair_pool_step_iff in Hfair as (Hstep & ?).
    eapply (pool_step_value_preservation _ _ _ _ j) in Hstep; last first.
    { rewrite list_lookup_fmap Hlook //= -(of_to_val _ _  val_t) //. }
    revert Hsteps Hstep. rewrite !list_lookup_fmap -(of_to_val _ _  val_t) -(of_to_val _ _  val_s).
    destruct (P' !! j) as [[??]|]; simpl; naive_solver.
Qed.

Lemma must_step_all_weaken P O O' D:
  O' ⊆ O →
  must_step_all P O D -∗
  must_step_all P O' D.
Proof.
  iIntros (Hsub) "Hall". iApply must_step_all_add_values; last done.
  naive_solver.
Qed.


Lemma must_step_all_delays_for P O D:
  (⌜delays_for P.(tgt) D⌝ -∗ must_step_all P O D) -∗ must_step_all P O D.
Proof. Admitted.
  (* rewrite lfp_fixpoint.
  rewrite /must_step; intros Hstep Hdel; eapply (Hstep Hdel Hdel).
Qed. *)

(*

Lemma sim_expr_all_insert P i e_t e_s:
  sim_expr_all P →
  sim_expr e_t e_s →
  sim_expr_all (<[i:=(e_t, e_s)]> P).
Proof.
  intros Hall Hsim e_t' e_s' Hin.
  eapply elem_of_list_lookup_1 in Hin as [j Hlook].
  eapply list_lookup_insert_Some in Hlook as [(-> & Heq & _)|(Hne & Hlook)].
  - naive_solver.
  - by eapply Hall, elem_of_list_lookup_2.
Qed.

Lemma sim_expr_all_app P P' :
  sim_expr_all P →
  sim_expr_all P' →
  sim_expr_all (P ++ P').
Proof.
  intros HP HP' e_t e_s [|]%elem_of_app; eauto.
Qed.


Lemma must_step_all_intro_source P P' I O D:
  pool_steps P.(src) I P'.(src) →
  P'.(tgt) = P.(tgt) →
  must_step_all P' (O ∖ list_to_set I) D →
  must_step_all P O D.
Proof.
  intros Hsteps Heq Hlocal.
  rewrite lfp_fixpoint {1}/must_step.
  intros Hdel. right. left.
  exists P', I. repeat split; done.
Qed.

Lemma must_step_all_intro_target_and_source P O D:
  (∃ T_t' i, pool_step P.(tgt) i T_t') →
  (∀ T_t' D' i,
    delays_for P.(tgt) D →
    fair_pool_step P.(tgt) D i T_t' D' →
   ∃ P' I, P'.(tgt) = T_t' ∧
   pool_steps P.(src) I P'.(src) ∧
   must_step_all P' (O ∖ list_to_set I) D') →
  must_step_all P O D.
Proof.
  intros CanStep Post.
  rewrite lfp_fixpoint {1}/must_step.
  intros Hdel. right. right. split; eauto.
Qed.


Lemma must_step_all_stutter_target P P' I O D:
  pool_steps P.(src) I P'.(src) →
  P'.(tgt) = P.(tgt) →
  must_step_all P' O D →
  must_step_all P O D.
Proof.
  intros Hsteps Heq Hlocal. eapply must_step_all_intro_source; eauto.
  eapply must_step_all_weaken; first done. set_solver.
Qed.


Lemma must_step_all_stutter_target_no_fork P j e_t e_s e_s' O D:
  P !! j = Some (e_t, e_s) →
  no_fork e_s e_s' →
  must_step_all (<[j := (e_t, e_s')]> P) (O ∖ {[j]}) D →
  must_step_all P O D.
Proof.
  intros Hlook Hstep Hlocal.
  eapply must_step_all_intro_source with (I := [j]) (P' := (<[j := (e_t, e_s')]> P)).
  - rewrite list_fmap_insert //=. eapply pool_steps_single, pool_step_iff.
    exists e_s, e_s', []. split; first done. split; first rewrite list_lookup_fmap Hlook //.
    by rewrite right_id.
  - rewrite list_fmap_insert //= list_insert_id // list_lookup_fmap Hlook //.
  - eapply must_step_all_weaken; eauto. set_solver.
Qed.


Lemma must_step_all_stutter_target_no_forks P j e_t e_s e_s' O D:
  P !! j = Some (e_t, e_s) →
  no_forks e_s e_s' →
  must_step_all (<[j := (e_t, e_s')]> P) O D →
  must_step_all P O D.
Proof.
  intros Hlook Hsteps. revert P Hlook. induction Hsteps as [e_s|e_s e_s' e_s'' Hstep Hsteps IH]; intros P Hlook.
  - rewrite list_insert_id //.
  - intros Hlocal. eapply must_step_all_stutter_target_no_fork; eauto.
    eapply must_step_all_weaken with (O := O); last set_solver.
    eapply IH.
    + eapply list_lookup_insert, lookup_lt_Some, Hlook.
    + by rewrite list_insert_insert.
Qed.



Lemma must_step_all_stutter_source' i e_t e_t' e_s P O D' T_t':
  T_t' = <[i := e_t']> P.(tgt) →
  P !! i = Some (e_t, e_s) →
  must_step_all (<[i := (e_t', e_s)]> P) O D' →
  ∃ P' I, P'.(tgt) = T_t' ∧ pool_steps P.(src) I P'.(src) ∧ must_step_all P' (O ∖ list_to_set I) D'.
Proof.
  intros Hupd Hlook Hall; exists (<[i := (e_t', e_s)]> P), [].
  rewrite !list_fmap_insert; split; first done.
  rewrite list_insert_id; last rewrite list_lookup_fmap Hlook //.
  split; first constructor. eapply local_all_weaken; eauto. set_solver.
Qed.


Lemma no_forks_pool_step e e' T j:
  no_fork e e' →
  T !! j = Some e →
  pool_step T j (<[j := e']> T).
Proof.
  intros H1 H2; eapply pool_step_iff.
  exists e, e', []; split; repeat split; eauto.
  by rewrite right_id.
Qed.


Lemma no_forks_pool_steps e e' T j:
  no_forks e e' →
  T !! j = Some e →
  ∃ I, pool_steps T I (<[j := e']> T).
Proof.
  induction 1 as [e|e e' e'' Hstep Hsteps IH] in T.
  - intros Hlook. exists []. rewrite list_insert_id //. constructor.
  - intros Hlook. eapply no_forks_pool_step in Hstep; last done.
    destruct (IH (<[j := e']> T)) as (I & Hsteps').
    { eapply list_lookup_insert, lookup_lt_Some, Hlook. }
    exists (j :: I).  econstructor; eauto.
    revert Hsteps'; by rewrite list_insert_insert.
Qed.

Lemma local_all_not_stuttered i e_t e_t' e_s e_s' e_s'' P O D' T_t' T_f_s T_f_t:
  T_t' = <[i := e_t']> P.(tgt) ++ T_f_t →
  P !! i = Some (e_t, e_s) →
  no_forks e_s e_s' →
  step e_s' e_s'' T_f_s →
  length T_f_t = length T_f_s →
  local_all (<[i := (e_t', e_s'')]> P ++ zip T_f_t T_f_s) (O ∖ {[i]}) D' →
  ∃ P' I, P'.(tgt) = T_t' ∧ pool_steps P.(src) I P'.(src) ∧ local_all P' (O ∖ list_to_set I) D'.
Proof.
  intros Hupd Hlook Hfrk Hstep Hlen Hall.
  eapply (no_forks_pool_steps _ _ P.(src) i) in Hfrk as (I & Hsteps); last first.
  { rewrite list_lookup_fmap Hlook //=. }
  exists (<[i := (e_t', e_s'')]> P ++ zip T_f_t T_f_s), (I ++ [i]).
  rewrite !fmap_app fst_zip ?Hlen // snd_zip ?Hlen // !list_fmap_insert Hupd.
  split; first done.
  split; last (eapply local_all_weaken; [done|set_solver]).
  eapply pool_steps_trans; first done.
  eapply pool_steps_single, pool_step_iff.
  exists e_s', e_s'', T_f_s.
  rewrite list_insert_insert list_lookup_insert //.
  eapply lookup_lt_Some; rewrite list_lookup_fmap Hlook //.
Qed. *)

Definition sim_expr_all_wo P O :=
  ([∗ list] k ↦ p ∈ P, if (decide (k ∈ O)) then emp else sim_expr Ω (lift_post Ω) (fst p) (snd p))%I.

Lemma sim_expr_all_to_wo P :
  sim_expr_all P ≡ sim_expr_all_wo P ∅.
Proof. Admitted.

Lemma sim_expr_all_wo_split P O i e_t e_s:
  P !! i = Some (e_t, e_s) →
  i ∉ O →
  sim_expr_all_wo P O ≡ (sim_expr Ω (lift_post Ω) e_t e_s ∗ sim_expr_all_wo P (O ∪ {[i]}))%I.
Proof. Admitted.

Lemma sim_expr_all_wo_insert i O P e_t e_s:
  i ∈ O →
  sim_expr_all_wo P O ≡ sim_expr_all_wo (<[i := (e_t, e_s)]> P) O.
Admitted.

Lemma sim_expr_all_app P1 P2:
  sim_expr_all (P1 ++ P2) ≡ (sim_expr_all P1 ∗ sim_expr_all P2)%I.
Admitted.

Lemma sim_expr_all_wo_app O P1 P2:
  (∀ i, i ∈ O → i < length P1) →
  (sim_expr_all_wo P1 O ∗ sim_expr_all P2)%I ≡ sim_expr_all_wo (P1 ++ P2)%I O.
Admitted.




Lemma no_forks_pool_steps' p e σ e' σ' T i:
  no_forks p e σ e' σ' →
  T !! i = Some e →
  ∃ I, pool_steps p T σ I (<[i := e']> T) σ' ∧ ((list_to_set I: gset nat) ⊆ {[i]}).
Admitted.


Lemma sim_expr_target_step_unfold T i p_t p_s σ_t σ_s e_t e_s e_t' σ_t' efs_t:
  T !! i = Some e_s →
  prim_step p_t e_t σ_t e_t' σ_t' efs_t →
  safe p_s e_s σ_s →
  state_interp p_t σ_t p_s σ_s -∗
  sim_expr Ω (lift_post Ω) e_t e_s ==∗
  ∃ e_s' σ_s' efs_s I, sim_expr Ω (lift_post Ω) e_t' e_s' ∗ state_interp p_t σ_t' p_s σ_s' ∗
      ⌜pool_steps p_s T σ_s I (<[i := e_s']> T ++ efs_s) σ_s'⌝ ∗ ⌜length efs_t = length efs_s⌝ ∗ sim_expr_all (zip efs_t efs_s).
Proof.
  intros Hlook Hprim Hsafe. iIntros "SI Hsim". rewrite sim_expr_unfold.
  iMod ("Hsim" with "[$SI //]") as "[Val|[Step|_]]"; last admit.
  - iModIntro. iDestruct "Val" as (e_s' σ_s' Hnfs) "[SI Hpost]".
    iDestruct "Hpost" as (v_t v_s Heq1 Heq2) "?".
    rewrite Heq1 in Hprim. exfalso. by eapply val_prim_step.
  - iDestruct "Step" as "[_ Step]".
    iMod ("Step" with "[//]") as "[Stutter|NoStutter]".
    + iModIntro. iDestruct "Stutter" as "(-> & SI & Hsim)".
      iExists e_s, σ_s. iFrame. iExists [], []. rewrite /sim_expr_all; simpl.
      iPureIntro. repeat split. rewrite right_id list_insert_id //. constructor.
    + iDestruct "NoStutter" as (e_s' e_s'' σ_s' σ_s'' efs_s Hnfs Hprim' Hlen) "(SI & Hsim & Hall)".
      iModIntro. iExists e_s'', σ_s''. iFrame. iExists efs_s.
      eapply no_forks_pool_steps' in Hnfs as (I & ? & Hsub); last done.
      iExists (I ++ [i]). repeat iSplit; [| done |].
      { iPureIntro. admit. }
      rewrite /sim_expr_all big_sepL2_alt bi.and_elim_r. iFrame.
Admitted.


Lemma sim_expr_must_step_all_core_ind P O D i:
  i ∈ O →
  O ⊆ threads P.(tgt) →
  □ (∀ j D P', ⌜j ∈ O⌝ -∗ ⌜O ∖ {[j]} ⊆ threads P'.(tgt)⌝ -∗ sim_expr_all P' -∗ must_step_all P' (O ∖ {[j]}) D) -∗
  sim_expr_all P -∗
  must_step_all P O D.
Proof.
  iIntros (Hel Hsub) "#IHO Hall". specialize (Hsub _ Hel) as Hthread.
  eapply threads_spec in Hthread as (e & Hlook).
  eapply list_lookup_fmap_inv in Hlook as ([e_t e_s] & -> & Hlook).
  rewrite sim_expr_all_to_wo (sim_expr_all_wo_split _ _ i) //.
  replace (∅ ∪ {[i]}: gset nat) with ({[i]}: gset nat) by set_solver.
  iDestruct "Hall" as "[Hsim Hall]".
  rewrite sim_expr_eq greatest_def_unfold.
  iApply (least_def_strong_ind _ (λ Ψ e_t e_s, ∀ P D, ⌜P !! i = Some (e_t, e_s)⌝ -∗ ⌜O ⊆ threads P.(tgt)⌝ -∗ sim_expr_all_wo P {[i]} -∗ (∀ e_t e_s, Ψ e_t e_s -∗ lift_post Ω e_t e_s) -∗ must_step_all P O D)%I with "[] Hsim [] [] Hall"); eauto.
  { intros n ?? Heq ??. repeat f_equiv. by apply Heq. }
  clear P D Hsub e_t e_s Hlook. iModIntro. iIntros (Ψ e_t e_s) "Hsim".
  iIntros (P D Hlook Hsub) "Hall Hpost".
  destruct (to_val e_t) as [v_t|] eqn: Hval.
  - (* thread i is a value *)
    admit.
  - (* thread i must be in D *)
    assert (i ∈ active_threads P.(tgt)) as Hact.
    { eapply active_threads_spec. exists e_t. split; last done.
      rewrite list_lookup_fmap Hlook //. }
    iApply must_step_all_delays_for. iIntros (Hdel).
    eapply Hdel in Hact as [d HD]. clear Hdel.
    iRevert (P D HD Hlook Hsub) "Hall".
    iInduction (lt_wf d) as [d _] "IHd".
    iIntros(P D HD Hlook Hsub) "Hall".
    rewrite must_step_unfold /must_step_inner.
    iIntros (p_t σ_t p_s σ_s) "(SI & %Hsafe & %Hdel)".
    iModIntro. iRight. iRight.
    iIntros (T_t' D' j σ_t' Hstep).
    destruct (decide (j = i)) as [->|Hne].
    + iClear "IHd". iMod ("Hsim" with "[$SI]") as "[Val|Step]".
      * admit.
      * iDestruct "Val" as (e_s' σ_s' Hnfs) "[SI HΨ]".
        iDestruct ("Hpost" with "HΨ") as (v_t v_s Heq1 Heq2) "?".
        rewrite Heq1 to_of_val in Hval. naive_solver.
      * iDestruct "Step" as "[Step|_]"; last admit.
        iDestruct "Step" as "[_ Hstep]".
        eapply fair_pool_step_inv in Hstep as (e_t_alt & e_t' & efs_t & Hstep & Hlook' & Hupd & Hdecr).
        rewrite list_lookup_fmap Hlook //= in Hlook'. injection Hlook' as <-.
        iMod ("Hstep" with "[//]") as "[Stutter|NoStutter]".
        -- iDestruct "Stutter" as "(-> & SI & Hupd)".
           iModIntro. iExists (<[i := (e_t', e_s)]> P), σ_s, []. iFrame.
           iSplit. { iPureIntro. rewrite Hupd right_id list_fmap_insert //. }
           iSplit. { iPureIntro. rewrite list_fmap_insert list_insert_id ?list_lookup_fmap ?Hlook //. constructor. }
           simpl. rewrite bi.and_elim_l. replace (O ∖ ∅) with O by set_solver.
           iApply ("Hupd" with "[] [] [Hall] Hpost").
           ++ iPureIntro. eapply list_lookup_insert, lookup_lt_Some, Hlook.
           ++ iPureIntro. rewrite list_fmap_insert. by etrans; last eapply threads_insert.
           ++ rewrite -sim_expr_all_wo_insert //. set_solver.
        -- iDestruct "NoStutter" as (e_s' e_s'' σ_s' σ_s'' efs_s Hnfs Hprim Hlen) "(SI & Hsim & Hfrks)".
           iModIntro. eapply (no_forks_pool_steps' _ _ _ _ _ P.(src) i) in Hnfs as (I & Hsteps & Hsub'); last first.
           { rewrite list_lookup_fmap Hlook //. }
           iExists (<[i := (e_t', e_s'')]> P ++ zip efs_t efs_s), σ_s'', (I ++ [i]).
           iSplit. { iPureIntro. rewrite fmap_app Hupd list_fmap_insert fst_zip // Hlen //. }
           iSplit.
           { iPureIntro. eapply pool_steps_trans; first eapply Hsteps. eapply pool_steps_single.
             rewrite fmap_app list_fmap_insert //= snd_zip ?Hlen //. eapply pool_step_iff.
             exists e_s', e_s'', efs_s. split; first done.
             split; last by rewrite list_insert_insert.
             by eapply list_lookup_insert, lookup_lt_Some; rewrite list_lookup_fmap Hlook. }
           iFrame. assert (list_to_set (I ++ [i]) = ({[i]}: gset nat)) as -> by set_solver.
           iApply "IHO"; first done.
           { iPureIntro. rewrite fmap_app list_fmap_insert. etrans; last eapply threads_prim_step. set_solver. }
           rewrite sim_expr_all_app. iSplitR "Hfrks".
           ++ rewrite sim_expr_all_to_wo (sim_expr_all_wo_split _ ∅ i);
              last set_solver;
              last by eapply list_lookup_insert, lookup_lt_Some, Hlook.
              rewrite -sim_expr_all_wo_insert; last set_solver.
              replace (∅ ∪ {[i]}: gset nat) with ({[i]}: gset nat) by set_solver.
              iFrame. iApply (sim_expr_mono with "Hpost [Hsim]").
              by rewrite sim_expr_eq.
           ++ rewrite /sim_expr_all.
              by rewrite big_sepL2_alt sim_expr_eq bi.and_elim_r.
      + eapply fair_pool_step_inv in Hstep as (e_j & e_j_t' & efs_t & Hstep & Hlook' & Hupd & Hdecr).
        eapply list_lookup_fmap_inv in Hlook' as ([e_j_t e_j_s] & -> & Hlookj); simpl in Hstep.
        eapply Hdecr in HD as (d' & -> & HD'); last done.
        assert (d' < S d') as Hlt by lia.
        iSpecialize ("IHd" $! d' Hlt with "Hsim Hpost").
        rewrite (sim_expr_all_wo_split _ _ j) //; last set_solver.
        iDestruct "Hall" as "[Hsim Hall]".
        iMod (sim_expr_target_step_unfold P.(src) j with "SI Hsim") as (e_j_s' σ_s' efs_s I) "(Hsim & SI & %Hsteps & %Hlen & Hfrks)".
        * rewrite list_lookup_fmap Hlookj //.
        * done.
        * admit.
        * iModIntro. iExists (<[j := (e_j_t', e_j_s')]> P ++ zip efs_t efs_s), σ_s', I.
          iFrame. rewrite Hupd !fmap_app !list_fmap_insert //= fst_zip ?Hlen // snd_zip ?Hlen //.
          do 2 (iSplit; first done). iApply (must_step_all_weaken _ O); first set_solver.
          iApply "IHd".
          -- done.
          -- iPureIntro. eapply lookup_app_l_Some. rewrite list_lookup_insert_ne //.
          -- iPureIntro. rewrite fmap_app list_fmap_insert fst_zip ?Hlen //=.
             etrans; last by eapply threads_prim_step. done.
          -- rewrite (sim_expr_all_wo_split _ {[i]} j); last set_solver; last first.
             { eapply lookup_app_l_Some, list_lookup_insert, lookup_lt_Some, Hlookj. }
             iFrame. rewrite -sim_expr_all_wo_app; last admit.
             iFrame. rewrite sim_expr_all_wo_insert //. set_solver.
Admitted.

Lemma sim_expr_must_step_all P O D:
  O ⊆ threads P.(tgt) → sim_expr_all P -∗ must_step_all P O D.
Proof.
  intros Hsub. iRevert (D P Hsub).
  iInduction (set_wf O) as [O _] "IHO".
  iIntros (D P Hsub) "Hall".
  destruct (decide (O ≡ ∅)) as [Empty|[i Hel]%set_choose].
  - rewrite must_step_unfold /must_step_inner.
    iIntros (p_t σ_t p_s σ_s) "(SI & %Hsafe & %Hdel)".
    iModIntro. iLeft. iFrame. iPureIntro.
    intros i; set_solver.
  - iApply sim_expr_must_step_all_core_ind; eauto.
    iModIntro. iIntros (j D' P' Hel' Hsub') "Hall". iApply "IHO".
    + iPureIntro. set_solver.
    + iPureIntro. set_solver.
    + done.
Qed.

Lemma sim_expr_to_pool P:
  sim_expr_all P -∗ sim_pool P.
Proof.
  iIntros "H". iApply (sim_pool_coind with "[] H"); clear P. iModIntro.
  iIntros (P D) "Hall". by iApply sim_expr_must_step_all.
Qed.

(*
Lemma pool_steps_concat T I T' J T''':
  pool_steps T I T' → pool_steps T' J T''' →  pool_steps T (I ++ J) T'''.
Proof.
induction 1 as [T|T T' T'' i I Hstep Hsteps IH]; simpl; eauto.
intros Hsteps'%IH. econstructor; eauto.
Qed.

Lemma no_magic_values_step (i: nat) T j T':
  pool_step T j T' →
  i ∈ active_threads T →
  i ∉ active_threads T' →
  i = j.
Proof.
  intros (e & e' & T_f & Hstep & Hlook & ->)%pool_step_iff.
  intros (e'' & Hlook' & Hnval)%active_threads_spec Hnact.
  destruct (decide (i = j)); first eauto.
  exfalso. eapply Hnact, active_threads_spec. exists e''.
  split; last done. eapply lookup_app_l_Some.
  rewrite list_lookup_insert_ne //.
Qed.

Lemma no_magic_values_steps (i: nat) T I T':
  pool_steps T I T' →
  i ∈ active_threads T →
  i ∉ active_threads T' →
  i ∈ (list_to_set I: gset nat).
Proof.
  induction 1 as [|T T' T'' j I Hstep Hsteps]; first naive_solver.
  intros Hact Hnact. destruct (decide (i ∈ active_threads T')); first set_solver.
  eapply no_magic_values_step in Hstep; eauto; subst; set_solver.
Qed.

Lemma lookup_pool P j e_t e_s:
  P.(tgt) !! j = Some e_t → P.(src) !! j = Some e_s → P !! j = Some (e_t, e_s).
Proof.
  rewrite !list_lookup_fmap; destruct (P !! j) as [[]|]; simpl; naive_solver.
Qed.

Lemma sim_pool_unfold_fair_div P D:
  fair_div P.(tgt) D →
  sim_pool P →
  ∃ P' D' I, sim_pool P' ∧
           fair_div P'.(tgt) D' ∧
           pool_steps P.(src) I P'.(src) ∧
           (all_values (threads P.(src) ∖ list_to_set I) P') ∧
           filter (λ i, i ∈ active_threads P.(src)) (threads P.(src)) ⊆ list_to_set I.
Proof.
  intros Hfair. rewrite /sim_pool.
  rewrite {1}gfp_fixpoint. fold sim_pool. rewrite /sim_pool_body.
  intros Hlfp; specialize (Hlfp D).
  revert Hlfp. rewrite threads_src_tgt. generalize (threads P.(src)) as O.
  intros O Hlfp. revert P O D Hlfp Hfair.
  change (lfp (must_step sim_pool) ⪯
    λ P O D, fair_div P.(tgt) D → ∃ P' D' I,
        sim_pool P' ∧ fair_div P'.(tgt) D' ∧ pool_steps P.(src) I P'.(src) ∧
        (all_values (O ∖ list_to_set I) P') ∧
        filter (λ i : nat, i ∈ active_threads P.(src)) O ⊆ list_to_set I).
  eapply lfp_least_pre_fixpoint; intros P O D MustStep Hfair.
  destruct Hfair as [i T' D' Hstep Hdel Hfair].
  destruct (MustStep Hdel) as [Values|[Stutter|[CanStep AllSteps]]]; clear MustStep.
  - destruct Values as [Hvalues Hsim]; exists P, D, []. split; first done.
    split; first (econstructor; eauto).
    split; first constructor. split.
    + simpl. intros ??; eapply Hvalues. set_solver.
    + intros j Hj. eapply elem_of_filter in Hj as [Hact HO].
      eapply active_threads_spec in Hact as (e & Hlook & Hnval).
      eapply Hvalues in HO as (e_t & e_s' & Hlook' & Hval1 & Hval2).
      revert Hlook. rewrite list_lookup_fmap Hlook'; simpl; naive_solver.
  - destruct Stutter as (P' & I & Hsteps & Htgt & IH).
    rewrite Htgt in IH. assert (fair_div P.(tgt) D) as Hfair' by (econstructor; eauto).
    destruct (IH Hfair') as (P'' & D'' & I' &  Hpool & Hfair'' & Hsteps' & Hvalues & Hfilter).
    exists P'', D'', (I ++ I'); split; first done. split; first done.
    split; first by eapply pool_steps_concat. split.
    + intros j Hj. eapply Hvalues. set_solver.
    + rewrite list_to_set_app.
      intros j [Hact Hj]%elem_of_filter.
      destruct (decide (j ∈ (list_to_set I: gset nat))); first by set_solver.
      destruct (decide (j ∈ active_threads P'.*2)).
      { eapply elem_of_union_r, Hfilter, elem_of_filter. set_solver. }
      eapply elem_of_union_l, no_magic_values_steps; eauto.
  - specialize (AllSteps _ _ _ Hstep) as (P' & I & <- & Hpool & Post).
    destruct (Post Hfair) as (P'' & D'' & I' & Hpool' & Hfair' & Hsteps & Hvalues & Hfilter).
    exists P'', D'', (I ++ I'). split; first done.
    split; first done.
    split; first by eapply pool_steps_concat. split.
    + intros ??; eapply Hvalues; set_solver.
    + rewrite list_to_set_app.
      intros j [Hact Hj]%elem_of_filter.
      destruct (decide (j ∈ (list_to_set I: gset nat))); first by set_solver.
      destruct (decide (j ∈ active_threads P'.*2)).
      { eapply elem_of_union_r, Hfilter, elem_of_filter. set_solver. }
      eapply elem_of_union_l, no_magic_values_steps; eauto.
Qed.


Lemma fair_div_must_take_steps P P' D I:
  fair_div P'.(tgt) D →
  pool_steps P.(src) I P'.(src) →
  all_values (threads P.(src) ∖ list_to_set I) P' →
  ∃ j, j ∈ I.
Proof.
  intros Hfair Hsteps Hvalues.
  destruct I; last by set_solver.
  inversion Hsteps as [T H1 H2 Heq|]; subst; clear H2.
  destruct Hfair as [j T'' D'' Hstep Hdel Hfair'].
  eapply fair_pool_step_inv in Hstep as (e & e' & T_f & Hstep & Hlook & -> & ?).
  exfalso. eapply val_no_step; eauto.
  destruct (Hvalues j) as (e_t & e_s & Hlook' & Hval1 & Hval2).
  { rewrite Heq -threads_src_tgt //= difference_empty threads_spec; eauto. }
  revert Hlook Hval1.
  rewrite list_lookup_fmap Hlook' //=. naive_solver.
Qed.


Lemma fair_div_forces_active_source P P' D I:
  fair_div P'.(tgt) D →
  pool_steps P.(src) I P'.(src) →
  all_values (threads P.(src) ∖ list_to_set I) P' →
  ∃ j, j ∈ active_threads P.(src).
Proof.
  intros Hfair Hsteps Hvalues.
  destruct (fair_div_must_take_steps P P' D I) as [i Hi]; eauto.
  inversion Hsteps as [|T T' T'' j J Hstep Hsteps']; subst; first set_solver.
  eapply pool_step_iff in Hstep as (e & e' & T_f & Hstep & Hlook & ->).
  exists j. eapply active_threads_spec.
  exists e; split; first done. intros ?; eapply val_no_step; eauto.
Qed.


Lemma sim_pool_val_or_step P D:
  fair_div P.(tgt) D →
  sim_pool P →
  ∃ P' D' I, sim_pool P' ∧
           fair_div P'.(tgt) D' ∧
           pool_steps P.(src) I P'.(src) ∧
           ∅ ⊂ active_threads P.(src) ⊆ list_to_set I.
Proof.
  intros Hfair Hpool.
  edestruct (sim_pool_unfold_fair_div P D Hfair Hpool) as (P' & D' & I & Hpool' & Hdiv & Hsteps & Hvalues & Hfilter).
  exists P', D', I. do 3 (split; first done).
  revert Hfilter; assert (filter (λ i : nat, i ∈ active_threads P.*2) (threads P.*2) = active_threads P.(src)) as ->.
  { eapply leibniz_equiv. intros j.
    rewrite elem_of_filter threads_spec active_threads_spec.
    naive_solver. }
  intros Hsub; split; last done.
  enough (∃ j, j ∈ active_threads P.(src)) as [j Hj] by set_solver.
  by eapply fair_div_forces_active_source.
Qed.

Lemma sim_pool_fair_div_alt P D:
  fair_div P.(tgt) D →
  sim_pool P →
  fair_div_alt P.(src).
Proof.
  revert P D; cofix IH. intros P D Hfair Hsim.
  destruct (sim_pool_val_or_step _ _ Hfair Hsim) as (P' & D' & I & Hsim' & Hfair' & Hsteps & Hsub).
  econstructor; eauto.
Qed.


Lemma sim_pool_preserves_fair_termination P D:
  fair_div P.(tgt) D →
  sim_pool P →
  ∃ D, fair_div P.(src) D.
Proof.
  intros ??; by eapply fair_div_iff, sim_pool_fair_div_alt.
Qed.

Lemma sim_expr_all_preserves_fair_termination P D:
  fair_div P.(tgt) D →
  sim_expr_all P →
  ∃ D, fair_div P.(src) D.
Proof.
  intros ??; by eapply sim_pool_preserves_fair_termination, sim_expr_to_pool.
Qed.
*)

End fix_lang.