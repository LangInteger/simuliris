From stdpp Require Import gmap relations.
From iris.prelude Require Import options.
From simuliris.simulation Require Import language.
From Coq.Logic Require Import Classical.

Section fairness.
Context {Λ: language}.

Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types c : expr_class Λ.
Implicit Types K : ectx Λ.
Implicit Types p : prog Λ.
Implicit Types T efs : list (expr Λ).

Definition enabled p i T σ :=
  ∃ e, T !! i = Some e ∧ reducible p e σ.

Definition exec: Type := nat → list (expr Λ) * state Λ * nat.

Notation "f '.(pool)'" := (fst (fst f)) (at level 5).
Notation "f '.(state)'" := (snd (fst f)) (at level 5).
Notation "f '.(id)'" := (snd f) (at level 5).


Definition diverges p (f: exec) T σ :=
  ((f 0).(pool) = T) ∧
  ((f 0).(state) = σ) ∧
  (∀ n, pool_step p (f n).(pool) (f n).(state) (f n).(id) (f (S n)).(pool) (f (S n)).(state)).

Record div_exec p T σ: Type := {
  the_exec :> nat → list (expr Λ) * state Λ * nat;
  exec_diverges: diverges p the_exec T σ
}.

Definition eventually_always_enabled {p T σ} i (f: div_exec p T σ)  :=
  ∃ m, ∀ n, m ≤ n → enabled p i ((f n).(pool)) ((f n).(state)).

Definition always_eventually_steps {p T σ} i (f: div_exec p T σ)  :=
  ∀ m, ∃ n, m ≤ n ∧ (f n).(id) = i.

Definition fair {p T σ} (f: div_exec p T σ) :=
  ∀ i, eventually_always_enabled i f → always_eventually_steps i f.

Definition fair_div p T σ := ∃ f: div_exec p T σ, fair f.




(* some theory about diverging executions *)
Program Definition div_exec_advance {p T σ} (f: div_exec p T σ) n: div_exec p (f n).(pool) (f n).(state) :=
  {| the_exec m := f (n + m) |}.
Next Obligation.
  intros p T σ f n; rewrite /diverges.
  replace (n + 0) with n by lia.
  do 2 (split; first done).
  intros k; simpl; rewrite Nat.add_succ_r.
  eapply exec_diverges.
Qed.

Definition div_exec_next {p T σ} (f: div_exec p T σ) : div_exec p (f 1).(pool) (f 1).(state) := div_exec_advance f 1.

Definition div_exec_trace {p T σ} (f: div_exec p T σ) n :=
  fmap (λ i, (f i).(id)) (seq 0 n).


Lemma div_exec_trace_spec {p T σ} (f: div_exec p T σ) n i:
  i ∈ div_exec_trace f n ↔ (∃ m, (f m).(id) = i ∧ m < n).
Proof.
  rewrite /div_exec_trace elem_of_list_fmap.
  split; intros (m & Heq & Hlt); exists m; (split; first done).
  - eapply elem_of_seq in Hlt. lia.
  - eapply elem_of_seq. lia.
Qed.

Lemma div_exec_trace_zero {p T σ} (f: div_exec p T σ):
  div_exec_trace f 0 = [].
Proof.
  reflexivity.
Qed.

Lemma div_exec_trace_succ {p T σ} (f: div_exec p T σ) n:
  div_exec_trace f (S n) = (f 0).(id) :: div_exec_trace (div_exec_next f) n.
Proof.
  change (div_exec_trace f (S n)) with ((f 0).(id) :: ((λ i, (f i).(id)) <$> seq 1 n)).
  f_equiv. rewrite /div_exec_trace -fmap_S_seq -list_fmap_compose //.
Qed.

Lemma div_exec_next_step p T σ (f: div_exec p T σ):
  pool_step p T σ (f 0).(id) (div_exec_next f 0).(pool) (div_exec_next f 0).(state).
Proof.
  destruct (exec_diverges _ _ _ (div_exec_next f))as (-> & -> & _).
  destruct (exec_diverges _ _ _ f) as (H1 & H2 & Hsteps).
  specialize (Hsteps 0). by rewrite H1 H2 in Hsteps.
Qed.

Lemma div_exec_steps {p T σ} (f: div_exec p T σ) n:
  pool_steps p T σ (div_exec_trace f n) (f n).(pool) (f n).(state).
Proof.
  revert p T σ f; induction n as [|n IH]; intros p T σ f.
  - destruct (exec_diverges _ _ _ f) as (-> & -> & ?); constructor.
  - rewrite div_exec_trace_succ.  econstructor; eauto using div_exec_next_step.
    simpl. eapply IH.
Qed.





(* Below, we rely on notions of fairness which assume safety.
   With safety, enabled threads are those that are not
   values (see active_safe_enabled). We call those threads
  *active*. *)

Definition active_threads T :=
  list_to_set (C := gset nat) (fmap fst (filter (λ '(i, e), to_val e = None) (imap pair T))).

Lemma active_threads_spec T i:
  i ∈ active_threads T ↔ ∃ e, T !! i = Some e ∧ to_val e = None.
Proof.
  rewrite /active_threads /enabled elem_of_list_to_set elem_of_list_fmap.
  split.
  - intros [[i' e] [-> Hlook]]; simpl.
    eapply elem_of_list_filter in Hlook as [? Hlook].
    eapply elem_of_lookup_imap in Hlook as (? & ? & Heq & ?).
    injection Heq as ??; subst. eexists; split; eauto.
  - intros [e [Hlook Hval]]. exists (i, e).
    split; first done. eapply elem_of_list_filter.
    split; first done. eapply elem_of_lookup_imap.
    eexists _, _. split; done.
Qed.

Lemma active_threads_step p T σ i T' σ':
  pool_step p T σ  i T' σ' → active_threads T ∖ {[i]} ⊆ active_threads T'.
Proof.
  intros (e & e' & T_f & Hstep & Hlook & ->)%pool_step_iff.
  intros j [Hact Hnj]%elem_of_difference.
  eapply active_threads_spec in Hact as (e'' & Hlook' & Hnval).
  assert (i ≠ j) by set_solver.
  eapply active_threads_spec. exists e''; split; last done.
  eapply lookup_app_l_Some. rewrite list_lookup_insert_ne //.
Qed.

Lemma active_threads_steps p T σ I T' σ':
  pool_steps p T σ I T' σ' → active_threads T ∖ list_to_set I ⊆ active_threads T'.
Proof.
  induction 1 as [|T T' T'' σ σ' σ'' i I Hstep Hsteps]; simpl; first set_solver.
  eapply active_threads_step in Hstep. set_solver.
Qed.

(* classic proof *)
Lemma active_safe_enabled i p T σ:
  pool_safe p T σ →
  i ∈ active_threads T →
  enabled p i T σ.
Proof.
  rewrite active_threads_spec; intros Hsafe (e & Hlook & Hnval).
  exists e; split; first done.
  eapply pool_safe_threads_safe in Hsafe; last done.
  rewrite /safe in Hsafe. destruct (classic (reducible p e σ)); first done.
  exfalso. eapply Hsafe; exists [e], σ, []; split; first constructor.
  exists e, 0; split; first done.
  split; first done. by eapply not_reducible.
Qed.

  (* classic proof *)
  Lemma active_eventually_steps p T σ (f: div_exec p T σ) i :
    fair f →
    pool_safe p T σ →
    i ∈ active_threads T →
    ∃ n, (f n).(id) = i.
  Proof.
    intros Hfair Hsafe Hact.
    destruct (classic (∃ n, (f n).(id) = i)) as [|Hne]; first done.
    exfalso. feed pose proof (Hfair i) as Hsteps; last first.
    { rewrite /always_eventually_steps in Hsteps.
      specialize (Hsteps 0). by naive_solver. }
    exists 0. intros n _. specialize (div_exec_steps f n) as Hsteps.
    eapply active_threads_steps in Hsteps. eapply active_safe_enabled.
    - eapply pool_steps_safe, Hsafe. eapply div_exec_steps.
    - eapply Hsteps, elem_of_difference; split; first done.
      rewrite elem_of_list_to_set. intros (m & Heq & _)%div_exec_trace_spec. naive_solver.
  Qed.








Section coinductive_inductive_fairness.

  CoInductive fair_div_coind p T σ : Prop :=
    fair_div_coind_step T' σ' I:
      pool_steps p T σ I T' σ' →
      ∅ ⊂ active_threads T ⊆ list_to_set I →
      fair_div_coind p T' σ' →
      fair_div_coind p T σ.


  Lemma all_active_eventually_step p T σ (f: div_exec p T σ) :
    fair f →
    pool_safe p T σ →
    ∃ n, active_threads T ⊆ list_to_set (div_exec_trace f n).
  Proof.
    intros Hfair Hsafe.
    enough (∀ O, O ⊆ active_threads T → ∃ n, O ⊆ list_to_set (div_exec_trace f n)) by eauto.
    intros O; induction (set_wf O) as [O _ IHO]; intros Hsub.
    destruct (decide (O ≡ ∅)) as [->%leibniz_equiv|[j Hj]%set_choose].
    - exists 0. set_solver.
    - eapply Hsub in Hj as Hact. eapply active_eventually_steps in Hact as (n1 & Hsteps); eauto.
      destruct (IHO (O ∖ {[j]})) as (n2 & Hstep'); [set_solver..|].
      exists (max n1 n2 + 1). intros k Hk. eapply elem_of_list_to_set, div_exec_trace_spec.
      destruct (decide (j = k)).
      + subst. exists n1. split; first done. lia.
      + assert (k ∈ div_exec_trace f n2) as Hel by (eapply elem_of_list_to_set; set_solver).
        eapply div_exec_trace_spec in Hel as (m & ? & ?).
        exists m. split; first done. lia.
  Qed.

  Lemma div_exec_some_active p T σ (f: div_exec p T σ) :
    ∃ i, i ∈ active_threads T.
  Proof.
    exists (f 0).(id). eapply active_threads_spec.
    specialize (div_exec_next_step _ _ _ f) as Hstep.
    eapply pool_step_iff in Hstep as (e & e' & efs & Hstep & Hlook & _).
    exists e. split; first done. by eapply val_stuck.
  Qed.

  Lemma fair_div_exec_advance p T σ (f: div_exec p T σ) n :
    fair f → fair (div_exec_advance f n).
  Proof.
    intros Hfair i Henabled.
    feed pose proof (Hfair i) as Hsteps.
    - destruct Henabled as (m & Hen). exists (m + n).
      intros n' (n'' & ->)%nat_le_sum.
      feed pose proof (Hen (m + n'')) as Hen; first lia.
      simpl in Hen. by replace (m + n + n'') with (n + (m + n'')) by lia.
    - intros k. destruct (Hsteps (n + k)) as (m' & (m & ->)%nat_le_sum & Hstep).
      exists (k + m). split; first lia. simpl.
      by replace (n + (k + m)) with (n + k + m) by lia.
  Qed.


  Lemma fair_div_post_fix_coind p T σ:
    fair_div p T σ →
    pool_safe p T σ →
    ∃ I T' σ', fair_div p T' σ' ∧
    pool_safe p T' σ' ∧
    pool_steps p T σ I T' σ' ∧
    ∅ ⊂ active_threads T ⊆ list_to_set I.
  Proof.
    intros [f Hfair] Hsafe.
    destruct (all_active_eventually_step _ _ _ _ Hfair Hsafe) as (n & Hsub).
    destruct (div_exec_some_active _ _ _ f) as (i & Hact).
    exists (div_exec_trace f n), (f n).(pool), (f n).(state).
    split; last split; last split.
    - exists (div_exec_advance f n). eapply fair_div_exec_advance, Hfair.
    - eapply pool_steps_safe; eauto using div_exec_steps.
    - eapply div_exec_steps.
    - split; set_solver.
  Qed.

  Lemma fair_div_to_fair_div_coind p T σ:
    fair_div p T σ →
    pool_safe p T σ →
    fair_div_coind p T σ.
  Proof.
    revert p T σ; cofix IH; intros p T σ Hfair Hsafe.
    destruct (fair_div_post_fix_coind _ _ _ Hfair Hsafe) as (I & T' & σ' & Hfair' & Hsafe' & Hsteps & Hact).
    econstructor; eauto.
  Qed.

End coinductive_inductive_fairness.



Section delay_based_fairness.
  Implicit Types D : gmap nat nat.

  Definition delays_for T D :=
    ∀ i, i ∈ active_threads T → is_Some (D !! i).

  Definition step_decr i D D' :=
    (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n').

  Inductive fair_pool_step (p: prog Λ):
    list (expr Λ) → gmap nat nat → state Λ → nat →
    list (expr Λ) → gmap nat nat → state Λ → Prop :=
    take_fair_step i T T' σ σ' D D':
      pool_step p T σ i T' σ' →
      step_decr i D D' →
      fair_pool_step p T D σ i T' D' σ'.

  Inductive fair_pool_steps (p: prog Λ):
    list (expr Λ) → gmap nat nat → state Λ → list nat →
    list (expr Λ) → gmap nat nat → state Λ → Prop :=
    | fair_pool_no_steps T σ (D: gmap nat nat) :
      delays_for T D → fair_pool_steps p T D σ [] T D σ
    | fair_pool_do_steps T T' T'' (D D' D'': gmap nat nat) (σ σ' σ'': state Λ) i I:
      delays_for T D →
      fair_pool_step p T D σ i T' D' σ' →
      fair_pool_steps p T' D' σ' I T'' D'' σ'' →
      fair_pool_steps p T D σ (i :: I) T'' D'' σ''.

  CoInductive fair_div_delay p T D σ : Prop :=
  | fair_div_step i T' D' σ':
    fair_pool_step p T D σ i T' D' σ' →
    delays_for T D →
    fair_div_delay p T' D' σ' →
    fair_div_delay p T D σ.

  CoInductive fair_div_delay_tc p T D σ : Prop :=
  | fair_div_tc_step I T' σ' D':
    I ≠ [] →
    fair_pool_steps p T D σ I T' D' σ' →
    fair_div_delay_tc p T' D' σ' →
    fair_div_delay_tc p T D σ.

  Lemma fair_pool_step_iff p T D σ i T' D' σ':
    fair_pool_step p T D σ i T' D' σ' ↔
      pool_step p T σ i T' σ' ∧ step_decr i D D'.
  Proof.
    split; destruct 1; eauto 10 using take_fair_step.
  Qed.

  Lemma fair_pool_step_inv p T σ D i T' σ' D':
    fair_pool_step p T D σ i T' D' σ' →
      ∃ e e' efs, prim_step p e σ e' σ' efs ∧
      T !! i = Some e ∧
      T' = <[i := e']> T ++ efs ∧
      step_decr i D D'.
  Proof.
    destruct 1 as [i T T' σ σ' D D' Pool Hdecr].
    eapply pool_step_iff in Pool as (e & e' & T_f & Hstep & Hlook & Hupd).
    eauto 10.
  Qed.



End delay_based_fairness.
End fairness.


