From iris Require Import bi bi.lib.fixpoint bi.updates bi.derived_laws.
From iris.proofmode Require Import tactics.
Import bi.

(* Satisfiability *)
Section satisfiable.

  Context {PROP : bi}.
  Context {PROP_bupd : BiBUpd PROP}.
  Context {PROP_affine : BiAffine PROP}.
  Implicit Types (P Q: PROP).

  Class Satisfiable (sat: PROP → Prop) := {
    sat_mono P Q: (P ⊢ Q) → sat P → sat Q;
    sat_elim φ: sat (⌜φ⌝)%I → φ;
    sat_bupd P: sat (|==> P)%I → sat P;
    sat_exists {X} Φ: sat (∃ x: X, Φ x)%I → ∃ x: X, sat (Φ x);
  }.

  Section derived_lemmas.
    Context {sat: PROP → Prop} `{Satisfiable sat}.
    Arguments sat _%I.

    (* derived *)
    Global Instance sat_if: Proper ((⊢) ==> impl) sat.
    Proof. intros P Q Hent Hsat; by eapply sat_mono. Qed.

    Global Instance sat_equiv: Proper ((≡) ==> iff) sat.
    Proof.
      intros P Q Heq; split; intros Hsat; eauto using sat_mono, equiv_entails, equiv_entails_sym.
    Qed.

    Lemma sat_sep P Q: sat (P ∗ Q) → sat P ∧ sat Q.
    Proof.
      intros Hsat; split; eapply sat_mono, Hsat; by iIntros "[P Q]".
    Qed.
    Lemma sat_and P Q: sat (P ∧ Q) → sat P ∧ sat Q.
    Proof.
      intros Hsat; split; eapply sat_mono, Hsat;
      eauto using bi.and_elim_l, bi.and_elim_r.
    Qed.
    Lemma sat_or P Q: sat (P ∨ Q) → sat P ∨ sat Q.
    Proof.
      rewrite or_alt; intros [[] Hsat] % sat_exists; eauto.
    Qed.
    Lemma sat_forall {X} Φ x: sat (∀ x: X, Φ x) → sat (Φ x).
    Proof.
      eapply sat_mono; eauto.
    Qed.
    Lemma sat_pers P: sat (<pers> P) → sat P.
    Proof.
      eapply sat_mono; eauto.
    Qed.
    Lemma sat_intuitionistic P: sat (□ P) → sat P.
    Proof.
      eapply sat_mono; eauto.
    Qed.
    Lemma sat_impl P Q: (⊢ P) → sat (P → Q) →  sat Q.
    Proof.
      intros Hent Hsat; eapply sat_mono, Hsat.
      iIntros "H". iApply impl_elim_r. iSplit; eauto.
      iApply Hent.
    Qed.
    Lemma sat_wand P Q: (⊢ P) → sat (P -∗ Q) → sat Q.
    Proof.
      intros Hent Hsat; eapply sat_mono, Hsat.
      iIntros "HPQ". iApply "HPQ". iApply Hent.
    Qed.
  End derived_lemmas.

  Section sat_frame.
    Context {sat: PROP → Prop} `{Satisfiable sat}.
    Arguments sat _%I.

    Definition sat_frame (F P: PROP) := sat (F ∗ P).

    Global Instance sat_frame_satisfiable F: Satisfiable (sat_frame F).
    Proof.
      split; unfold sat_frame.
      - intros P Q HPQ Hsat. eapply sat_mono, Hsat.
        iIntros "($ & P)". by iApply HPQ.
      - intros Φ Hsat. eapply sat_elim, sat_mono, Hsat.
        iIntros "(_ & $)".
      - intros P Hsat. eapply sat_bupd, sat_mono, Hsat.
        iIntros "($ & $)".
      - intros X Φ Hsat. eapply sat_exists, sat_mono, Hsat.
        iIntros "($ & $)".
    Qed.

    Lemma sat_frame_intro P F Q:
      (P -∗ F ∗ Q) → sat P → sat_frame F Q.
    Proof.
      unfold sat_frame; eapply sat_mono.
    Qed.

  End sat_frame.

End satisfiable.
Arguments sat_frame {_} {_}%function_scope _%I _%I.