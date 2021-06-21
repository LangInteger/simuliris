From simuliris.stacked_borrows Require Import proofmode.

(** * Some trivial tests to check that the proofmode works *)
Section boring_lang.
Context `{sborGS Σ}.

Definition val_rel (r1 r2 : result) : iProp Σ := ⌜r1 = r2⌝.
(*Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.*)

Lemma test1 π :
  ⊢ (let: "x" :=  #[ScInt 5] + #[ScInt 5] in "x") ⪯{π, val_rel} #[ScInt 10] {{ val_rel }}.
Proof.
  (*target_bind (_ + _)%E. *)
  (*target_bind (Let _ _ _)%E.*)
  sim_pures.
  sim_val. eauto.
Qed.

End boring_lang.
