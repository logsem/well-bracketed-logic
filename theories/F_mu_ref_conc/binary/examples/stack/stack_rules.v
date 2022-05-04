From iris.proofmode Require Import proofmode.
From iris_examples.logrel.F_mu_ref_conc.binary Require Import logrel.
From iris.prelude Require Import options.

Section Rules.
  Context `{heapIG Σ}.
  Notation D := (persistent_predO (val * val) (iPropI Σ)).

  Program Definition StackLink_pre (Q : D) : D -n> D := λne P,
    PersPred (λ v, ∃ l w, ⌜v.1 = LocV l⌝ ∗ l ↦ᵢ□ w ∗
            ((⌜w = InjLV UnitV⌝ ∧ ⌜v.2 = FoldV (InjLV UnitV)⌝) ∨
            (∃ y1 z1 y2 z2, ⌜w = InjRV (PairV y1 (FoldV z1))⌝ ∗
              ⌜v.2 = FoldV (InjRV (PairV y2 z2))⌝ ∗ Q (y1, y2) ∗ ▷ P(z1, z2))))%I.
  Solve Obligations with solve_proper.

  Global Instance StackLink_pre_contractive Q : Contractive (StackLink_pre Q).
  Proof. solve_contractive. Qed.

  Definition StackLink (Q : D) : D := fixpoint (StackLink_pre Q).

  Lemma StackLink_unfold Q v :
    StackLink Q v ≡ (∃ l w,
      ⌜v.1 = LocV l⌝ ∗ l ↦ᵢ□ w ∗
      ((⌜w = InjLV UnitV⌝ ∧ ⌜v.2 = FoldV (InjLV UnitV)⌝) ∨
      (∃ y1 z1 y2 z2, ⌜w = InjRV (PairV y1 (FoldV z1))⌝
                      ∗ ⌜v.2 = FoldV (InjRV (PairV y2 z2))⌝
                      ∗ Q (y1, y2) ∗ ▷ @StackLink Q (z1, z2))))%I.
  Proof. rewrite {1}/StackLink (fixpoint_unfold (StackLink_pre Q) v) //. Qed.

  Global Opaque StackLink. (* So that we can only use the unfold above. *)

  Global Instance StackLink_persistent (Q : D) v `{∀ vw, Persistent (Q vw)} :
    Persistent (StackLink Q v).
  Proof.
    unfold Persistent.
    iIntros "H". iLöb as "IH" forall (v). rewrite StackLink_unfold.
    iDestruct "H" as (l w) "[% [#Hl [#Hr|Hr]]]"; subst.
    { iExists l, w; iModIntro; eauto. }
    iDestruct "Hr" as (y1 z1 y2 z2) "[#H1 [#H2 [#HQ H']]]".
    iDestruct ("IH" with "H'") as "#H''". iClear "H'".
    iModIntro. eauto 20.
  Qed.
End Rules.
