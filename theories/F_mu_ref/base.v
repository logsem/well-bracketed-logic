From iris.program_logic Require Import weakestpre.
From iris.base_logic Require Import invariants.
From Autosubst Require Export Autosubst.
From iris.prelude Require Import options.

Canonical Structure varO := leibnizO var.

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
  Proof using Type*.
    revert x; induction m as [|m IH]=> -[|x];
      repeat (destruct (lt_dec _ _) || asimpl || rewrite IH); auto with lia.
  Qed.
End Autosubst_Lemmas.

Ltac properness :=
  repeat match goal with
  | |- (∃ _: _, _)%I ≡ (∃ _: _, _)%I => apply bi.exist_proper =>?
  | |- (∀ _: _, _)%I ≡ (∀ _: _, _)%I => apply bi.forall_proper =>?
  | |- (_ ∧ _)%I ≡ (_ ∧ _)%I => apply bi.and_proper
  | |- (_ ∨ _)%I ≡ (_ ∨ _)%I => apply bi.or_proper
  | |- (_ → _)%I ≡ (_ → _)%I => apply bi.impl_proper
  | |- (WP _ {{ _ }})%I ≡ (WP _ {{ _ }})%I => apply wp_proper =>?
  | |- (▷ _)%I ≡ (▷ _)%I => apply bi.later_proper
  | |- (□ _)%I ≡ (□ _)%I => apply bi.intuitionistically_proper
  | |- (_ ∗ _)%I ≡ (_ ∗ _)%I => apply bi.sep_proper
  | |- (inv _ _)%I ≡ (inv _ _)%I => apply (contractive_proper _)
  end.

Ltac solve_proper_alt :=
  repeat intro; (simpl + idtac);
  by repeat match goal with H : _ ≡{_}≡ _|- _ => rewrite H end.

Reserved Notation "⟦ τ ⟧" (at level 0, τ at level 70).
Reserved Notation "⟦ τ ⟧ₑ" (at level 0, τ at level 70).
Reserved Notation "⟦ Γ ⟧*" (at level 0, Γ at level 70).
