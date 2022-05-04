From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
From iris.algebra Require Import auth list numbers.
From iris.program_logic Require Import adequacy.
From iris_examples.logrel.F_mu_ref_conc.unary Require Import soundness.
From iris.prelude Require Import options.

Definition symbol_typ :=
  TArrow
    TUnit
    (TExist (TProd (TArrow TUnit (TVar 0)) (TArrow (TVar 0) (TBool)))).

Definition symbol_nat : expr :=
  Lam (LetIn (Alloc (#n 0))
             (Pack
                (Pair
                   (Lam (FAA (Var 1) (#n 1)))
                   (Lam (If
                           (BinOp Lt (Var 0) (Load (Var 1)))
                           (#♭ true)
                           (App Unit Unit) (* a stuck term *) )
                ))
             )
      ).

Section symbol_nat_sem_typ.
  Context `{heapIG Σ, inG Σ (authUR max_natUR)}.

  Definition Max_token γ m : iProp Σ := own γ (● MaxNat m).
  Definition Token γ m := own γ (◯ MaxNat (S m)).

  Lemma Token_init : ⊢ |==> ∃ γ, Max_token γ 0.
  Proof. iApply own_alloc; apply auth_auth_valid; done. Qed.

  Lemma Token_alloc γ k :
    Max_token γ k ==∗ Max_token γ (k + 1) ∗ Token γ k.
  Proof.
    iIntros "Hk".
    rewrite /Max_token /Token Nat.add_1_r; simpl.
    iMod (own_update _ _ (● MaxNat (S k) ⋅ ◯ MaxNat (S k)) with "Hk")
      as "[$ $]"; last done.
    apply auth_update_alloc.
    apply max_nat_local_update; simpl; lia.
  Qed.

  Lemma Token_lt γ k k' : Max_token γ k -∗ Token γ k' -∗ ⌜k' < k⌝.
  Proof.
    iIntros "Hmt Htk".
    rewrite /Max_token /Token; simpl.
    by iDestruct (own_valid_2 with "Hmt Htk") as
        %[?%max_nat_included _]%auth_both_valid_discrete.
  Qed.

  Lemma symbol_nat_sem_typ : ⊢ [] ⊨ symbol_nat : symbol_typ.
  Proof using Type*.
    iIntros (Δ vs) "!# HΔ".
    rewrite /symbol_nat /symbol_typ /interp_expr /=.
    iDestruct (interp_env_length with "HΔ") as %?; destruct vs; last done.
    asimpl.
    iApply wp_value.
    iModIntro.
    iIntros (? ?); simplify_eq; simpl.
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_alloc; first done.
    iNext. iIntros (l) "Hl".
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iMod Token_init as (γ) "Hmt".
    iMod (inv_alloc (nroot .@ "tk") _ (∃ t, l ↦ᵢ (#nv t) ∗ Max_token γ t)
            with "[Hl Hmt]") as "#Hinv".
    { unfold Max_token. by iNext; iExists _; iFrame. }
    iApply wp_value.
    iModIntro.
    iExists (PersPred (λ v, ∃ m, ⌜v = #nv m⌝ ∗ Token γ m))%I; simpl.
    iExists _; iSplit; first done.
    iExists _, _; iSplit; first done.
    iSplit.
    - iModIntro.
      iIntros (? ?); simplify_eq; simpl.
      iApply wp_pure_step_later; auto. iNext. asimpl.
      iApply wp_atomic.
      iInv (nroot.@"tk") as (t) "[Hl Hmt]" "Hcl".
      iModIntro.
      iApply (wp_FAA with "Hl").
      iNext. iIntros "Hl".
      iMod (Token_alloc with "Hmt") as "[Hmt Htk]".
      iMod ("Hcl" with "[Hl Hmt]") as "_"; last by eauto.
      iNext; iExists _; iFrame.
    - iModIntro.
      iIntros (w). iDestruct 1 as (m ?) "Htk"; simplify_eq.
      iApply wp_pure_step_later; auto. iNext. asimpl.
      iApply (wp_bind (fill [IfCtx _ _])).
      iApply (wp_bind (fill [BinOpRCtx _ (#nv _)])).
      iApply wp_atomic.
      iInv (nroot.@"tk") as (t) "[Hl Hmt]" "Hcl".
      iModIntro.
      iApply (wp_load with "Hl").
      iNext. iIntros "Hl".
      iDestruct (Token_lt with "Hmt Htk") as %?.
      iMod ("Hcl" with "[Hl Hmt]") as "_".
      { iNext; iExists _; iFrame. }
      iModIntro.
      simpl.
      iApply wp_pure_step_later; auto. iNext.
      simpl. destruct lt_dec; last done. simpl.
      iApply wp_value.
      iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; eauto.
  Qed.

End symbol_nat_sem_typ.
