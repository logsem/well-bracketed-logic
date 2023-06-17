From WBLogrel.F_mu_ref.unary Require Export fundamental.
From iris.algebra Require Import auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From WBLogrel.program_logic Require Import adequacy.
From iris.prelude Require Import options.

Class soundness_unary_preG Σ := soundness_unary_preIG {
  soundness_unary_preG_iris :: invGpreS Σ;
  soundness_unary_preG_heap :: gen_heapGpreS loc F_mu_ref.val Σ;
  soundness_unary_preG_reg :: gstacksGpre Σ
}.

Theorem soundness Σ `{soundness_unary_preG Σ} e τ e' thp σ σ' :
  (∀ `{!heapIG Σ}, ⊢ [] ⊨ e : τ) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  not_stuck e' σ'.
Proof.
  intros Hlog ??.
  cut (adequate NotStuck e σ (λ _ _, True));
    first by intros [_ Hsafe]; eapply Hsafe; eauto.
  eapply (wbwp_adequacy Σ _). iIntros (Hinv ? ?).
  iMod (gen_heap_init σ) as (Hheap) "[Hh _]".
  iModIntro. iExists (λ σ _, gen_heap_interp σ), (λ _, True%I); iFrame.
  set (HeapΣ := (HeapIG Σ Hinv Hheap _)).
  replace e with e.[env_subst[]] by by asimpl.
  iApply (wbwp_wand with "[]"); last by iIntros (?) "_".
  iApply (Hlog HeapΣ $! [] []); iApply (@interp_env_nil _ HeapΣ).
Qed.

Corollary type_soundness e τ e' thp σ σ' :
  [] ⊢ₜ e : τ →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp → not_stuck e' σ'.
Proof.
  intros ??. set (Σ := #[invΣ ; gen_heapΣ loc F_mu_ref.val; gstacksΣ]).
  set (HG := soundness_unary_preIG Σ _ _ _).
  eapply (soundness Σ); eauto using fundamental.
Qed.
