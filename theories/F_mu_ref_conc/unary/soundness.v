From iris_examples.logrel.F_mu_ref_conc.unary Require Export fundamental.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris.prelude Require Import options.

Class heapPreIG Σ := HeapPreIG {
  heap_preG_iris :> invGpreS Σ;
  heap_preG_heap :> gen_heapGpreS loc F_mu_ref_conc.val Σ
}.

Theorem soundness Σ `{heapPreIG Σ} e τ e' thp σ σ' :
  (∀ `{heapIG Σ}, ⊢ [] ⊨ e : τ) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  not_stuck e' σ'.
Proof.
  intros Hlog ??.
  cut (adequate NotStuck e σ (λ _ _, True));
    first by intros [_ Hsafe]; eapply Hsafe; eauto.
  eapply (wp_adequacy Σ _). iIntros (Hinv ?).
  iMod (gen_heap_init σ) as (Hheap) "[Hh _]".
  iModIntro. iExists (λ σ _, gen_heap_interp σ), (λ _, True%I); iFrame.
  set (HeapΣ := (HeapIG Σ Hinv Hheap)).
  iApply (wp_wand with "[]").
  - replace e with e.[env_subst[]] by by asimpl.
    iApply (Hlog HeapΣ $! [] []). iApply (@interp_env_nil _ HeapΣ).
  - eauto.
Qed.

Corollary type_soundness e τ e' thp σ σ' :
  [] ⊢ₜ e : τ →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp → not_stuck e' σ'.
Proof.
  intros ??. set (Σ := #[invΣ ; gen_heapΣ loc F_mu_ref_conc.val]).
  set (HG := HeapPreIG Σ _ _).
  eapply (soundness Σ); eauto using fundamental.
Qed.
