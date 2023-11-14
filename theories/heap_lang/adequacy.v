From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import mono_nat.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From WBLogic.program_logic Require Export weakestpre adequacy.
From iris.heap_lang Require Import adequacy notation.
From WBLogic.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

Class wbheapGpreS Σ := WBHeapGpreS {
  wbheapGpreS_iris :: invGpreS Σ;
  wbheapGpreS_heap :: gen_heapGpreS loc (option val) Σ;
  wbheapGpreS_inv_heap :: inv_heapGpreS loc (option val) Σ;
  wbheapGpreS_proph :: proph_mapGpreS proph_id (val * val) Σ;
  wbheapGS_step_cnt :: mono_natG Σ;
  wbheapGpreS_gstacks :: gstacksGpre Σ;
}.

Definition wbheapΣ : gFunctors := #[heapΣ; mono_natΣ; gstacksΣ].
Global Instance subG_wbheapGpreS {Σ} : subG wbheapΣ Σ → wbheapGpreS Σ.
Proof. solve_inG. Qed.

Global Instance subG_wbheapΣ_heapΣ `{!subG wbheapΣ Σ} : subG heapΣ Σ.
Proof. match goal with H : _ |- _ => apply subG_inv in H; destruct H end; done. Qed.

(* TODO: The [wp_adequacy] lemma is insufficient for a state interpretation
with a non-constant step index function. We thus use the more general
[wp_strong_adequacy] lemma. The proof below replicates part of the proof of
[wp_adequacy], and it hence would make sense to see if we can prove a version
of [wp_adequacy] for a non-constant step version. *)
Definition wbheap_adequacy Σ `{!wbheapGpreS Σ} e σ φ :
  (∀ `{!wbheapGS Σ}, ⊢ inv_heap_inv -∗ WBWP e @ ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  intros Hwp.
  apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wbwp_strong_adequacy Σ _); [|done].
  iIntros (Hinv ?).
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (mono_nat_own_alloc) as (γ) "[Hsteps _]".
  iDestruct (Hwp (WBHeapGS _ _ _ _ _ _ _ _) with "Hi") as "Hwp".
  iModIntro.
  iExists (λ σ ns κs nt, (gen_heap_interp σ.(heap) ∗
                          proph_map_interp κs σ.(used_proph_id) ∗
                          mono_nat_auth_own γ 1 ns))%I.
  iExists (λ v, ⌜φ v⌝%I), (λ _, True)%I, _ => /=.
  iFrame.
  iIntros (es' t2' -> ?) " _ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|by eauto].
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.
