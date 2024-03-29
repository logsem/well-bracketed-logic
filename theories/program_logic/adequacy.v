(* This file is taken from iris and edited. *)

From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Import adequacy.
From WBLogic.program_logic Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

(** This file contains the adequacy statements of the Iris program logic. First
we prove a number of auxilary results. *)

(** Iris's generic adequacy result *)
(** The lemma is parameterized by [use_credits] over whether to make later credits available or not.
  Below, a concrete instances is provided with later credits (see [wp_strong_adequacy]). *)
Lemma wbwp_strong_adequacy Σ Λ `{!invGpreS Σ, !gstacksGpre Σ} e σ1 n κs t2 σ2 φ
  (num_laters_per_step : nat → nat) :
  (* WP *)
  (∀ `{Hinv : !invGS Σ, !gstacksIG Σ},
      ⊢ |={⊤}=> ∃
         (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
         (Φ : val Λ → iProp Σ)
         (fork_post : val Λ → iProp Σ)
         (* Note: existentially quantifying over Iris goal! [iExists _] should
         usually work. *)
         state_interp_mono,
       let _ : irisGS Λ Σ :=
           IrisG Hinv stateI fork_post num_laters_per_step state_interp_mono
       in
       stateI σ1 0 κs 0 ∗
       WBWP e @ ∅; ⊤ {{ Φ }} ∗
       (∀ e' t2',
         (* es' is the final state of the initial threads, t2' the rest *)
         ⌜ t2 = e' :: t2' ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ⌜ ∀ e2, e2 ∈ t2 → not_stuck e2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 n [] (length t2') -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         (from_option Φ True (to_val e')) -∗
         (* For all forked-off threads that are done, their postcondition
            [fork_post] holds. *)
         ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n ([e], σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  iIntros (Hwp ?).
  eapply wp_strong_adequacy_gen; [eassumption| |eassumption].
  iIntros (?) "".
  iMod gstacks_init as (?) "HM".
  iMod Hwp as (SI Φ fpost SI_mono) "(Hsi&Hwp&Hpost)".
  iModIntro; iExists SI, [Φ], fpost, SI_mono; iFrame "Hsi".
  iSplitL "HM Hwp".
  { iSplitL; last done. rewrite /= /wbwp.
    iApply (wp_wand with "[HM Hwp]"); first by iApply "Hwp".
    iIntros (?); iDestruct 1 as (?) "(?&?&$)". }
  iIntros (es' ? ? ? Hnstuck) "Hsi Hps Hops".
  destruct es' as [|? []]; simplify_eq/=.
  iDestruct "Hps" as "[Hps _]".
  iApply ("Hpost" with "[//] [] [$] [$] [$]").
  iPureIntro.
  intros ?; apply Hnstuck; done.
Qed.

(** This simpler form of adequacy requires the [irisGS] instance that you use
everywhere to syntactically be of the form
{|
  iris_invGS := ...;
  state_interp σ _ κs _ := ...;
  fork_post v := ...;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
|}
In other words, the state interpretation must ignore [ns] and [nt], the number
of laters per step must be 0, and the proof of [state_interp_mono] must have
this specific proof term.
*)
(** Again, we first prove a lemma generic over the usage of credits. *)
Lemma wbwp_adequacy Σ Λ `{!invGpreS Σ, !gstacksGpre Σ} e σ φ :
  (∀ `{Hinv : !invGS Σ, !gstacksIG Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS Λ Σ :=
           IrisG Hinv (λ σ _ κs _, stateI σ κs) fork_post (λ _, 0)
                 (λ _ _ _ _, fupd_intro _ _)
       in
       stateI σ κs ∗ WBWP e @ ∅; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  intros Hwp.
  apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply wbwp_strong_adequacy; [eassumption|eassumption| |eassumption].
  intros ??.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iExists (λ σ _ κs _, stateI σ κs), (λ v, ⌜φ v⌝%I), fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> ?) "_ H _".
  iApply fupd_mask_intro_discard; [done|].
  iSplit; last by eauto.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

Lemma wbwp_invariance Σ Λ `{!invGpreS Σ, !gstacksGpre Σ} e1 σ1 t2 σ2 φ :
  (∀ `{Hinv : !invGS Σ, !gstacksIG Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS Λ Σ := IrisG Hinv (λ σ _, stateI σ) fork_post
              (λ _, 0) (λ _ _ _ _, fupd_intro _ _) in
       stateI σ1 κs 0 ∗ WBWP e1 @ ∅; ⊤ {{ _, True }} ∗
       (stateI σ2 [] (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (wbwp_strong_adequacy Σ); [eassumption|eassumption| |eassumption]=> ??.
  iMod (Hwp _ _ κs) as (stateI fork_post) "(Hσ & Hwp & Hφ)".
  iExists (λ σ _, stateI σ), (λ _, True)%I, fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> _) "Hσ H _ /=".
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_intro_discard; first set_solver.
Qed.
