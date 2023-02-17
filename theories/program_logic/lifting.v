(** This file has been taken from iris and edited accordingly. *)
(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
From WBLogrel.program_logic Require Export weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{!irisGS Λ Σ, !gstacksIG Σ}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Lemma wbwp_pure_step_fupd `{!Inhabited (state Λ)} E E' out e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (|={E}[E']▷=>^n £ n -∗ WBWP e2 @ out; E {{ Φ }}) ⊢ WBWP e1 @ out; E {{ Φ }}.
Proof.
  rewrite /wbwp.
  iIntros (Hexec Hφ) "Hwp".
  iIntros (M) "HM".
  iApply wp_pure_step_fupd; first done.
  iApply (step_fupdN_wand with "Hwp").
  iIntros "Hwp H".
  iSpecialize ("Hwp" with "H HM"); done.
Qed.

Lemma wbwp_pure_step_later `{!Inhabited (state Λ)} E out e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n (£ n -∗ WBWP e2 @ out; E {{ Φ }}) ⊢ WBWP e1 @ out; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wbwp_pure_step_fupd //. clear Hexec.
  enough (∀ P, ▷^n P -∗ |={E}▷=>^n P) as Hwp by apply Hwp. iIntros (?).
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.
