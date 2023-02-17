From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From WBLogrel.F_mu_ref Require Import rules.
From WBLogrel.F_mu_ref.binary Require Import soundness rules.
From iris.prelude Require Import options.

Definition fact : expr :=
  Rec (If (BinOp Eq (Var 1) (#n 0))
          (#n 1)
          (BinOp Mult (Var 1) (App (Var 0) (BinOp Sub (Var 1) (#n 1))))).

Definition factV : val :=
  RecV (If (BinOp Eq (Var 1) (#n 0))
          (#n 1)
          (BinOp Mult (Var 1) (App (Var 0) (BinOp Sub (Var 1) (#n 1))))).

Lemma fact_typed : [] ⊢ₜ fact : TArrow TNat TNat.
Proof. repeat econstructor. Qed.

Lemma fact_unfold :
  fact = Rec (If (BinOp Eq (Var 1) (#n 0))
                 (#n 1)
                 (BinOp Mult (Var 1) (App (Var 0) (BinOp Sub (Var 1) (#n 1))))).
Proof. done. Qed.

Global Typeclasses Opaque fact.
Global Opaque fact.

Global Typeclasses Opaque factV.
Global Opaque factV.

Definition fact_acc_body : expr :=
  Rec (Lam
         (If (BinOp Eq (Var 2) (#n 0))
             (Var 0)
             (LetIn
                (BinOp Mult (Var 2) (Var 0))
                (LetIn
                   (BinOp Sub (Var 3) (#n 1))
                   (App (App (Var 3) (Var 0)) (Var 1))
                )
             )
         )
      ).

Lemma fact_acc_body_typed : [] ⊢ₜ fact_acc_body : TArrow TNat (TArrow TNat TNat).
Proof. repeat econstructor. Qed.

Lemma fact_acc_body_subst f : fact_acc_body.[f] = fact_acc_body.
Proof. by asimpl. Qed.

Global Hint Rewrite fact_acc_body_subst : autosubst.

Lemma fact_acc_body_unfold :
  fact_acc_body =
  Rec (Lam
         (If (BinOp Eq (Var 2) (#n 0))
             (Var 0)
             (LetIn
                (BinOp Mult (Var 2) (Var 0))
                (LetIn
                   (BinOp Sub (Var 3) (#n 1))
                   (App (App (Var 3) (Var 0)) (Var 1))
                )
             )
         )
      ).
Proof. trivial. Qed.

Global Typeclasses Opaque fact_acc_body.
Global Opaque fact_acc_body.

Definition fact_acc : expr :=
  Lam (App (App fact_acc_body (Var 0)) (#n 1)).

Definition fact_accV : val :=
  LamV (App (App fact_acc_body (Var 0)) (#n 1)).

Lemma fact_acc_unfold : fact_acc = Lam (App (App fact_acc_body (Var 0)) (#n 1)).
Proof. done. Qed.

Lemma fact_acc_subst f : fact_acc.[f] = fact_acc.
Proof. by asimpl. Qed.

Lemma fact_acc_typed : [] ⊢ₜ fact_acc : TArrow TNat TNat.
Proof.
  repeat econstructor.
  apply (closed_context_weakening [_] []); eauto.
  apply fact_acc_body_typed.
Qed.

Global Typeclasses Opaque fact_acc.
Global Opaque fact_acc.

Global Typeclasses Opaque fact_accV.
Global Opaque fact_accV.

Section fact_equiv.
  Context `{heapIG Σ, cfgSG Σ, ghost_regG Σ}.

  Lemma fact_fact_acc_refinement :
    ⊢ [] ⊨ fact ≤log≤ fact_acc : (TArrow TNat TNat).
  Proof.
    iIntros (? vs) "!# [#HE HΔ]".
    iDestruct (interp_env_length with "HΔ") as %?; destruct vs; simplify_eq.
    iClear "HΔ". asimpl.
    change fact_acc with (of_val fact_accV).
    change fact with (of_val factV).
    iApply bin_val_rel_bin_expr_rel.
    iIntros ([] (n&?&?)) "!#"; simplify_eq/=.
    change (of_val fact_accV) with fact_acc.
    change (of_val factV) with fact.
    rewrite fact_acc_unfold.
    iIntros (j K) "Hj"; simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
    asimpl.
    iApply (wbwp_mono _ _ _ (λ v, ∃ m, j ⤇ fill K (#n (1 * m)) ∗ ⌜v = #nv m⌝))%I.
    { iIntros (?). iDestruct 1 as (m) "[? %]"; subst.
      iExists (#nv _); iFrame; eauto. }
    generalize 1 as l => l.
    iInduction n as [|n] "IH" forall (l).
    - rewrite fact_unfold.
      iApply wbwp_pure_step_later; auto.
      rewrite -fact_unfold.
      iNext; iIntros "_"; simpl; asimpl.
      rewrite fact_acc_body_unfold.
      iMod (do_step_pure _ _ (AppLCtx _ :: _) with "[$Hj]") as "Hj"; auto.
      rewrite -fact_acc_body_unfold.
      simpl; asimpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      iApply (wbwp_bind (fill [IfCtx _ _])).
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl.
      iApply wbwp_value. simpl.
      iMod (do_step_pure _ _ (IfCtx _ _ :: _) with "[$Hj]") as "Hj"; auto.
      simpl.
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      iApply wbwp_value.
      iExists 1. replace (l * 1) with l by lia.
      iFrame; done.
    - rewrite fact_unfold.
      iApply wbwp_pure_step_later; auto.
      rewrite -fact_unfold.
      iNext; iIntros "_"; simpl; asimpl.
      rewrite fact_acc_body_unfold.
      iMod (do_step_pure _ _ (AppLCtx _ :: _) with "[$Hj]") as "Hj"; auto.
      rewrite -fact_acc_body_unfold.
      simpl; asimpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      iApply (wbwp_bind (fill [IfCtx _ _])).
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl.
      iApply wbwp_value. simpl.
      iMod (do_step_pure _ _ (IfCtx _ _ :: _) with "[$Hj]") as "Hj"; auto.
      simpl.
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      iAsimpl.
      iApply (wbwp_bind (fill [BinOpRCtx _ (#nv _)])).
      change fact with (of_val factV).
      iApply (wbwp_bind (fill [AppRCtx _])).
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl; iApply wbwp_value; simpl.
      iMod (do_step_pure _ _ (LetInCtx _ :: _) with "[$Hj]") as "Hj"; auto.
      simpl.
      change (of_val factV) with fact.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      iAsimpl.
      iMod (do_step_pure _ _ (LetInCtx _ :: _) with "[$Hj]") as "Hj"; auto.
      simpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      asimpl.
      replace (n -0) with n by lia.
      iApply wbwp_wand_r; iSplitL; first by iApply ("IH" with "[$]"); eauto.
      iIntros (v). iDestruct 1 as (m) "[H %]"; simplify_eq.
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl; iApply wbwp_value.
      iExists ((S n) * m); simpl.
      replace (l * (m + n * m)) with ((l + n * l) * m)
        by lia.
      iFrame; auto.
  Qed.

  Lemma fact_acc_fact_refinement :
    ⊢ [] ⊨ fact_acc ≤log≤ fact : (TArrow TNat TNat).
  Proof.
    iIntros (? vs) "!# [#HE HΔ]".
    iDestruct (interp_env_length with "HΔ") as %?; destruct vs; simplify_eq.
    iClear "HΔ". asimpl.
    change fact_acc with (of_val fact_accV).
    change fact with (of_val factV).
    iApply bin_val_rel_bin_expr_rel.
    iIntros ([] (n&?&?)) "!#"; simplify_eq/=.
    change (of_val fact_accV) with fact_acc.
    change (of_val factV) with fact.
    rewrite fact_acc_unfold.
    iIntros (j K) "Hj"; simpl.
    iApply wbwp_pure_step_later; auto.
    iNext; iIntros "_"; iAsimpl.
    iApply (wbwp_mono _ _ _ (λ v, ∃ m, j ⤇ fill K (#n m) ∗ ⌜v = #nv (1 * m)⌝))%I.
    { iIntros (?). iDestruct 1 as (m) "[? %]"; simplify_eq.
      replace (1 * m) with m by lia.
      iExists (#nv _); iFrame; eauto. }
    generalize 1 as l => l.
    iInduction n as [|n] "IH" forall (K l).
    - rewrite fact_acc_body_unfold.
      iApply (wbwp_bind (fill [AppLCtx _])).
      iApply wbwp_pure_step_later; auto.
      rewrite -fact_acc_body_unfold.
      iNext; iIntros "_"; simpl; asimpl.
      iApply wbwp_value; simpl.
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl; asimpl.
      rewrite fact_unfold.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      simpl; iAsimpl.
      rewrite -fact_unfold.
      iMod (do_step_pure _ _ (IfCtx _ _ :: _) with "[$Hj]") as "Hj"; auto.
      iApply (wbwp_bind (fill [IfCtx _ _])).
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl.
      iApply wbwp_value. simpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl.
      iApply wbwp_value.
      iExists 1.
      replace (l * 1) with l by lia; iFrame; auto.
    - rewrite {2}fact_acc_body_unfold.
      iApply (wbwp_bind (fill [AppLCtx _])).
      iApply wbwp_pure_step_later; auto.
      rewrite -fact_acc_body_unfold.
      iNext; iIntros "_"; simpl; asimpl.
      iApply wbwp_value; simpl.
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl; asimpl.
      rewrite fact_unfold.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      rewrite -fact_unfold.
      asimpl.
      simpl.
      iApply (wbwp_bind (fill [IfCtx _ _])).
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl.
      iApply wbwp_value. simpl.
      iMod (do_step_pure _ _ (IfCtx _ _ :: _) with "[$Hj]") as "Hj"; auto.
      simpl.
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      change fact with (of_val factV).
      iMod (do_step_pure _ _ (AppRCtx _:: BinOpRCtx _ (#nv _) :: _)
             with "[$Hj]") as "Hj"; eauto.
      simpl.
      change (of_val factV) with fact.
      iApply (wbwp_bind (fill [LetInCtx _])).
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl; iApply wbwp_value; simpl.
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl. asimpl.
      iApply (wbwp_bind (fill [LetInCtx _])).
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl; iApply wbwp_value; simpl.
      iApply wbwp_pure_step_later; auto.
      iNext; iIntros "_"; simpl. asimpl.
      replace (n -0) with n by lia.
      iApply wbwp_fupd.
      iApply wbwp_wand_r; iSplitL;
        first by iApply ("IH" $! (BinOpRCtx _ (#nv _) :: K) with "[$]"); eauto.
      iIntros (v). iDestruct 1 as (m) "[Hj %]"; simplify_eq.
      simpl.
      iMod (do_step_pure with "[$Hj]") as "Hj"; auto.
      simpl.
      iModIntro.
      iExists (S n * m).
      iFrame.
      eauto with lia.
  Qed.

End fact_equiv.

Theorem fact_ctx_equiv :
  [] ⊨ fact ≤ctx≤ fact_acc : (TArrow TNat TNat) ∧
  [] ⊨ fact_acc ≤ctx≤ fact : (TArrow TNat TNat).
Proof.
  set (Σ := #[invΣ ; gen_heapΣ loc val; soundness_binaryΣ; gstacksΣ]).
  set (HG := soundness.soundness_unary_preIG Σ _ _ _).
  split.
  - eapply (binary_soundness Σ); auto using fact_acc_typed, fact_typed.
    intros; apply fact_fact_acc_refinement.
  -  eapply (binary_soundness Σ); auto using fact_acc_typed, fact_typed.
    intros; apply fact_acc_fact_refinement.
Qed.
