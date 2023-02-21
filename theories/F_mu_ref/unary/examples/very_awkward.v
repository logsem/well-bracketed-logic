From iris.algebra Require Import auth gmap.
From iris.proofmode Require Import proofmode.
From WBLogrel.program_logic Require Import lifting adequacy.
From WBLogrel.F_mu_ref Require Import wp_rules.
From WBLogrel.F_mu_ref.unary Require Import soundness.
From WBLogrel Require Import oneshot.

Definition very_awkward_packed : expr :=
  Pack
    (Pair
       (LetIn
          (Alloc (#n 0))
          (Lam
             (Seq
                (Store (Var 1) (#n 0))
                (Seq
                   (App (Var 0) Unit)
                   (Seq
                      (Store (Var 1) (#n 1))
                      (Seq
                         (App (Var 0) Unit)
                         (Load (Var 1))))))))
       (Lam (If (BinOp Eq (Var 0) (#n 1)) Unit (App Unit Unit)))).

Lemma very_awkward_typed :
  [] ⊢ₜ very_awkward_packed :
    TExist (TProd (TArrow (TArrow TUnit TUnit) (TVar 0)) (TArrow (TVar 0) TUnit)) → False.
Proof.
  intros; repeat match goal with | H : _ ⊢ₜ _ : _ |- _ => inversion H; simplify_eq; clear H end.
Qed.

Definition very_awkward_self_apply : expr :=
  UnpackIn
    very_awkward_packed
    (LetIn
       (Fst (Var 0))
       (LetIn
          (Snd (Var 1))
          (App (Var 0) (App (Var 1) (Lam (Seq (App (Var 2) (Lam Unit)) Unit)))))).

Section very_awkward.
  Context `{!heapIG Σ, !oneshotG Σ}.

  Lemma very_awkward_sem_typed :
    ⊢ [] ⊨ very_awkward_packed :
      TExist (TProd (TArrow (TArrow TUnit TUnit) (TVar 0)) (TArrow (TVar 0) TUnit)).
  Proof.
    iIntros (? vs) "!# HΔ".
    iDestruct (interp_env_length with "HΔ") as %Hlen; destruct vs; simplify_eq.
    iClear (Hlen) "HΔ". asimpl.
    iApply (wbwp_bind (fill [PairLCtx _; PackCtx])).
    iApply (wbwp_bind (fill [LetInCtx _])).
    iApply wbwp_alloc; first done.
    iNext. iIntros (l) "Hl /=".
    iApply wbwp_pure_step_later; auto.
    iNext; iIntros "_". asimpl.
    iMod new_pending as (γ) "Hpen".
    iApply (wbwp_make_gstack _ _ γ); iIntros (n) "Hfr".
    iDestruct (gstack_frag_exists with "Hfr") as "#Hx".
    iMod (inv_alloc
            (nroot .@ "awk") _
            (∃ γ s, gstack_frag n s ∗ ⌜gtop s = Some γ⌝ ∗
               ((pending γ ∗ l ↦ᵢ #nv 0) ∨ (shot γ ∗ l ↦ᵢ #nv 1)))%I with "[Hpen Hfr Hl]") as "#Hinv".
    { iNext; iExists γ, _. iFrame "Hfr". iSplit; first by rewrite gtop_gsingleton. iLeft; iFrame. }
    iApply wbwp_value.
    simpl.
    iApply wbwp_value.
    iModIntro.
    iExists (PersPred (λ v, ⌜v = (#nv 1)⌝))%I, _; iSplit; first done.
    iExists (LamV _), (LamV _); iSplit; first done.
    iSplit; last first.
    { iIntros "!#" (?) "-> /=".
      iApply wbwp_pure_step_later; auto; iNext; iIntros "_"; asimpl.
      iApply (wbwp_bind (fill [IfCtx _ _])).
      iApply wbwp_pure_step_later; auto; iNext; iIntros "_"; simpl.
      iApply wbwp_value; simpl.
      iApply wbwp_pure_step_later; auto; iNext; iIntros "_"; simpl.
      iApply wbwp_value; done. }
    iIntros "!#" (f) "#Hf /=".
    iApply (wbwp_get_gstack_full n with "[$]"); first done.
    iIntros (s) "Hfl".
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_"; asimpl.
    iApply (wbwp_bind (fill [SeqCtx _])).
    iInv (nroot .@ "awk") as (γ1 s') ">(Hfr & % & Hl)" "Hcl".
    iAssert (∃ v, l ↦ᵢ v ∗ (pending γ1 ∨ shot γ1))%I with "[Hl]" as (?) "[Hl Hps]".
    { iDestruct "Hl" as "[[? ?]|[? ?]]"; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    iMod (new_pending) as (γ2) "Hpen2".
    iMod (gstack_push _ _ _ γ2 with "Hfl Hfr") as "[Hfl Hfr]".
    iApply (wbwp_store with "[$]").
    iNext. iIntros "Hl".
    iMod ("Hcl" with "[Hpen2 Hfr Hl]") as "_".
    { iNext; iExists γ2, _; iFrame "Hfr"; iSplit; first by rewrite gtop_gpush. iLeft; iFrame. }
    iModIntro.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iAssert (|==> shot γ1)%I with "[Hps]" as ">#Hsh".
    { iDestruct "Hps" as "[Hp|Hs]"; last done. iApply shoot; done. }
    iApply (wbwp_bind (fill [SeqCtx _])).
    iApply (wbwp_wand with "[Hfl]").
    { iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hf" $! UnitV); done. }
    iIntros (?) "[Hfl ->] /=".
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iApply (wbwp_bind (fill [SeqCtx _])).
    iInv (nroot .@ "awk") as (γ3 s') ">(Hfr & % & Hl)" "Hcl".
    iAssert (∃ v, l ↦ᵢ v)%I with "[Hl]" as (?) "Hl".
    { iDestruct "Hl" as "[[? ?]|[? ?]]"; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    iMod (gstack_pop with "Hfl Hfr") as "[Hfl Hfr]".
    iApply (wbwp_store with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hfr Hl]") as "_".
    { iNext; iExists γ1, _; iFrame "Hfr". iSplit; first done. iRight; iFrame; done. }
    iModIntro. simpl.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iApply (wbwp_bind (fill [SeqCtx _])).
    iApply (wbwp_wand with "[Hfl]").
    { iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hf" $! UnitV); done. }
    iIntros (?) "[Hfl ->]"; simplify_eq/=.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iInv (nroot .@ "awk") as (γ4 s') ">(Hfr & % & Hl)" "Hcl".
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    simplify_eq.
    iDestruct "Hl" as "[[Hp _]|[_ Hl]]".
    { iExFalso; iApply shot_not_pending; done. }
    iApply (wbwp_load with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hfr Hl]") as "_".
    { iNext; iExists _, _; iFrame. iSplit; first done. iRight; iFrame; done. }
    iModIntro.
    iFrame; done.
  Qed.

  Lemma very_awkward_self_apply_sem_typed :
    ⊢ [] ⊨ very_awkward_self_apply : TUnit.
  Proof.
    iIntros (? vs) "!# HΔ".
    iDestruct (interp_env_length with "HΔ") as %Hlen; destruct vs; simplify_eq.
    iClear (Hlen) "HΔ". asimpl.
    iApply (wbwp_bind (fill [UnpackInCtx _])).
    iApply wbwp_wand.
    { iApply (very_awkward_sem_typed $! [] []); iApply interp_env_nil. }
    simpl.
    iIntros (v) "#Hv".
    iDestruct "Hv" as (τi w) "[-> Hw]".
    iDestruct "Hw" as (f test) "(-> & #Hf & #Htest) /=".
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_". asimpl.
    iApply (wbwp_bind (fill [LetInCtx _])).
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iApply wbwp_value; simpl.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_". asimpl.
    iApply (wbwp_bind (fill [LetInCtx _])).
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iApply wbwp_value; simpl.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_". asimpl.
    iApply (wbwp_bind (fill [AppRCtx _])).
    iApply wbwp_wand.
    { iApply ("Hf" $! (LamV _)).
      iIntros "!#" (?) "-> /=".
      iApply wbwp_pure_step_later; auto. iNext; iIntros "_". asimpl.
      iApply (wbwp_bind (fill [SeqCtx _])).
      iApply wbwp_wand.
      - iApply ("Hf" $! (LamV _)).
        iIntros "!#" (?) "-> /=".
        iApply wbwp_pure_step_later; auto. iNext; iIntros "_". simpl.
        iApply wbwp_value; done.
      - iIntros (w) "Hτi /=".
        iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
        iApply wbwp_value; done. }
    iIntros (w) "#Hτi /=".
    iApply ("Htest" with "[$]").
  Qed.

End very_awkward.

Theorem very_awkward_self_apply_safe thp σ σ' e' :
  rtc erased_step ([very_awkward_self_apply], σ) (thp, σ') → e' ∈ thp →
  not_stuck e' σ'.
Proof.
  set (Σ := #[invΣ ; gen_heapΣ loc val ; gstacksΣ; oneshotΣ]).
  set (HG := soundness_unary_preIG Σ _ _ _).
  apply (soundness Σ _ TUnit).
  intros; apply very_awkward_self_apply_sem_typed.
Qed.
