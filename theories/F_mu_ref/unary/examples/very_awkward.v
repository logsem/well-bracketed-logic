From iris.algebra Require Import auth gmap.
From iris.unstable.algebra Require Import monotone.
From iris.proofmode Require Import proofmode.
From WBLogrel.program_logic Require Import lifting adequacy.
From WBLogrel.F_mu_ref Require Import wp_rules.
From WBLogrel.F_mu_ref.unary Require Import soundness.
From iris.prelude Require Import options.

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

Definition rel : relation bool :=
  λ b1 b2,
  match b2 with
  | true => True
  | false =>
    match b1 with
    | true => False
    | false => True
    end
  end.

Global Instance rel_PreOrder : PreOrder rel.
Proof. split; repeat intros []; done. Qed.

Section rel.
  Context `{!inG Σ (authUR (mraUR rel))}.

  Definition exactly (γ : gname) (b : bool) := own γ (● principal rel b).

  Definition atleast (γ : gname) (b : bool) := own γ (◯ principal rel b).

  Lemma exactly_update γ b1 b2 : rel b1 b2 → exactly γ b1 ==∗ exactly γ b2 ∗ atleast γ b2.
  Proof.
    intros.
    rewrite -own_op; apply own_update.
    apply auth_update_alloc.
    apply mra_local_update_grow; done.
  Qed.

  Lemma exactly_alloc b : ⊢ |==> ∃ γ, exactly γ b.
  Proof. apply own_alloc; apply auth_auth_valid; done. Qed.

  Lemma exatly_atleast_rel γ b1 b2 : exactly γ b1 -∗ atleast γ b2 -∗ ⌜rel b2 b1⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hincl _]%auth_both_valid_discrete.
    revert Hincl; rewrite principal_included; done.
  Qed.

End rel.

Definition relΣ := #[GFunctor (authUR (mraUR rel))].

Global Instance sub_relΣ_inG Σ : subG relΣ Σ → inG Σ (authUR (mraUR rel)).
Proof. solve_inG. Qed.

Section very_awkward.
  Context `{!heapIG Σ, !inG Σ (authUR (mraUR rel))}.

  Lemma very_awkward_sem_typed `{!inG Σ (authUR (mraUR rel))} :
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
    iMod (exactly_alloc false) as (γ) "Hex".
    iApply (wbwp_make_gstack _ _ γ); iIntros (n) "Hfrg".
    iDestruct (gstack_frag_exists with "Hfrg") as "#Hx".
    iMod (inv_alloc
            (nroot .@ "awk") _
            (∃ γ s b, gstack_frag n s ∗ ⌜gtop s = Some γ⌝ ∗ exactly γ b ∗
               if b then l ↦ᵢ (#nv 1) else l ↦ᵢ (#nv 0))%I with "[Hex Hfrg Hl]") as "#Hinv".
    { iNext; iExists γ, _, false; iFrame; rewrite gtop_gsingleton; done. }
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
    iInv (nroot .@ "awk") as (γ1 s' b) "(>Hfr & >% & >Hex1 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ᵢ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    iMod (exactly_alloc false) as (γ2) "Hex2".
    iMod (gstack_push _ _ _ γ2 with "Hfl Hfr") as "[Hfl Hfr]".
    iApply (wbwp_store with "[$]").
    iNext. iIntros "Hl".
    iMod ("Hcl" with "[Hex2 Hfr Hl]") as "_".
    { iNext; iExists γ2, _, false; iFrame; rewrite gtop_gpush; done. }
    iModIntro.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iMod (exactly_update _ _ true with "Hex1") as "[Hex1 Hat1]"; first done.
    iApply (wbwp_bind (fill [SeqCtx _])).
    iApply (wbwp_wand with "[Hfl]").
    { iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hf" $! UnitV); done. }
    iIntros (?) "[Hfl ->] /=".
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iApply (wbwp_bind (fill [SeqCtx _])).
    iInv (nroot .@ "awk") as (γ3 s' b2) "(>Hfr & >%Hγ3 & >Hex2 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ᵢ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b2; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    iMod (gstack_pop with "Hfl Hfr") as "[Hfl Hfr]".
    iApply (wbwp_store with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hex1 Hfr Hl]") as "_".
    { iNext; iExists γ1, _, true; iFrame; done. }
    iModIntro. simpl.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iApply (wbwp_bind (fill [SeqCtx _])).
    iApply (wbwp_wand with "[Hfl]").
    { iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hf" $! UnitV); done. }
    iIntros (?) "[Hfl ->]"; simplify_eq/=.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iInv (nroot .@ "awk") as (γ4 ? b3) "(>Hfr & >% & >Hex1 & Hl)" "Hcl".
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    simplify_eq.
    iDestruct (exatly_atleast_rel with "Hex1 Hat1") as %?.
    destruct b3; last done.
    iApply (wbwp_load with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hex1 Hfr Hl]") as "_".
    { iNext; iExists _, _, true; iFrame; done. }
    iModIntro.
    iFrame; done.
  Qed.

  Lemma very_awkward_self_apply_sem_typed `{!inG Σ (authUR (mraUR rel))} :
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
  set (Σ := #[invΣ ; gen_heapΣ loc val ; gstacksΣ; relΣ]).
  set (HG := soundness_unary_preIG Σ _ _ _).
  apply (soundness Σ _ TUnit).
  intros; apply very_awkward_self_apply_sem_typed.
Qed.
