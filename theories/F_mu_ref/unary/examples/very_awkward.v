From iris.algebra Require Import auth gmap.
From iris.staging.algebra Require Import monotone.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting adequacy.
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
  Context `{heapIG Σ, ghost_regG Σ}.

  Lemma very_awkward_sem_typed `{!inG Σ (authUR (mraUR rel))} :
    ⊢ [] ⊨ very_awkward_packed :
      TExist (TProd (TArrow (TArrow TUnit TUnit) (TVar 0)) (TArrow (TVar 0) TUnit)).
  Proof.
    iIntros (? vs) "!# HΔ".
    iDestruct (interp_env_length with "HΔ") as %Hlen; destruct vs; simplify_eq.
    iClear (Hlen) "HΔ". asimpl.
    iIntros (M) "Hreg /=".
    iApply (wp_bind (fill [PairLCtx _; PackCtx])).
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_alloc; first done.
    iNext. iIntros (l) "Hl /=".
    iApply wp_pure_step_later; auto.
    iNext. asimpl.
    iMod (exactly_alloc false) as (γ) "Hex".
    iMod (res_name_alloc _ γ with "Hreg") as (id HidM) "[Hreg Hid]".
    rewrite insert_union_singleton_r; last first.
    { rewrite -(not_elem_of_dom (D := gset ghost_id)); done. }
    iMod (inv_alloc
            (nroot .@ "awk") _
            (∃ γ b, named_ghost id 1 γ ∗ exactly γ b ∗ if b then l ↦ᵢ (#nv 1) else l ↦ᵢ (#nv 0))%I
            with "[Hex Hid Hl]") as "#Hinv".
    { iNext; iExists γ, false; iFrame. }
    iApply wp_value.
    simpl.
    iApply wp_value.
    iExists _; iFrame; iSplit; last first.
    { iPureIntro. apply map_union_subseteq_l. }
    iModIntro.
    iExists (PersPred (λ v, ⌜v = (#nv 1)⌝))%I, _; iSplit; first done.
    iExists (LamV _), (LamV _); iSplit; first done.
    clear M HidM.
    iSplit; last first.
    { iIntros "!#" (M ?) "Hreg -> /=".
      iApply wp_pure_step_later; auto; iNext; asimpl.
      iApply (wp_bind (fill [IfCtx _ _])).
      iApply wp_pure_step_later; auto; iNext; simpl.
      iApply wp_value; simpl.
      iApply wp_pure_step_later; auto; iNext; simpl.
      iApply wp_value; simpl.
      iExists _; iFrame; done. }
    iIntros "!#" (M f) "Hreg #Hf /=".
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [SeqCtx _])).
    iInv (nroot .@ "awk") as (γ1 b) "(>Hid & >Hex1 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ᵢ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b; iExists _; iFrame. }
    iDestruct (named_ghost_agree with "Hreg Hid") as %Hids1.
    iMod (exactly_alloc false) as (γ2) "Hex2".
    iMod (named_ghost_update _ _ _ γ2 with "Hreg Hid") as "[Hreg Hid]".
    iApply (wp_store with "[$]").
    iNext. iIntros "Hl".
    iMod ("Hcl" with "[Hex2 Hid Hl]") as "_".
    { iNext; iExists γ2, false; iFrame. }
    iModIntro.
    iApply wp_pure_step_later; auto. iNext.
    iMod (exactly_update _ _ true with "Hex1") as "[Hex1 Hat1]"; first done.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_wand with "[Hreg]").
    { iApply ("Hf" $! _ UnitV with "[$] [//]"). }
    iIntros (?); iDestruct 1 as (N) "(-> & %HN & Hreg)"; simplify_eq/=.
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [SeqCtx _])).
    iInv (nroot .@ "awk") as (γ3 b2) "(>Hid & >Hex2 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ᵢ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b2; iExists _; iFrame. }
    iMod (named_ghost_update _ _ _ γ1 with "Hreg Hid") as "[Hreg Hid]".
    iApply (wp_store with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hex1 Hid Hl]") as "_".
    { iNext; iExists γ1, true; iFrame. }
    iModIntro. simpl.
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_wand with "[Hreg]").
    { iApply ("Hf" $! _ UnitV with "[$] [//]"). }
    iIntros (?); iDestruct 1 as (N') "(-> & %HN' & Hreg)"; simplify_eq/=.
    iApply wp_pure_step_later; auto. iNext.
    iInv (nroot .@ "awk") as (γ4 b3) "(>Hid & >Hex1 & Hl)" "Hcl".
    iDestruct (named_ghost_agree with "Hreg Hid") as %Hids2.
    assert (N' !! id = Some γ1) as Heq.
    { eapply lookup_weaken; last by apply HN'.
      rewrite lookup_insert; done. }
    simplify_eq.
    iDestruct (exatly_atleast_rel with "Hex1 Hat1") as %?.
    destruct b3; last done.
    iApply (wp_load with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hex1 Hid Hl]") as "_".
    { iNext; iExists _, true; iFrame. }
    iModIntro.
    iExists _; iFrame.
    iSplit; first done.
    iPureIntro.
    etrans; last apply HN'.
    etrans; last apply insert_mono, HN.
    rewrite insert_insert insert_id; auto.
  Qed.

  Lemma very_awkward_self_apply_sem_typed `{!inG Σ (authUR (mraUR rel))} :
    ⊢ [] ⊨ very_awkward_self_apply : TUnit.
  Proof.
    iIntros (? vs) "!# HΔ".
    iDestruct (interp_env_length with "HΔ") as %Hlen; destruct vs; simplify_eq.
    iClear (Hlen) "HΔ". asimpl.
    iIntros (M) "Hreg /=".
    iApply (wp_bind (fill [UnpackInCtx _])).
    iApply (wp_wand with "[Hreg]").
    { iApply (very_awkward_sem_typed $! [] []); [iApply interp_env_nil|]; done. }
    simpl.
    iIntros (v). iDestruct 1 as (N) "(#Hv & %HN & Hreg)".
    iDestruct "Hv" as (τi w) "[-> Hw]".
    iDestruct "Hw" as (f test) "(-> & #Hf & #Htest) /=".
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_pure_step_later; auto. iNext.
    iApply wp_value; simpl.
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_pure_step_later; auto. iNext.
    iApply wp_value; simpl.
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [AppRCtx _])).
    iApply (wp_wand with "[Hreg]").
    { iApply ("Hf" $! _ (LamV _) with "[$]").
      iIntros "!#" (N' ?) "Hreg -> /=".
      iApply wp_pure_step_later; auto. iNext. asimpl.
      iApply (wp_bind (fill [SeqCtx _])).
      iApply (wp_wand with "[Hreg]").
      - iApply ("Hf" $! _ (LamV _) with "[$]").
        iIntros "!#" (N'' ?) "Hreg -> /=".
        iApply wp_pure_step_later; auto. iNext. simpl.
        iApply wp_value; iExists _; iFrame; done.
      - iIntros (w) "/=". iDestruct 1 as (N'') "(#Hτi & %HN'' & Hreg)".
        iApply wp_pure_step_later; auto. iNext.
        iApply wp_value; iExists _; iFrame; done. }
    iIntros (w) "/=". iDestruct 1 as (N') "(#Hτi & %HN' & Hreg)".
    iApply (wp_wand with "[Hreg]").
    { iApply ("Htest" with "[$] [//]"). }
    iIntros (w') "/=". iDestruct 1 as (N'') "(-> & %HN'' & Hreg)".
    iExists _; iFrame. iSplit; first done.
    iPureIntro.
    etrans; last done.
    etrans; done.
  Qed.

End very_awkward.



Theorem very_awkward_self_apply_safe thp σ σ' e' :
  rtc erased_step ([very_awkward_self_apply], σ) (thp, σ') → e' ∈ thp →
  not_stuck e' σ'.
Proof.
  set (Σ := #[invΣ ; gen_heapΣ loc val ; ghost_regΣ; relΣ]).
  set (HG := soundness_unary_preIG Σ _ _ _).
  apply (soundness Σ _ TUnit).
  intros; apply very_awkward_self_apply_sem_typed.
Qed.
