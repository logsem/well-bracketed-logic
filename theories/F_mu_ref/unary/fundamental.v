From iris.base_logic Require Import invariants.
From iris.program_logic Require Import lifting.
From iris.proofmode Require Import proofmode.
From WBLogrel.F_mu_ref.unary Require Export logrel.
From WBLogrel.F_mu_ref Require Export wp_rules.
From iris.prelude Require Import options.

Definition log_typed `{heapIG Σ, ghost_regG Σ} (Γ : list type) (e : expr) (τ : type) : iProp Σ :=
  □ ∀ Δ vs, ⟦ Γ ⟧* Δ vs -∗ ⟦ τ ⟧ₑ Δ e.[env_subst vs].
Notation "Γ ⊨ e : τ" := (log_typed Γ e τ) (at level 74, e, τ at next level).

Section typed_interp.
  Context `{heapIG Σ, ghost_regG Σ}.
  Notation D := (persistent_predO val (iPropI Σ)).

  Local Tactic Notation "smart_wp_bind"
        uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (wp_bind (fill [ctx]));
    iApply (wp_wand with "[-]"); [iApply Hp; trivial|]; cbn;
    iIntros (v) Hv.

  Lemma sem_typed_var Γ x τ :
    Γ !! x = Some τ → ⊢ Γ ⊨ Var x : τ.
  Proof.
    iIntros (? Δ vs) "!# #HΓ"; simpl.
    iDestruct (interp_env_Some_l with "HΓ") as (v) "[% ?]"; first done.
    erewrite env_subst_lookup; eauto.
    iIntros (?) "?"; iApply wp_value; iExists _; iFrame; iSplit; done.
  Qed.

  Lemma sem_typed_unit Γ : ⊢ Γ ⊨ Unit : TUnit.
  Proof.
    iIntros (Δ vs) "!# #HΓ".
    iIntros (?) "?"; iApply wp_value; iExists _; iFrame; iSplit; done.
  Qed.

  Lemma sem_typed_nat Γ n : ⊢ Γ ⊨ #n n : TNat.
  Proof.
    iIntros (Δ vs) "!# #HΓ /=".
    iIntros (?) "?"; iApply wp_value; iExists _; iFrame; iSplit; eauto.
  Qed.

  Lemma sem_typed_bool Γ b : ⊢ Γ ⊨ #♭ b : TBool.
  Proof.
    iIntros (Δ vs) "!# #HΓ /=".
    iIntros (?) "?"; iApply wp_value; iExists _; iFrame; iSplit; eauto.
  Qed.

  Lemma sem_typed_nat_binop Γ op e1 e2 :
    Γ ⊨ e1 : TNat -∗ Γ ⊨ e2 : TNat -∗ Γ ⊨ BinOp op e1 e2 : binop_res_type op.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ /=".
    iIntros (?) "?".
    smart_wp_bind (BinOpLCtx _ e2.[env_subst vs]) v "Hv" "IH1".
    iDestruct "Hv" as (N1 [] ?) "?".
    smart_wp_bind (BinOpRCtx _ v) v' "Hv'" "IH2".
    iDestruct "Hv'" as (N2 [] ?) "?".
    simplify_eq/=.
    iApply wp_pure_step_later; auto. iNext. iApply wp_value.
    iExists _; iSplit; last (iSplit; last (by iFrame); iPureIntro; etrans; done).
    destruct op; simpl; try destruct eq_nat_dec;
      try destruct le_dec; try destruct lt_dec; eauto 10.
  Qed.

  Lemma sem_typed_pair Γ e1 e2 τ1 τ2 :
    Γ ⊨ e1 : τ1 -∗ Γ ⊨ e2 : τ2 -∗ Γ ⊨ Pair e1 e2 : TProd τ1 τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    smart_wp_bind (PairLCtx e2.[env_subst vs]) v "Hv" "IH1".
    iDestruct "Hv" as (N1) "(#?&%&?)".
    smart_wp_bind (PairRCtx v) v' "Hv'" "IH2".
    iDestruct "Hv'" as (N2) "(#?&%&?)".
    iApply wp_value.
    iExists _; iSplit; last (iSplit; last (by iFrame); iPureIntro; etrans; done).
    eauto.
  Qed.

  Lemma sem_typed_fst Γ e τ1 τ2 :
        Γ ⊨ e : TProd τ1 τ2 -∗ Γ ⊨ Fst e : τ1.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    smart_wp_bind (FstCtx) v "Hv" "IH"; cbn.
    iDestruct "Hv" as (N1) "(#Hv&%&?)".
    iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
    simpl.
    iApply wp_pure_step_later; auto.
    iApply wp_value.
    iExists _; iSplit; last (iSplit; last (by iFrame); iPureIntro; etrans; done).
    done.
  Qed.

  Lemma sem_typed_snd Γ e τ1 τ2 :
    Γ ⊨ e : TProd τ1 τ2 -∗ Γ ⊨ Snd e : τ2.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    smart_wp_bind (SndCtx) v "Hv" "IH"; cbn.
    iDestruct "Hv" as (N1) "(#Hv&%&?)".
    iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
    simpl.
    iApply wp_pure_step_later; auto.
    iApply wp_value.
    iExists _; iSplit; last (iSplit; last (by iFrame); iPureIntro; etrans; done).
    done.
  Qed.

  Lemma sem_typed_injl Γ e τ1 τ2 : Γ ⊨ e : τ1 -∗ Γ ⊨ InjL e : (TSum τ1 τ2).
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    smart_wp_bind (InjLCtx) v "Hv" "IH"; cbn.
    iDestruct "Hv" as (N1) "(#Hv&%&?)".
    iApply wp_value.
    iExists _; iSplit; last (iSplit; last (by iFrame); iPureIntro; etrans; done).
    eauto.
  Qed.

  Lemma sem_typed_injr Γ e τ1 τ2 : Γ ⊨ e : τ2 -∗ Γ ⊨ InjR e : TSum τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    smart_wp_bind (InjRCtx) v "Hv" "IH"; cbn.
    iDestruct "Hv" as (N1) "(#Hv&%&?)".
    iApply wp_value.
    iExists _; iSplit; last (iSplit; last (by iFrame); iPureIntro; etrans; done).
    eauto.
  Qed.

  Lemma sem_typed_case Γ e0 e1 e2 τ1 τ2 τ3 :
    Γ ⊨ e0: TSum τ1 τ2 -∗
    τ1 :: Γ ⊨ e1 : τ3 -∗
    τ2 :: Γ ⊨ e2 : τ3 -∗
    Γ ⊨ Case e0 e1 e2 : τ3.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    smart_wp_bind (CaseCtx _ _) v "Hv" "IH1"; cbn.
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    iDestruct (interp_env_length with "HΓ") as %?.
    iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[% Hw]"; simplify_eq/=.
    + iApply wp_pure_step_later; first done. asimpl. iNext.
      iApply (wp_wand with "[Hreg]"); first
        iApply ("IH2" $! Δ (w :: vs) with "[] Hreg"); first by iApply interp_env_cons; auto.
      iIntros (v). iDestruct 1 as (N) "(?&%&?)".
      iExists _; iFrame; iPureIntro.
      etrans; done.
    + iApply wp_pure_step_later; first done. asimpl. iNext.
      iApply (wp_wand with "[Hreg]"); first
        iApply ("IH3" $! Δ (w :: vs) with "[] Hreg"); first by iApply interp_env_cons; auto.
      iIntros (v). iDestruct 1 as (N) "(?&%&?)".
      iExists _; iFrame; iPureIntro.
      etrans; done.
  Qed.

  Lemma sem_typed_if Γ e0 e1 e2 τ :
    Γ ⊨ e0 : TBool -∗ Γ ⊨ e1 : τ -∗ Γ ⊨ e2 : τ -∗ Γ ⊨ If e0 e1 e2 : τ.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    smart_wp_bind (IfCtx _ _) v "Hv" "IH1"; cbn.
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    iDestruct "Hv" as ([]) "%"; subst; simpl;
      [iApply wp_pure_step_later .. ]; auto; iNext.
    - iApply (wp_wand with "[Hreg]"); first
        iApply ("IH2" with "[] Hreg"); first done.
      iIntros (v). iDestruct 1 as (N) "(?&%&?)".
      iExists _; iFrame; iPureIntro.
      etrans; done.
    - iApply (wp_wand with "[Hreg]"); first
        iApply ("IH3" with "[] Hreg"); first done.
      iIntros (v). iDestruct 1 as (N) "(?&%&?)".
      iExists _; iFrame; iPureIntro.
      etrans; done.
  Qed.

  Lemma sem_typed_rec Γ e τ1 τ2 :
    TArrow τ1 τ2 :: τ1 :: Γ ⊨ e : τ2 -∗ Γ ⊨ Rec e : TArrow τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    iApply wp_value. simpl.
    iExists _; iFrame; iSplit; last done.
    iModIntro. iLöb as "IHL". iIntros (M' w) "Hreg #Hw".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    asimpl. change (Rec _) with (of_val (RecV e.[upn 2 (env_subst vs)])) at 2.
    iApply ("IH" $! Δ (_ :: w :: vs)); last done.
    iApply interp_env_cons; iSplit; [|iApply interp_env_cons]; auto.
  Qed.

  Lemma sem_typed_lam Γ e τ1 τ2 : τ1 :: Γ ⊨ e : τ2 -∗ Γ ⊨ Lam e : TArrow τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    iApply wp_value. simpl.
    iExists _; iFrame; iSplit; last done.
    iModIntro. iIntros (M' w) "Hreg #Hw".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    asimpl.
    iApply ("IH" $! Δ (w :: vs)); auto.
    iApply interp_env_cons; iSplit; auto.
  Qed.

  Lemma sem_typed_letin Γ e1 e2 τ1 τ2 :
    Γ ⊨ e1 : τ1 -∗ τ1 :: Γ ⊨ e2 : τ2 -∗ Γ ⊨ LetIn e1 e2: τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    smart_wp_bind (LetInCtx _) v "Hv" "IH1"; cbn.
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    asimpl.
    iApply (wp_wand with "[Hreg]");
      first iApply ("IH2" $! Δ (v :: vs) with "[] Hreg");
      first by iApply interp_env_cons; iSplit; eauto.
    iIntros (w). iDestruct 1 as (N2) "(?&%&?)".
    iExists _; iFrame.
    iPureIntro; etrans; done.
  Qed.

  Lemma sem_typed_seq Γ e1 e2 τ1 τ2 :
    Γ ⊨ e1 : τ1 -∗ Γ ⊨ e2 : τ2 -∗ Γ ⊨ Seq e1 e2 : τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    smart_wp_bind (SeqCtx _) v "Hv" "IH1"; cbn.
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    iApply (wp_wand with "[Hreg]"); first
      iApply ("IH2" with "[] Hreg"); first done.
    iIntros (w). iDestruct 1 as (N2) "(?&%&?)".
    iExists _; iFrame.
    iPureIntro; etrans; done.
  Qed.

  Lemma sem_typed_app Γ e1 e2 τ1 τ2 :
      Γ ⊨ e1 : TArrow τ1 τ2 -∗ Γ ⊨ e2 : τ1 -∗ Γ ⊨ App e1 e2 :  τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ"; simpl.
    iIntros (?) "?".
    smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "Hv" "IH1".
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    smart_wp_bind (AppRCtx v) w "Hw" "IH2".
    iDestruct "Hw" as (N2) "(#Hw&%&Hreg)".
    iApply (wp_wand with "[Hreg]"); first
      iApply ("Hv" with "Hreg"); first done.
    iIntros (w'). iDestruct 1 as (N3) "(?&%&?)".
    iExists _; iFrame.
    iPureIntro; etrans; first etrans; done.
  Qed.

  Lemma sem_typed_tlam Γ e τ :
    (subst (ren (+1)) <$> Γ) ⊨ e : τ -∗ Γ ⊨ TLam e : TForall τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ /=".
    iIntros (?) "?".
    iApply wp_value; simpl.
    iExists _; iFrame; iSplit; last done.
    iModIntro; iIntros (M' τi) "Hreg".
    iApply wp_pure_step_later; auto; iNext.
    iApply "IH"; last done. by iApply interp_env_ren.
  Qed.

  Lemma sem_typed_tapp Γ e τ τ' : Γ ⊨ e : TForall τ -∗ Γ ⊨ TApp e : τ.[τ'/].
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ /=".
    iIntros (?) "?".
    smart_wp_bind TAppCtx v "Hv" "IH"; cbn.
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    iApply wp_wand_r; iSplitL;
      first by iApply ("Hv" $! _ (⟦ τ' ⟧ Δ)).
    iIntros (w). iDestruct 1 as (N3) "(?&%&?)".
    iExists _; iFrame; iSplit; first by iApply interp_subst.
    iPureIntro; etrans; done.
  Qed.

  Lemma sem_typed_pack Γ e τ τ' : Γ ⊨ e : τ.[τ'/] -∗ Γ ⊨ Pack e : TExist τ.
  Proof.
    iIntros "#IH" (Δ vs) "!##HΓ /=".
    iIntros (?) "?".
    smart_wp_bind PackCtx v "Hv" "IH".
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    iApply wp_value.
    rewrite -interp_subst.
    iExists _; iFrame; iSplit; last done.
    iModIntro. iExists (interp _ Δ), _; iSplit; done.
  Qed.

  Lemma sem_typed_unpack Γ e1 e2 τ τ' :
    Γ ⊨ e1 : TExist τ -∗
    τ :: (subst (ren (+1)) <$> Γ) ⊨ e2 : τ'.[ren (+1)]  -∗
    Γ ⊨ UnpackIn e1 e2 : τ'.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ /=".
    iIntros (?) "?".
    smart_wp_bind (UnpackInCtx _) v "Hv" "IH1".
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    iDestruct "Hv" as (τi w ->) "#Hw"; simpl.
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    asimpl.
    iApply wp_wand_r; iSplitL.
    { iApply ("IH2" $! (τi :: Δ) (w :: vs) with "[] Hreg").
      iApply interp_env_cons; iSplit; first done.
      iApply interp_env_ren; done. }
    iIntros (w'). iDestruct 1 as (N3) "(?&%&?)".
    iExists _; iFrame; iSplit; first by iApply (interp_weaken [] [_]).
    iPureIntro; etrans; done.
  Qed.

  Lemma sem_typed_fold Γ e τ : Γ ⊨ e : τ.[(TRec τ)/] -∗ Γ ⊨ Fold e : TRec τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ /=".
    iIntros (?) "?".
    smart_wp_bind FoldCtx v "Hv" ("IH" $! Δ vs).
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    iApply wp_value.
    iExists _; iFrame; iSplit; last done.
    rewrite /= -interp_subst fixpoint_interp_rec1_eq /=.
    iModIntro; eauto.
  Qed.

  Lemma sem_typed_unfold Γ e τ : Γ ⊨ e : TRec τ -∗ Γ ⊨ Unfold e : τ.[(TRec τ)/].
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ /=".
    iIntros (?) "?".
    smart_wp_bind UnfoldCtx v "Hv" ("IH" $! Δ vs).
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    rewrite /= fixpoint_interp_rec1_eq.
    change (fixpoint _) with (⟦ TRec τ ⟧ Δ); simpl.
    iDestruct "Hv" as (w) "#[% Hw]"; subst.
    simpl.
    iApply wp_pure_step_later; cbn; auto using to_of_val.
    iNext. iApply wp_value.
    iExists _; iFrame; iSplit; last done.
    by iApply interp_subst.
  Qed.

  Lemma sem_typed_alloc Γ e τ : Γ ⊨ e : τ -∗ Γ ⊨ Alloc e : Tref τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ /=".
    iIntros (?) "?".
    smart_wp_bind AllocCtx v "Hv" "IH"; cbn.
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    iClear "HΓ". iApply wp_fupd.
    iApply wp_alloc; auto 1 using to_of_val.
    iNext; iIntros (l) "Hl".
    iMod (inv_alloc _ _ (∃ v : val, l ↦ᵢ v ∗ ⟦ τ ⟧ Δ v)%I with "[Hl]") as "HN".
    { by iNext; iExists _; iFrame. }
    iModIntro.
    iExists _; iFrame; iSplit; [by eauto| done].
  Qed.

  Lemma sem_typed_load Γ e τ : Γ ⊨ e : (Tref τ) -∗ Γ ⊨ Load e : τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ /=".
    iIntros (?) "?".
    smart_wp_bind LoadCtx v "Hv" "IH"; cbn. iClear "HΓ".
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    iDestruct "Hv" as (l) "[% #Hv]"; subst.
    iApply wp_atomic.
    iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
    iApply (wp_load with "Hw1").
    iModIntro. iNext.
    iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
  Qed.

  Lemma sem_typed_store Γ e1 e2 τ :
    Γ ⊨ e1 : (Tref τ) -∗ Γ ⊨ e2 : τ -∗ Γ ⊨ Store e1 e2 : TUnit.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ /=".
    iIntros (?) "?".
    smart_wp_bind (StoreLCtx _) v "Hv" "IH1"; cbn.
    iDestruct "Hv" as (N1) "(#Hv&%&Hreg)".
    smart_wp_bind (StoreRCtx _) w "Hw" "IH2"; cbn. iClear "HΓ".
    iDestruct "Hw" as (N2) "(#Hw&%&Hreg)".
    iDestruct "Hv" as (l) "[% #Hv]"; subst.
    iApply wp_atomic.
    iInv (logN .@ l) as (z) "[Hz1 #Hz2]" "Hclose".
    iApply (wp_store with "Hz1"); auto using to_of_val.
    iModIntro. iNext.
    iIntros "Hz1".
    iMod ("Hclose" with "[Hz1 Hz2]") as "_"; first by eauto.
    iModIntro; iExists _; iFrame; iSplit; first done.
    iPureIntro; etrans; done.
  Qed.

  Theorem fundamental Γ e τ : Γ ⊢ₜ e : τ → ⊢ Γ ⊨ e : τ.
  Proof.
    induction 1.
    - iApply sem_typed_var; done.
    - iApply sem_typed_unit; done.
    - iApply sem_typed_nat; done.
    - iApply sem_typed_bool; done.
    - iApply sem_typed_nat_binop; done.
    - iApply sem_typed_pair; done.
    - iApply sem_typed_fst; done.
    - iApply sem_typed_snd; done.
    - iApply sem_typed_injl; done.
    - iApply sem_typed_injr; done.
    - iApply sem_typed_case; done.
    - iApply sem_typed_if; done.
    - iApply sem_typed_rec; done.
    - iApply sem_typed_lam; done.
    - iApply sem_typed_letin; done.
    - iApply sem_typed_seq; done.
    - iApply sem_typed_app; done.
    - iApply sem_typed_tlam; done.
    - iApply sem_typed_tapp; done.
    - iApply sem_typed_pack; done.
    - iApply sem_typed_unpack; done.
    - iApply sem_typed_fold; done.
    - iApply sem_typed_unfold; done.
    - iApply sem_typed_alloc; done.
    - iApply sem_typed_load; done.
    - iApply sem_typed_store; done.
  Qed.
End typed_interp.
