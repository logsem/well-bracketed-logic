From iris.proofmode Require Import proofmode.
From WBLogic.program_logic Require Export weakestpre.
From WBLogic Require Export persistent_pred.
From WBLogic.F_mu_ref Require Export wp_rules typing.
From iris.algebra Require Import list.
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.
Import uPred.

Definition logN : namespace := nroot .@ "logN".

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{!heapIG Σ}.
  Notation D := (persistent_predO val (iPropI Σ)).
  Implicit Types τi : D.
  Implicit Types Δ : listO D.
  Implicit Types interp : listO D -n> D.

  Local Arguments ofe_car !_.

  Program Definition env_lookup (x : nat) : listO D -n> D :=
    λne Δ, PersPred (default (inhabitant : persistent_pred _ _) (Δ !! x)).
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Definition interp_unit : listO D -n> D := λne Δ, PersPred (λ w, ⌜w = UnitV⌝)%I.
  Definition interp_nat : listO D -n> D :=
    λne Δ, PersPred (λ w, ⌜∃ n, w = #nv n⌝)%I.
  Definition interp_bool : listO D -n> D :=
    λne Δ, PersPred (λ w, ⌜∃ n, w = #♭v n⌝)%I.

  Program Definition interp_prod
          (interp1 interp2 : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, ∃ w1 w2, ⌜w = PairV w1 w2⌝ ∧ interp1 Δ w1 ∧ interp2 Δ w2)%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_sum
      (interp1 interp2 : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, (∃ w1, ⌜w = InjLV w1⌝ ∧ interp1 Δ w1) ∨
                 (∃ w2, ⌜w = InjRV w2⌝ ∧ interp2 Δ w2))%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_arrow
      (interp1 interp2 : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, □ ∀ v,
      interp1 Δ v -∗ WBWP App (of_val w) (of_val v) {{ interp2 Δ }})%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_forall
      (interp : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, □ ∀ τi : D, WBWP TApp (of_val w) {{ interp (τi :: Δ) }})%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_exist (interp : listO D -n> D) : listO D -n> D :=
    λne Δ, PersPred (λ w, □ ∃ (τi : D) v, ⌜w = PackV v⌝ ∗ interp (τi :: Δ) v)%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Definition interp_rec1 (interp : listO D -n> D) (Δ : listO D) (τi : D) : D :=
    PersPred (λ w, □ (∃ v, ⌜w = FoldV v⌝ ∧ ▷ interp (τi :: Δ) v))%I.

  Global Instance interp_rec1_contractive
    (interp : listO D -n> D) (Δ : listO D) : Contractive (interp_rec1 interp Δ).
  Proof. by solve_contractive. Qed.

  Lemma fixpoint_interp_rec1_eq (interp : listO D -n> D) Δ x :
    fixpoint (interp_rec1 interp Δ) x ≡
    interp_rec1 interp Δ (fixpoint (interp_rec1 interp Δ)) x.
  Proof. exact: (fixpoint_unfold (interp_rec1 interp Δ) x). Qed.

  Program Definition interp_rec (interp : listO D -n> D) : listO D -n> D :=
    λne Δ, fixpoint (interp_rec1 interp Δ).
  Next Obligation.
    intros interp n Δ1 Δ2 HΔ; apply fixpoint_ne => τi w. solve_proper.
  Qed.

  Program Definition interp_ref_inv (l : loc) : D -n> iPropO Σ :=
    λne τi, (∃ v, l ↦ᵢ v ∗ τi v)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref (interp : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, ∃ l, ⌜w = LocV l⌝ ∧
                      inv (logN .@ l) (interp_ref_inv l (interp Δ)))%I.
  Solve Obligations with solve_proper.

  Fixpoint interp (τ : type) : listO D -n> D :=
    match τ return _ with
    | TUnit => interp_unit
    | TNat => interp_nat
    | TBool => interp_bool
    | TProd τ1 τ2 => interp_prod (interp τ1) (interp τ2)
    | TSum τ1 τ2 => interp_sum (interp τ1) (interp τ2)
    | TArrow τ1 τ2 => interp_arrow (interp τ1) (interp τ2)
    | TVar x => env_lookup x
    | TForall τ' => interp_forall (interp τ')
    | TExist τ' => interp_exist (interp τ')
    | TRec τ' => interp_rec (interp τ')
    | Tref τ' => interp_ref (interp τ')
    end.
  Notation "⟦ τ ⟧" := (interp τ).

  Definition interp_env (Γ : list type)
      (Δ : listO D) (vs : list val) : iProp Σ :=
    (⌜length Γ = length vs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs)%I.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Definition interp_expr (τ : type) (Δ : listO D) (e : expr) : iProp Σ := WBWP e {{ ⟦ τ ⟧ Δ }}.

  Global Instance interp_env_base_persistent Δ Γ vs :
  TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs).
  Proof. revert vs; induction Γ => vs; destruct vs; constructor; apply _. Qed.
  Global Instance interp_env_persistent Γ Δ vs : Persistent (⟦ Γ ⟧* Δ vs) := _.

  Lemma interp_weaken Δ1 Π Δ2 τ :
    ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ (Δ1 ++ Π ++ Δ2)
    ≡ ⟦ τ ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2; simpl; auto.
    - intros w; simpl; properness; auto;
        match goal with IH : ∀ _, _ |- _ => by apply IH end.
    - intros w; simpl; properness; auto;
        match goal with IH : ∀ _, _ |- _ => by apply IH end.
    - intros w; simpl; properness; auto;
        repeat
        (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - apply fixpoint_proper=> τi w /=.
      properness; auto.
      match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end.
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      intros ?; simpl.
      rewrite !lookup_app_r; [|lia ..]; do 3 f_equiv; lia.
    - intros w; simpl; properness; auto.
      repeat
        (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - intros w; simpl; properness; auto.
      match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end.
    - intros w; simpl; properness; auto.
      match goal with IH : ∀ _, _ |- _ => by apply IH end.
  Qed.

  Lemma interp_subst_up Δ1 Δ2 τ τ' :
    ⟦ τ ⟧ (Δ1 ++ interp τ' Δ2 :: Δ2)
    ≡ ⟦ τ.[upn (length Δ1) (τ' .: ids)] ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Δ2; induction τ=> Δ1 Δ2; simpl; auto.
    - intros w; simpl; properness; auto;
        match goal with IH : ∀ _, _ |- _ => by apply IH end.
    - intros w; simpl; properness; auto;
        match goal with IH : ∀ _, _ |- _ => by apply IH end.
    - intros w; simpl; properness; auto;
        repeat
        (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - apply fixpoint_proper=> τi w /=.
      properness; auto.
      match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end.
    - match goal with |- context [_ !! ?x] => rename x into idx end.
      rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      intros ?; simpl.
      rewrite !lookup_app_r; [|lia ..].
      case EQ: (idx - length Δ1) => [|n]; simpl.
      { symmetry. asimpl. apply (interp_weaken [] Δ1 Δ2 τ'). }
      rewrite !lookup_app_r; [|lia ..]. do 3 f_equiv. lia.
    - intros w; simpl; properness; auto.
      repeat
        (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - intros w; simpl; properness; auto.
      match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end.
    - intros w; simpl; properness; auto.
      match goal with IH : ∀ _, _ |- _ => by apply IH end.
  Qed.

  Lemma interp_subst Δ2 τ τ' v : ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) v ≡ ⟦ τ.[τ'/] ⟧ Δ2 v.
  Proof. apply (interp_subst_up []). Qed.

  Lemma interp_env_length Δ Γ vs : ⟦ Γ ⟧* Δ vs ⊢ ⌜length Γ = length vs⌝.
  Proof. by iIntros "[% ?]". Qed.

  Lemma interp_env_Some_l Δ Γ vs x τ :
    Γ !! x = Some τ → ⟦ Γ ⟧* Δ vs ⊢ ∃ v, ⌜vs !! x = Some v⌝ ∧ ⟦ τ ⟧ Δ v.
  Proof.
    iIntros (?) "[Hlen HΓ]"; iDestruct "Hlen" as %Hlen.
    destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
    { by rewrite -Hlen; apply lookup_lt_Some with τ. }
    iExists v; iSplit; first done. iApply (big_sepL_elem_of with "HΓ").
    apply elem_of_list_lookup_2 with x.
    rewrite lookup_zip_with; by simplify_option_eq.
  Qed.

  Lemma interp_env_nil Δ : ⊢ ⟦ [] ⟧* Δ [].
  Proof. iSplit; simpl; auto. Qed.
  Lemma interp_env_cons Δ Γ vs τ v :
    ⟦ τ :: Γ ⟧* Δ (v :: vs) ⊣⊢ ⟦ τ ⟧ Δ v ∗ ⟦ Γ ⟧* Δ vs.
  Proof.
    rewrite /interp_env /= (assoc _ (⟦ _ ⟧ _ _)) -(comm _ ⌜(_ = _)⌝%I) -assoc.
    by apply sep_proper; [apply pure_proper; lia|].
  Qed.

  Lemma interp_env_ren Δ (Γ : list type) (vs : list val) τi :
    ⟦ subst (ren (+1)) <$> Γ ⟧* (τi :: Δ) vs ⊣⊢ ⟦ Γ ⟧* Δ vs.
  Proof.
    apply sep_proper; [apply pure_proper; by rewrite fmap_length|].
    revert Δ vs τi; induction Γ=> Δ [|v vs] τi; csimpl; auto.
    apply sep_proper; auto. apply (interp_weaken [] [τi] Δ).
  Qed.
End logrel.

Global Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr τ).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
