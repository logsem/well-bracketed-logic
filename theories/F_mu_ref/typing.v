From WBLogrel.F_mu_ref Require Export lang.
From iris.prelude Require Import options.

Inductive type :=
  | TUnit : type
  | TNat : type
  | TBool : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TForall (τ : {bind 1 of type})
  | TExist (τ : {bind 1 of type})
  | Tref (τ : type).

Global Instance Ids_type : Ids type. derive. Defined.
Global Instance Rename_type : Rename type. derive. Defined.
Global Instance Subst_type : Subst type. derive. Defined.
Global Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Definition binop_res_type (op : binop) : type :=
  match op with
  | Add => TNat | Sub => TNat | Mult => TNat
  | Eq => TBool | Le => TBool | Lt => TBool
  end.

Inductive EqType : type → Prop :=
  | EqTUnit : EqType TUnit
  | EqTNat : EqType TNat
  | EqTBool : EqType TBool
  | EQRef τ : EqType (Tref τ).

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).

Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → Γ ⊢ₜ Var x : τ
  | Unit_typed : Γ ⊢ₜ Unit : TUnit
  | Nat_typed n : Γ ⊢ₜ #n n : TNat
  | Bool_typed b : Γ ⊢ₜ #♭ b : TBool
  | BinOp_typed op e1 e2 :
     Γ ⊢ₜ e1 : TNat → Γ ⊢ₜ e2 : TNat → Γ ⊢ₜ BinOp op e1 e2 : binop_res_type op
  | Pair_typed e1 e2 τ1 τ2 : Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Snd e : τ2
  | InjL_typed e τ1 τ2 : Γ ⊢ₜ e : τ1 → Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 : Γ ⊢ₜ e : τ2 → Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 τ3 :
     Γ ⊢ₜ e0 : TSum τ1 τ2 → τ1 :: Γ ⊢ₜ e1 : τ3 → τ2 :: Γ ⊢ₜ e2 : τ3 →
     Γ ⊢ₜ Case e0 e1 e2 : τ3
  | If_typed e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool → Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ If e0 e1 e2 : τ
  | Rec_typed e τ1 τ2 :
     TArrow τ1 τ2 :: τ1 :: Γ ⊢ₜ e : τ2 → Γ ⊢ₜ Rec e : TArrow τ1 τ2
  | Lam_typed e τ1 τ2 :
      τ1 :: Γ ⊢ₜ e : τ2 → Γ ⊢ₜ Lam e : TArrow τ1 τ2
  | LetIn_typed e1 e2 τ1 τ2 :
      Γ ⊢ₜ e1 : τ1 → τ1 :: Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ LetIn e1 e2 : τ2
  | Seq_typed e1 e2 τ1 τ2 :
      Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ Seq e1 e2 : τ2
  | App_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : TArrow τ1 τ2 → Γ ⊢ₜ e2 : τ1 → Γ ⊢ₜ App e1 e2 : τ2
  | TLam_typed e τ :
     subst (ren (+1)) <$> Γ ⊢ₜ e : τ → Γ ⊢ₜ TLam e : TForall τ
  | TApp_typed e τ τ' : Γ ⊢ₜ e : TForall τ → Γ ⊢ₜ TApp e : τ.[τ'/]
  | Pack_typed e τ τ' :
     Γ ⊢ₜ e : τ.[τ'/] → Γ ⊢ₜ Pack e : TExist τ
  | UnpackIn_typed e1 e2 τ τ' :
     Γ ⊢ₜ e1 : TExist τ →
     τ :: (subst (ren (+1)) <$> Γ) ⊢ₜ e2 : τ'.[ren (+1)] →
     Γ ⊢ₜ UnpackIn e1 e2 : τ'
  | TFold e τ : Γ ⊢ₜ e : τ.[TRec τ/] → Γ ⊢ₜ Fold e : TRec τ
  | TUnfold e τ : Γ ⊢ₜ e : TRec τ → Γ ⊢ₜ Unfold e : τ.[TRec τ/]
  | TAlloc e τ : Γ ⊢ₜ e : τ → Γ ⊢ₜ Alloc e : Tref τ
  | TLoad e τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ Load e : τ
  | TStore e e' τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ e' : τ → Γ ⊢ₜ Store e e' : TUnit
where "Γ ⊢ₜ e : τ" := (typed Γ e τ).

Fixpoint env_subst (vs : list val) : var → expr :=
  match vs with
  | [] => ids
  | v :: vs' => (of_val v) .: env_subst vs'
  end.

Lemma env_subst_lookup vs x v :
  vs !! x = Some v → env_subst vs x = of_val v.
Proof.
  revert vs; induction x as [|x IH] => vs.
  - by destruct vs; inversion 1.
  - destruct vs as [|w vs]; first by inversion 1.
    rewrite -lookup_tail /=.
    apply IH.
Qed.

Lemma typed_n_closed Γ τ e : Γ ⊢ₜ e : τ → (∀ f, e.[upn (length Γ) f] = e).
Proof.
  intros H. induction H => f; asimpl; simpl in *; auto with f_equal.
  - rename select (_ !! _ = Some _) into H.
    apply lookup_lt_Some in H. rewrite iter_up. destruct lt_dec; auto with lia.
  - f_equal. eauto.
  - f_equal. rewrite ->map_length in *. done.
  - rewrite ->map_length in *; by f_equal.
Qed.

(** Weakening *)
Lemma context_gen_weakening ξ Γ' Γ e τ :
  Γ' ++ Γ ⊢ₜ e : τ →
  Γ' ++ ξ ++ Γ ⊢ₜ e.[upn (length Γ') (ren (+ (length ξ)))] : τ.
Proof.
  intros H1.
  remember (Γ' ++ Γ) as Ξ eqn:HeqΞ. revert Γ' Γ ξ HeqΞ.
  induction H1 => Γ1 Γ2 ξ HeqΞ; subst; asimpl; eauto using typed.
  - rename select (_ !! _ = Some _) into Hlookup.
    rewrite iter_up; destruct lt_dec as [Hl | Hl].
    + constructor. rewrite lookup_app_l; trivial. by rewrite lookup_app_l in Hlookup.
    + asimpl. constructor. rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r in Hlookup; auto with lia.
      rename select var into x.
      match goal with
        |- _ !! ?A = _ => by replace A with (x - length Γ1) by lia
      end.
  - econstructor; eauto.
    all: match goal with H : context[_ → _ ⊢ₜ _ : _] |- _ => by apply (H (_::_)) end.
  - constructor.
    match goal with H : context[_ → _ ⊢ₜ _ : _] |- _ => by apply (H (_::_::_)) end.
  - constructor.
    match goal with H : context[_ → _ ⊢ₜ _ : _] |- _ => by apply (H (_::_)) end.
  - econstructor; eauto.
    match goal with H : context[_ → _ ⊢ₜ _ : _] |- _ => by apply (H (_::_)) end.
  - constructor.
    match goal with H : context[_ → _ ⊢ₜ _ : _] |- _ => rename H into IH end.
    specialize (IH
      (subst (ren (+1)) <$> Γ1) (subst (ren (+1)) <$> Γ2) (subst (ren (+1)) <$> ξ)).
    rewrite ?map_length in IH.
    repeat rewrite fmap_app. apply IH.
    by repeat rewrite fmap_app.
  - econstructor; eauto.
    match goal with H : context[_ → _ ⊢ₜ _ : _.[ren (+1)]] |- _ => rename H into IH end.
    match goal with H : context[_ → _ ⊢ₜ _ : TExist ?t] |- _ => rename t into τ end.
    specialize (IH
      (τ :: (subst (ren (+1)) <$> Γ1)) (subst (ren (+1)) <$> Γ2) (subst (ren (+1)) <$> ξ)).
    asimpl in IH. rewrite ?map_length in IH.
    repeat rewrite fmap_app. apply IH.
    by repeat rewrite fmap_app.
Qed.

Lemma context_weakening ξ Γ e τ :
  Γ ⊢ₜ e : τ → ξ ++ Γ ⊢ₜ e.[(ren (+ (length ξ)))] : τ.
Proof. eapply (context_gen_weakening _ []). Qed.

Lemma closed_context_weakening ξ Γ e τ :
  (∀ f, e.[f] = e) → Γ ⊢ₜ e : τ → ξ ++ Γ ⊢ₜ e : τ.
Proof. intros H1 H2. erewrite <- H1. by eapply context_weakening. Qed.
