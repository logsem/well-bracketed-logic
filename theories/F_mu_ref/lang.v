From iris.program_logic Require Export language ectx_language ectxi_language.
From WBLogic.F_mu_ref Require Export base.
From iris.algebra Require Export ofe.
From stdpp Require Import gmap.
From iris.prelude Require Import options.

Module F_mu_ref.
  Definition loc := positive.

  Global Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _.

  Inductive binop := Add | Sub | Mult | Eq | Le | Lt.

  Global Instance binop_dec_eq (op op' : binop) : Decision (op = op').
  Proof. solve_decision. Defined.

  Inductive expr :=
  | Var (x : var)
  | Rec (e : {bind 2 of expr})
  | App (e1 e2 : expr)
  | Lam (e : {bind expr})
  | LetIn (e1 : expr) (e2 : {bind expr})
  | Seq (e1 e2 : expr)
  (* Base Types *)
  | Unit
  | Int (n : Z)
  | Bool (b : bool)
  | BinOp (op : binop) (e1 e2 : expr)
  (* If then else *)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
  (* Recursive Types *)
  | Fold (e : expr)
  | Unfold (e : expr)
  (* Polymorphic Types *)
  | TLam (e : expr)
  | TApp (e : expr)
  (* Existential Types *)
  | Pack (e : expr)
  | UnpackIn (e1 : expr) (e2 : {bind expr})
  (* Reference Types *)
  | Loc (l : loc)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr).
  Global Instance Ids_expr : Ids expr. derive. Defined.
  Global Instance Rename_expr : Rename expr. derive. Defined.
  Global Instance Subst_expr : Subst expr. derive. Defined.
  Global Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

  (* Notation for bool and nat *)
  Notation "#♭ b" := (Bool b) (at level 20).
  Notation "#z n" := (Int n) (at level 20).

  Global Instance expr_dec_eq (e e' : expr) : Decision (e = e').
  Proof. solve_decision. Defined.

  Inductive val :=
  | RecV (e : {bind 1 of expr})
  | LamV (e : {bind expr})
  | TLamV (e : {bind 1 of expr})
  | PackV (v : val)
  | UnitV
  | IntV (n : Z)
  | BoolV (b : bool)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | FoldV (v : val)
  | LocV (l : loc).

  (* Notation for bool and nat *)
  Notation "'#♭v' b" := (BoolV b) (at level 20).
  Notation "'#zv' n" := (IntV n) (at level 20).

  Definition binop_eval (op : binop) : Z → Z → val :=
    match op with
    | Add => λ a b, #zv(a + b)
    | Sub => λ a b, #zv(a - b)
    | Mult => λ a b, #zv(a * b)
    | Eq => λ a b, if (Z.eq_dec a b) then #♭v true else #♭v false
    | Le => λ a b, if (Z.le_dec a b) then #♭v true else #♭v false
    | Lt => λ a b, if (Z.lt_dec a b) then #♭v true else #♭v false
    end.

  Global Instance val_dec_eq (v v' : val) : Decision (v = v').
  Proof. solve_decision. Defined.

  Global Instance val_inh : Inhabited val := populate UnitV.

  Fixpoint of_val (v : val) : expr :=
    match v with
    | RecV e => Rec e
    | LamV e => Lam e
    | TLamV e => TLam e
    | PackV v => Pack (of_val v)
    | UnitV => Unit
    | IntV v => Int v
    | BoolV v => Bool v
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    | InjLV v => InjL (of_val v)
    | InjRV v => InjR (of_val v)
    | FoldV v => Fold (of_val v)
    | LocV l => Loc l
    end.

  Fixpoint to_val (e : expr) : option val :=
    match e with
    | Rec e => Some (RecV e)
    | Lam e => Some (LamV e)
    | TLam e => Some (TLamV e)
    | Pack e => PackV <$> to_val e
    | Unit => Some UnitV
    | Int n => Some (IntV n)
    | Bool b => Some (BoolV b)
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
    | InjL e => InjLV <$> to_val e
    | InjR e => InjRV <$> to_val e
    | Fold e => v ← to_val e; Some (FoldV v)
    | Loc l => Some (LocV l)
    | _ => None
    end.

  (** Evaluation contexts *)
  Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | LetInCtx (e2 : expr)
  | SeqCtx (e2 : expr)
  | TAppCtx
  | PackCtx
  | UnpackInCtx (e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | BinOpLCtx (op : binop) (e2 : expr)
  | BinOpRCtx (op : binop) (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
  | IfCtx (e1 : {bind expr}) (e2 : {bind expr})
  | FoldCtx
  | UnfoldCtx
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx e2 => App e e2
    | AppRCtx v1 => App (of_val v1) e
    | LetInCtx e2 => LetIn e e2
    | SeqCtx e2 => Seq e e2
    | TAppCtx => TApp e
    | PackCtx => Pack e
    | UnpackInCtx e2 => UnpackIn e e2
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (of_val v1) e
    | BinOpLCtx op e2 => BinOp op e e2
    | BinOpRCtx op v1 => BinOp op (of_val v1) e
    | FstCtx => Fst e
    | SndCtx => Snd e
    | InjLCtx => InjL e
    | InjRCtx => InjR e
    | CaseCtx e1 e2 => Case e e1 e2
    | IfCtx e1 e2 => If e e1 e2
    | FoldCtx => Fold e
    | UnfoldCtx => Unfold e
    | AllocCtx => Alloc e
    | LoadCtx => Load e
    | StoreLCtx e2 => Store e e2
    | StoreRCtx v1 => Store (of_val v1) e
    end.

  Definition state : Type := gmap loc val.

  Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
  (* β *)
  | BetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Rec e1) e2) σ [] e1.[(Rec e1), e2/] σ []
  (* Lam-β *)
  | LamBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Lam e1) e2) σ [] e1.[e2/] σ []
  (* LetIn-β *)
  | LetInBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (LetIn e1 e2) σ [] e2.[e1/] σ []
  (* Seq-β *)
  | SeqBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (Seq e1 e2) σ [] e2 σ []
  (* Products *)
  | FstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Fst (Pair e1 e2)) σ [] e1 σ []
  | SndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Snd (Pair e1 e2)) σ [] e2 σ []
  (* Sums *)
  | CaseLS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjL e0) e1 e2) σ [] e1.[e0/] σ []
  | CaseRS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjR e0) e1 e2) σ [] e2.[e0/] σ []
    (* nat bin op *)
  | BinOpS op a b σ :
      head_step (BinOp op (#z a) (#z b)) σ [] (of_val (binop_eval op a b)) σ []
  (* If then else *)
  | IfFalse e1 e2 σ :
      head_step (If (#♭ false) e1 e2) σ [] e2 σ []
  | IfTrue e1 e2 σ :
      head_step (If (#♭ true) e1 e2) σ [] e1 σ []
  (* Recursive Types *)
  | Unfold_Fold e v σ :
      to_val e = Some v →
      head_step (Unfold (Fold e)) σ [] e σ []
  (* Polymorphic Types *)
  | TBeta e σ :
      head_step (TApp (TLam e)) σ [] e σ []
  (* Existential Types *)
  | UnpackS e1 v e2 σ :
      to_val e1 = Some v →
      head_step (UnpackIn (Pack e1) e2) σ [] e2.[e1/] σ []
  (* Reference Types *)
  | AllocS e v σ l :
     to_val e = Some v → σ !! l = None →
     head_step (Alloc e) σ [] (Loc l) (<[l:=v]>σ) []
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Loc l)) σ [] (of_val v) σ []
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Loc l) e) σ [] Unit (<[l:=v]>σ) [].

  (** Basic properties about the language *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. by induction v; simplify_option_eq. Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    revert v; induction e; intros; simplify_option_eq; auto with f_equal.
  Qed.

  Global Instance of_val_inj : Inj (=) (=) of_val.
  Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma val_stuck e1 σ1 κs e2 σ2 ef :
    head_step e1 σ1 κs e2 σ2 ef → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val Ki e σ1 κs e2 σ2 ef :
    head_step (fill_item Ki e) σ1 κs e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
           end; auto.
  Qed.

  Lemma alloc_fresh e v σ :
    let l := fresh (dom σ) in
    to_val e = Some v → head_step (Alloc e) σ [] (Loc l) (<[l:=v]>σ) [].
  Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

  Lemma val_head_stuck e1 σ1 κs e2 σ2 efs : head_step e1 σ1 κs e2 σ2 efs → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

  Canonical Structure stateO := leibnizO state.
  Canonical Structure valO := leibnizO val.
  Canonical Structure exprO := leibnizO expr.
End F_mu_ref.

Canonical Structure F_mu_ref_ectxi_lang :=
  EctxiLanguage F_mu_ref.lang_mixin.
Canonical Structure F_mu_ref_ectx_lang :=
  EctxLanguageOfEctxi F_mu_ref_ectxi_lang.
Canonical Structure F_mu_ref_lang :=
  LanguageOfEctx F_mu_ref_ectx_lang.

Export F_mu_ref.

Global Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

Global Hint Extern 5 (IntoVal _ _) =>
  eapply of_to_val; fast_done : typeclass_instances.
Global Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val;
  rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Global Hint Extern 5 (AsVal _) =>
  eexists; eapply of_to_val; fast_done : typeclass_instances.
Global Hint Extern 10 (AsVal _) =>
  eexists; rewrite /IntoVal; eapply of_to_val;
  rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Definition is_atomic (e : expr) : Prop :=
  match e with
  | Alloc e => is_Some (to_val e)
  | Load e =>  is_Some (to_val e)
  | Store e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
  | _ => False
  end.
Local Hint Resolve language.val_irreducible : core.
Local Hint Resolve to_of_val : core.
Local Hint Unfold language.irreducible : core.
Global Instance is_atomic_correct s e : is_atomic e → Atomic s e.
Proof.
  intros Ha; apply strongly_atomic_atomic,  ectx_language_atomic.
  - destruct 1; simpl in *; try tauto; eauto.
  - intros K e' -> Hval%eq_None_not_Some.
    induction K as [|Ki K] using rev_ind; first done.
    simpl in Ha; rewrite fill_app in Ha; simpl in Ha.
    destruct Hval. apply (fill_val K e'); simpl in *.
    destruct Ki; naive_solver.
Qed.

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.

Global Hint Extern 0 (Atomic _ _) => solve_atomic : core.
Global Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.
