From iris.proofmode Require Import proofmode.
From iris_examples.logrel.F_mu_ref_conc Require Import examples.lock.
From iris.prelude Require Import options.

Definition CG_StackType τ :=
  TRec (TSum TUnit (TProd τ.[ren (+1)] (TVar 0))).

(* Coarse-grained push *)
Definition CG_push (st : expr) : expr :=
  Lam (Store (st.[ren (+1)]) (Fold (InjR (Pair (Var 0) (Load st.[ren (+ 1)]))))).

Definition CG_locked_push (st l : expr) := with_lock (CG_push st) l.
Definition CG_locked_pushV (st l : expr) : val := with_lockV (CG_push st) l.

Definition CG_pop (st : expr) : expr :=
  Lam (Case (Unfold (Load st.[ren (+ 1)]))
            (InjL Unit)
            (
              Seq
                (Store st.[ren (+ 2)] (Snd (Var 0)))
                (InjR (Fst (Var 0)))
            )
      ).

Definition CG_locked_pop (st l : expr) := with_lock (CG_pop st) l.
Definition CG_locked_popV (st l : expr) : val := with_lockV (CG_pop st) l.

Definition CG_snap (st l : expr) :=  with_lock (Lam (Load st.[ren (+1)])) l.
Definition CG_snapV (st l : expr) : val := with_lockV (Lam (Load st.[ren (+1)])) l.

Definition CG_iter (f : expr) : expr :=
  Rec (Case (Unfold (Var 1))
            Unit
            (
              Seq
                (App f.[ren (+3)] (Fst (Var 0)))
                (App (Var 1) (Snd (Var 0)))
            )
      ).

Definition CG_iterV (f : expr) : val :=
  RecV (Case (Unfold (Var 1))
            Unit
            (
              Seq
                (App f.[ren (+3)] (Fst (Var 0)))
                (App (Var 1) (Snd (Var 0)))
            )
      ).

Definition CG_snap_iter (st l : expr) : expr :=
  Lam (App (CG_iter (Var 0)) (App (CG_snap st.[ren (+1)] l.[ren (+1)]) Unit)).

Definition CG_stack_body (st l : expr) : expr :=
  Pair (Pair (CG_locked_push st l) (CG_locked_pop st l))
       (CG_snap_iter st l).

Definition CG_stack : expr :=
  TLam (
      LetIn
        newlock
        (LetIn
           (Alloc (Fold (InjL Unit)))
           (CG_stack_body (Var 0) (Var 1)))).

Section CG_Stack.
  Context `{heapIG Σ, cfgSG Σ}.

  Lemma CG_push_type st Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ (CG_push st) (TArrow τ TUnit).
  Proof.
    intros H1. repeat econstructor.
    { eapply (context_weakening [_]); eauto. }
    repeat constructor; asimpl; trivial.
    eapply (context_weakening [_]); eauto.
  Qed.

  Lemma CG_push_subst (st : expr) f : (CG_push st).[f] = CG_push st.[f].
  Proof. unfold CG_push; asimpl; trivial. Qed.

  Hint Rewrite CG_push_subst : autosubst.

  Lemma steps_CG_push E j K st v w :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ v ∗ j ⤇ fill K (App (CG_push (Loc st)) (of_val w))
    ⊢ |={E}=> j ⤇ fill K Unit ∗ st ↦ₛ FoldV (InjRV (PairV w v)).
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold CG_push.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (step_load _ j (PairRCtx _ :: InjRCtx :: FoldCtx :: StoreRCtx (LocV _) :: K)
            with "[$Hj $Hx]") as "[Hj Hx]"; eauto.
    simpl.
    iMod (step_store _ j K with "[$Hj $Hx]") as "[Hj Hx]"; eauto.
    { rewrite /= !to_of_val //. }
    iModIntro. by iFrame.
  Qed.

  Typeclasses Opaque CG_push.
  Global Opaque CG_push.

  Lemma CG_locked_push_to_val st l :
    to_val (CG_locked_push st l) = Some (CG_locked_pushV st l).
  Proof. trivial. Qed.

  Lemma CG_locked_push_of_val st l :
    of_val (CG_locked_pushV st l) = CG_locked_push st l.
  Proof. trivial. Qed.

  Global Opaque CG_locked_pushV.
  Lemma CG_locked_push_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_locked_push st l) (TArrow τ TUnit).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; auto using CG_push_type.
  Qed.

  Lemma CG_locked_push_subst (st l : expr) f :
    (CG_locked_push st l).[f] = CG_locked_push st.[f] l.[f].
  Proof. by rewrite /CG_locked_push; asimpl. Qed.

  Hint Rewrite CG_locked_push_subst : autosubst.

  Lemma steps_CG_locked_push E j K st w v l :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ v ∗ l ↦ₛ (#♭v false)
      ∗ j ⤇ fill K (App (CG_locked_push (Loc st) (Loc l)) (of_val w))
    ⊢ |={E}=> j ⤇ fill K Unit ∗ st ↦ₛ FoldV (InjRV (PairV w v)) ∗ l ↦ₛ (#♭v false).
  Proof.
    intros HNE. iIntros "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_push.
    iMod (steps_with_lock _ _ _ _ _ (st ↦ₛ v)%I _ UnitV with "[$Hj $Hx $Hl]")
      as "Hj"; auto.
    iIntros (K') "[#Hspec Hxj]".
    iApply steps_CG_push; first done. by iFrame.
  Qed.

  Typeclasses Opaque CG_locked_push.
  Global Opaque CG_locked_push.

  (* Coarse-grained pop *)
  Lemma CG_pop_type st Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ (CG_pop st) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    intros H1.
    econstructor.
    eapply (Case_typed _ _ _ _ TUnit); eauto using typed.
    - replace (TSum TUnit (TProd τ (CG_StackType τ))) with
          ((TSum TUnit (TProd τ.[ren (+1)] (TVar 0))).[(CG_StackType τ)/])
        by (by asimpl).
      repeat econstructor.
      eapply (context_weakening [_]); eauto.
    - econstructor; eauto using typed.
      econstructor; eauto using typed.
      eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma CG_pop_subst (st : expr) f :
    (CG_pop st).[f] = CG_pop st.[f].
  Proof. by rewrite /CG_pop; asimpl. Qed.

  Hint Rewrite CG_pop_subst : autosubst.

  Lemma steps_CG_pop_suc E j K st v w :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ FoldV (InjRV (PairV w v)) ∗
               j ⤇ fill K (App (CG_pop (Loc st)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjR (of_val w)) ∗ st ↦ₛ v.
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold CG_pop.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (step_load _ _ (UnfoldCtx :: CaseCtx _ _ :: K)  with "[$Hj $Hx]")
      as "[Hj Hx]"; eauto.
    simpl.
    iMod (do_step_pure _ _ (CaseCtx _ _ :: K) with "[$Hj]") as "Hj"; eauto.
    simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (do_step_pure _ _ (StoreRCtx (LocV _) :: SeqCtx _ :: K)
            with "[$Hj]") as "Hj"; eauto.
    simpl.
    iMod (step_store _ j (SeqCtx _ :: K) with "[$Hj $Hx]") as "[Hj Hx]";
      eauto using to_of_val.
    simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iMod (do_step_pure _ _ (InjRCtx :: K) with "[$Hj]") as "Hj"; eauto.
    simpl.
    by iFrame "Hj Hx".
  Qed.

  Lemma steps_CG_pop_fail E j K st :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ FoldV (InjLV UnitV) ∗
               j ⤇ fill K (App (CG_pop (Loc st)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjL Unit) ∗ st ↦ₛ FoldV (InjLV UnitV).
  Proof.
    iIntros (HNE) "[#Hspec [Hx Hj]]". unfold CG_pop.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (step_load _ j (UnfoldCtx :: CaseCtx _ _ :: K)
                    _ _ _ with "[$Hj $Hx]") as "[Hj Hx]"; eauto.
    iMod (do_step_pure _ _ (CaseCtx _ _ :: K) with "[$Hj]") as "Hj"; eauto.
    simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    by iFrame "Hj Hx"; trivial.
  Qed.

  Typeclasses Opaque CG_pop.
  Global Opaque CG_pop.

  Lemma CG_locked_pop_to_val st l :
    to_val (CG_locked_pop st l) = Some (CG_locked_popV st l).
  Proof. trivial. Qed.

  Lemma CG_locked_pop_of_val st l :
    of_val (CG_locked_popV st l) = CG_locked_pop st l.
  Proof. trivial. Qed.

  Global Opaque CG_locked_popV.

  Lemma CG_locked_pop_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_locked_pop st l) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; auto using CG_pop_type.
  Qed.

  Lemma CG_locked_pop_subst (st l : expr) f :
    (CG_locked_pop st l).[f] = CG_locked_pop st.[f] l.[f].
  Proof. by rewrite /CG_locked_pop; asimpl. Qed.

  Hint Rewrite CG_locked_pop_subst : autosubst.

  Lemma steps_CG_locked_pop_suc E j K st v w l :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ FoldV (InjRV (PairV w v)) ∗ l ↦ₛ (#♭v false)
               ∗ j ⤇ fill K (App (CG_locked_pop (Loc st) (Loc l)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjR (of_val w)) ∗ st ↦ₛ v ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_pop.
    iMod (steps_with_lock _ _ _ _ _ (st ↦ₛ FoldV (InjRV (PairV w v)))%I
                          _ (InjRV w) UnitV
            with "[$Hj $Hx $Hl]") as "Hj"; eauto.
    iIntros (K') "[#Hspec Hxj]".
    iApply steps_CG_pop_suc; eauto.
  Qed.

  Lemma steps_CG_locked_pop_fail E j K st l :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ FoldV (InjLV UnitV) ∗ l ↦ₛ (#♭v false)
               ∗ j ⤇ fill K (App (CG_locked_pop (Loc st) (Loc l)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjL Unit) ∗ st ↦ₛ FoldV (InjLV UnitV) ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_pop.
    iMod (steps_with_lock _ _ _ _ _ (st ↦ₛ FoldV (InjLV UnitV))%I _
                          (InjLV UnitV) UnitV
          with "[$Hj $Hx $Hl]") as "Hj"; eauto.
    iIntros (K') "[#Hspec Hxj] /=".
      iApply steps_CG_pop_fail; eauto.
  Qed.

  Typeclasses Opaque CG_locked_pop.
  Global Opaque CG_locked_pop.

  Lemma CG_snap_to_val st l : to_val (CG_snap st l) = Some (CG_snapV st l).
  Proof. trivial. Qed.

  Lemma CG_snap_of_val st l : of_val (CG_snapV st l) = CG_snap st l.
  Proof. trivial. Qed.

  Typeclasses Opaque CG_snapV.
  Global Opaque CG_snapV.

  Lemma CG_snap_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_snap st l) (TArrow TUnit (CG_StackType τ)).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; trivial. do 2 constructor.
    eapply (context_weakening [_]); eauto.
  Qed.

  Lemma CG_snap_subst (st l : expr) f :
    (CG_snap st l).[f] = CG_snap st.[f] l.[f].
  Proof. by unfold CG_snap; asimpl. Qed.

  Hint Rewrite CG_snap_subst : autosubst.

  Lemma steps_CG_snap E j K st v l :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ v ∗ l ↦ₛ (#♭v false)
               ∗ j ⤇ fill K (App (CG_snap (Loc st) (Loc l)) Unit)
      ⊢ |={E}=> j ⤇ (fill K (of_val v)) ∗ st ↦ₛ v ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hx [Hl Hj]]]". unfold CG_snap.
    iMod (steps_with_lock _ _ _ _ _ (st ↦ₛ v)%I _ v UnitV
          with "[$Hj $Hx $Hl]") as "Hj"; eauto.
    iIntros (K') "[#Hspec [Hx Hj]]".
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (step_load with "[$Hj $Hx]") as "[Hj Hx]"; eauto.
    by iFrame.
  Qed.

  Typeclasses Opaque CG_snap.
  Global Opaque CG_snap.

  (* Coarse-grained iter *)
  Lemma CG_iter_folding (f : expr) :
    CG_iter f =
    Rec (Case (Unfold (Var 1))
              Unit
              (
                Seq
                  (App f.[ren (+3)] (Fst (Var 0)))
                  (App (Var 1) (Snd (Var 0)))
              )
        ).
  Proof. trivial. Qed.

  Lemma CG_iter_type f Γ τ :
    typed Γ f (TArrow τ TUnit) →
    typed Γ (CG_iter f) (TArrow (CG_StackType τ) TUnit).
  Proof.
    intros ?. econstructor.
    eapply (Case_typed _ _ _ _ TUnit); eauto using typed.
    - replace (TSum TUnit (TProd τ (CG_StackType τ))) with
      ((TSum TUnit (TProd τ.[ren (+1)] (TVar 0))).[(CG_StackType τ)/])
        by (by asimpl).
      repeat econstructor.
    - repeat econstructor; simpl; eauto using typed.
      eapply (context_weakening [_; _; _]); eauto.
  Qed.

  Lemma CG_iter_to_val f : to_val (CG_iter f) = Some (CG_iterV f).
  Proof. trivial. Qed.

  Lemma CG_iter_of_val f : of_val (CG_iterV f) = CG_iter f.
  Proof. trivial. Qed.

  Typeclasses Opaque CG_iterV.
  Global Opaque CG_iterV.

  Lemma CG_iter_subst (f : expr) g : (CG_iter f).[g] = CG_iter f.[g].
  Proof. by unfold CG_iter; asimpl. Qed.

  Hint Rewrite CG_iter_subst : autosubst.

  Lemma steps_CG_iter E j K f v w :
    nclose specN ⊆ E →
    spec_ctx
             ∗ j ⤇ fill K (App (CG_iter (of_val f))
                               (Fold (InjR (Pair (of_val w) (of_val v)))))
      ⊢ |={E}=>
    j ⤇ fill K
          (Seq (App (of_val f) (of_val w))
               (App (CG_iter (of_val f)) (Snd (Pair (of_val w) (of_val v))))).
  Proof.
    iIntros (HNE) "[#Hspec Hj]". unfold CG_iter.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (do_step_pure _ _ (CaseCtx _ _ :: K) with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (do_step_pure _ _ (AppRCtx f :: SeqCtx _ :: K) with "[$Hj]")
      as "Hj"; eauto.
  Qed.

  Lemma steps_CG_iter_end E j K f :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (App (CG_iter (of_val f)) (Fold (InjL Unit)))
      ⊢ |={E}=> j ⤇ fill K Unit.
  Proof.
    iIntros (HNE) "[#Hspec Hj]". unfold CG_iter.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iMod (do_step_pure _ _ (CaseCtx _ _ :: K) with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
  Qed.

  Typeclasses Opaque CG_iter.
  Global Opaque CG_iter.

  Lemma CG_snap_iter_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_snap_iter st l) (TArrow (TArrow τ TUnit) TUnit).
  Proof.
    intros H1 H2; repeat econstructor.
    - eapply CG_iter_type; by constructor.
    - eapply CG_snap_type; by eapply (context_weakening [_]).
  Qed.

  Lemma CG_snap_iter_subst (st l : expr) g :
    (CG_snap_iter st l).[g] = CG_snap_iter st.[g] l.[g].
  Proof. by unfold CG_snap_iter; asimpl. Qed.

  Hint Rewrite CG_snap_iter_subst : autosubst.

  Lemma CG_stack_body_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_stack_body st l)
          (TProd
             (TProd (TArrow τ TUnit) (TArrow TUnit (TSum TUnit τ)))
             (TArrow (TArrow τ TUnit) TUnit)
          ).
  Proof.
    intros H1 H2.
    repeat (econstructor; eauto using CG_locked_push_type,
                          CG_locked_pop_type, CG_snap_iter_type).
  Qed.


  Typeclasses Opaque CG_snap_iter.
  Global Opaque CG_snap_iter.

  Lemma CG_stack_body_subst (st l : expr) f :
    (CG_stack_body st l).[f] = CG_stack_body st.[f] l.[f].
  Proof. by unfold CG_stack_body; asimpl. Qed.

  Hint Rewrite CG_stack_body_subst : autosubst.

  Lemma CG_stack_type Γ :
    typed Γ CG_stack
          (TForall
             (TProd
                (TProd
                   (TArrow (TVar 0) TUnit)
                   (TArrow TUnit (TSum TUnit (TVar 0)))
                )
                (TArrow (TArrow (TVar 0) TUnit) TUnit)
          )).
  Proof.
    repeat econstructor;
      eauto 10 using newlock_type, CG_locked_push_type, CG_locked_pop_type,
      CG_snap_iter_type, typed.
    asimpl; repeat constructor.
  Qed.

  Lemma CG_stack_closed f : CG_stack.[f] = CG_stack.
  Proof. by unfold CG_stack; asimpl. Qed.

End CG_Stack.

Global Hint Rewrite CG_push_subst : autosubst.
Global Hint Rewrite CG_locked_push_subst : autosubst.
Global Hint Rewrite CG_locked_pop_subst : autosubst.
Global Hint Rewrite CG_pop_subst : autosubst.
Global Hint Rewrite CG_locked_pop_subst : autosubst.
Global Hint Rewrite CG_snap_subst : autosubst.
Global Hint Rewrite CG_iter_subst : autosubst.
Global Hint Rewrite CG_snap_iter_subst : autosubst.
Global Hint Rewrite CG_stack_body_subst : autosubst.
Global Hint Rewrite CG_stack_closed : autosubst.
