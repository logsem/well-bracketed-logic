From iris_examples.logrel.F_mu_ref_conc Require Import typing.
From iris.prelude Require Import options.

Definition FG_StackType τ :=
  TRec (Tref (TSum TUnit (TProd τ.[ren (+1)] (TVar 0)))).

Definition FG_Stack_Ref_Type τ :=
  Tref (TSum TUnit (TProd τ (FG_StackType τ))).

Definition FG_push (st : expr) : expr :=
  Rec
    (LetIn
       (Load st.[ren (+2)])
       (* try push *)
       (If (CAS (st.[ren (+3)]) (Var 0)
                (Alloc (InjR (Pair (Var 2) (Fold (Var 0)))))
           )
           Unit (* push succeeds we return unit *)
           (App (Var 1) (Var 2)) (* push fails, we try again *)
       )
    ).

Definition FG_pushV (st : expr) : val :=
  RecV
    (LetIn
       (Load st.[ren (+2)])
       (* try push *)
       (If (CAS (st.[ren (+3)]) (Var 0)
                (Alloc (InjR (Pair (Var 2) (Fold (Var 0)))))
           )
           Unit (* push succeeds we return unit *)
           (App (Var 1) (Var 2)) (* push fails, we try again *)
       )
    ).

Definition FG_pop (st : expr) : expr :=
  Rec
    (LetIn
       (Load st.[ren (+ 2)])
       (LetIn
          (Load (Var 0))
          (Case
             (Var 0)
             (InjL Unit)
             ( (* try popping *)
               If
                 (CAS
                    (st.[ren (+5)])
                    (Var 2)
                    (Unfold (Snd (Var 0)))
                 )
                 (InjR (Fst (Var 0))) (* pop succeeds *)
                 (App (Var 3) (Var 4)) (* pop fails, we retry*)
             )
          )
       )
    ).

Definition FG_popV (st : expr) : val :=
  RecV
    (LetIn
       (Load st.[ren (+ 2)])
       (LetIn
          (Load (Var 0))
          (Case
             (Var 0)
             (InjL Unit)
             ( (* try popping *)
               If
                 (CAS
                    (st.[ren (+5)])
                    (Var 2)
                    (Unfold (Snd (Var 0)))
                 )
                 (InjR (Fst (Var 0))) (* pop succeeds *)
                 (App (Var 3) (Var 4)) (* pop fails, we retry*)
             )
          )
       )
    ).

Definition FG_iter (f : expr) : expr :=
  Rec
    (Case (Load (Unfold (Var 1)))
          Unit
          (Seq
             (App f.[ren (+3)] (Fst (Var 0)))
             (App (Var 1) (Snd (Var 0))) (* recursive_call *)
          )
    ).

Definition FG_iterV (f : expr) : val :=
  RecV
    (Case (Load (Unfold (Var 1)))
          Unit
          (Seq
             (App f.[ren (+3)] (Fst (Var 0)))
             (App (Var 1) (Snd (Var 0))) (* recursive_call *)
          )
    ).

Definition FG_read_iter (st : expr) : expr :=
  Lam (App (FG_iter (Var 0)) (Fold (Load st.[ren (+1)]))).

Definition FG_stack_body (st : expr) : expr :=
  Pair (Pair (FG_push st) (FG_pop st)) (FG_read_iter st).

Definition FG_stack : expr :=
  TLam (App (Rec (FG_stack_body (Var 1)))
                (Alloc (Alloc (InjL Unit)))).

Section FG_stack.
  (* Fine-grained push *)
  Lemma FG_push_folding (st : expr) :
    FG_push st =
    Rec
    (LetIn
       (Load st.[ren (+2)])
       (* try push *)
       (If (CAS (st.[ren (+3)]) (Var 0)
                (Alloc (InjR (Pair (Var 2) (Fold (Var 0)))))
           )
           Unit (* push succeeds we return unit *)
           (App (Var 1) (Var 2)) (* push fails, we try again *)
       )
    ).
  Proof. trivial. Qed.


  Lemma FG_push_to_val st : to_val (FG_push st) = Some (FG_pushV st).
  Proof. trivial. Qed.

  Lemma FG_push_of_val st : of_val (FG_pushV st) = FG_push st.
  Proof. trivial. Qed.

  Typeclasses Opaque FG_pushV.
  Global Opaque FG_pushV.

  Lemma FG_push_type st Γ τ :
    typed Γ st (Tref (FG_Stack_Ref_Type τ)) →
    typed Γ (FG_push st) (TArrow τ TUnit).
  Proof.
    intros ?.
    do 2 econstructor.
    { econstructor; eapply (context_weakening [_; _]); eauto. }
    econstructor; eauto using typed.
    econstructor; eauto using typed; repeat econstructor.
    - eapply (context_weakening [_; _; _]); eauto.
    - by asimpl.
  Qed.

  Lemma FG_push_subst (st : expr) f :
    (FG_push st).[f] = FG_push st.[f].
  Proof. by rewrite /FG_push; asimpl. Qed.

  Hint Rewrite FG_push_subst : autosubst.

  Typeclasses Opaque FG_push.
  Global Opaque FG_push.

  (* Fine-grained push *)
  Lemma FG_pop_folding (st : expr) :
    FG_pop st =
    Rec
      (LetIn
         (Load st.[ren (+ 2)])
         (LetIn
            (Load (Var 0))
            (Case
               (Var 0)
               (InjL Unit)
               ( (* try popping *)
                 If
                   (CAS
                      (st.[ren (+5)])
                      (Var 2)
                    (Unfold (Snd (Var 0)))
                   )
                   (InjR (Fst (Var 0))) (* pop succeeds *)
                   (App (Var 3) (Var 4)) (* pop fails, we retry*)
               )
            )
         )
      ).
  Proof. trivial. Qed.

  Lemma FG_pop_to_val st : to_val (FG_pop st) = Some (FG_popV st).
  Proof. trivial. Qed.
  Lemma FG_pop_of_val st : of_val (FG_popV st) = FG_pop st.
  Proof. trivial. Qed.

  Typeclasses Opaque FG_popV.
  Global Opaque FG_popV.

  Lemma FG_pop_type st Γ τ :
    typed Γ st (Tref (FG_Stack_Ref_Type τ)) →
    typed Γ (FG_pop st) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    replace (FG_Stack_Ref_Type τ) with
        (Tref (TSum TUnit (TProd τ.[ren (+1)] (TVar 0)))).[FG_StackType τ/];
      last first.
    { by asimpl. }
    intros ?.
    do 2 econstructor.
    { econstructor. eapply (context_weakening [_; _]); eauto. }
    econstructor.
    { repeat econstructor. }
    econstructor.
    { repeat econstructor. }
    { repeat econstructor. }
    econstructor.
    - econstructor;
        [|eapply (context_weakening [_; _; _; _; _]); eauto| |];
        repeat econstructor.
    - by repeat econstructor; asimpl.
    - repeat econstructor.
  Qed.

  Lemma FG_pop_subst (st : expr) f : (FG_pop st).[f] = FG_pop st.[f].
  Proof. unfold FG_pop. by asimpl. Qed.

  Hint Rewrite FG_pop_subst : autosubst.

  Typeclasses Opaque FG_pop.
  Global Opaque FG_pop.

  (* Fine-grained iter *)
  Lemma FG_iter_folding (f : expr) :
    FG_iter f =
    Rec
      (Case (Load (Unfold (Var 1)))
            Unit
            (Seq
               (App f.[ren (+3)] (Fst (Var 0)))
               (App (Var 1) (Snd (Var 0))) (* recursive_call *)
            )
      ).
  Proof. trivial. Qed.

  Lemma FG_iter_type f Γ τ :
    typed Γ f (TArrow τ TUnit) →
    typed Γ (FG_iter f) (TArrow (FG_StackType τ) TUnit).
  Proof.
    intros H1.
    econstructor.
    eapply (Case_typed _ _ _ _ TUnit);
      [| repeat constructor
       | repeat econstructor; eapply (context_weakening [_; _; _]); eauto].
    econstructor.
    replace (Tref (TSum TUnit (TProd τ (FG_StackType τ)))) with
    ((Tref (TSum TUnit (TProd τ.[ren(+1)] (TVar 0)))).[(FG_StackType τ)/])
      by (by asimpl).
    repeat econstructor.
  Qed.

  Lemma FG_iter_to_val st : to_val (FG_iter st) = Some (FG_iterV st).
  Proof. trivial. Qed.

  Lemma FG_iter_of_val st : of_val (FG_iterV st) = FG_iter st.
  Proof. trivial. Qed.

  Global Opaque FG_popV.
  Lemma FG_iter_subst (f : expr) g : (FG_iter f).[g] = FG_iter f.[g].
  Proof. unfold FG_iter. by asimpl. Qed.

  Hint Rewrite FG_iter_subst : autosubst.

  Typeclasses Opaque FG_iter.
  Global Opaque FG_iter.

  Lemma FG_read_iter_type st Γ τ :
    typed Γ st (Tref (FG_Stack_Ref_Type τ)) →
    typed Γ (FG_read_iter st)
          (TArrow (TArrow τ TUnit) TUnit).
  Proof.
    intros H1; repeat econstructor.
    - eapply FG_iter_type; by constructor.
    - by eapply (context_weakening [_]); asimpl.
  Qed.

  Lemma FG_read_iter_subst (st : expr) g :
    (FG_read_iter st).[g] = FG_read_iter st.[g].
  Proof. by unfold FG_read_iter; asimpl. Qed.

  Hint Rewrite FG_read_iter_subst : autosubst.

  Typeclasses Opaque FG_read_iter.
  Global Opaque FG_read_iter.

  Lemma FG_stack_body_type st Γ τ :
    typed Γ st (Tref (FG_Stack_Ref_Type τ)) →
    typed Γ (FG_stack_body st)
          (TProd
             (TProd (TArrow τ TUnit) (TArrow TUnit (TSum TUnit τ)))
             (TArrow (TArrow τ TUnit) TUnit)
          ).
  Proof.
    intros H1.
    repeat (econstructor; eauto using FG_push_type,
                          FG_pop_type, FG_read_iter_type).
  Qed.

  Lemma FG_stack_body_subst (st : expr) f :
    (FG_stack_body st).[f] = FG_stack_body st.[f].
  Proof. by unfold FG_stack_body; asimpl. Qed.

  Hint Rewrite FG_stack_body_subst : autosubst.

  Lemma FG_stack_type Γ :
    typed Γ FG_stack
          (TForall
             (TProd
                (TProd
                   (TArrow (TVar 0) TUnit)
                   (TArrow TUnit (TSum TUnit (TVar 0)))
                )
                (TArrow (TArrow (TVar 0) TUnit) TUnit)
          )).
  Proof.
    repeat econstructor.
    - eapply FG_push_type; try constructor; simpl; eauto.
    - eapply FG_pop_type; try constructor; simpl; eauto.
    - eapply FG_read_iter_type; constructor; by simpl.
  Qed.

  Lemma FG_stack_closed f : FG_stack.[f] = FG_stack.
  Proof. by unfold FG_stack; asimpl. Qed.

End FG_stack.

Global Hint Rewrite FG_push_subst : autosubst.
Global Hint Rewrite FG_pop_subst : autosubst.
Global Hint Rewrite FG_iter_subst : autosubst.
Global Hint Rewrite FG_read_iter_subst : autosubst.
Global Hint Rewrite FG_stack_body_subst : autosubst.
Global Hint Rewrite FG_stack_closed : autosubst.
