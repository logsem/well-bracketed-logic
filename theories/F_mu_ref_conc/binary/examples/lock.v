From iris.proofmode Require Import proofmode.
From iris_examples.logrel.F_mu_ref_conc.binary Require Export rules.
From iris_examples.logrel.F_mu_ref_conc Require Export typing.
From iris.prelude Require Import options.

(** [newlock = alloc false] *)
Definition newlock : expr := Alloc (#♭ false).
(** [acquire = λ x. if cas(x, false, true) then #() else acquire(x) ] *)
Definition acquire : expr :=
  Rec (If (CAS (Var 1) (#♭ false) (#♭ true)) (Unit) (App (Var 0) (Var 1))).
(** [release = λ x. x <- false] *)
Definition release : expr := Lam (Store (Var 0) (#♭ false)).
(** [with_lock e l = λ x. (acquire l) ;; e x ;; (release l)] *)
Definition with_lock (e : expr) (l : expr) : expr :=
  Lam
    (Seq
       (App acquire l.[ren (+1)])
       (LetIn
          (App e.[ren (+1)] (Var 0))
          (Seq (App release l.[ren (+2)]) (Var 0))
       )
    ).

Definition with_lockV (e l : expr) : val :=
  LamV
    (Seq
       (App acquire l.[ren (+1)])
       (LetIn
          (App e.[ren (+1)] (Var 0))
          (Seq (App release l.[ren (+2)]) (Var 0))
       )
    ).

Lemma with_lock_to_val e l : to_val (with_lock e l) = Some (with_lockV e l).
Proof. trivial. Qed.

Lemma with_lock_of_val e l : of_val (with_lockV e l) = with_lock e l.
Proof. trivial. Qed.

Global Typeclasses Opaque with_lockV.
Global Opaque with_lockV.

Lemma newlock_closed f : newlock.[f] = newlock.
Proof. by asimpl. Qed.
Global Hint Rewrite newlock_closed : autosubst.

Lemma acquire_closed f : acquire.[f] = acquire.
Proof. by asimpl. Qed.
Global Hint Rewrite acquire_closed : autosubst.

Lemma release_closed f : release.[f] = release.
Proof. by asimpl. Qed.
Global Hint Rewrite release_closed : autosubst.

Lemma with_lock_subst (e l : expr) f :
  (with_lock e l).[f] = with_lock e.[f] l.[f].
Proof. unfold with_lock; asimpl; trivial. Qed.

Definition LockType := Tref TBool.

Lemma newlock_type Γ : typed Γ newlock LockType.
Proof. repeat constructor. Qed.

Lemma acquire_type Γ : typed Γ acquire (TArrow LockType TUnit).
Proof. do 3 econstructor; eauto using EqTBool; repeat constructor. Qed.

Lemma release_type Γ : typed Γ release (TArrow LockType TUnit).
Proof. repeat econstructor. Qed.

Lemma with_lock_type e l Γ τ τ' :
  typed Γ e (TArrow τ τ') →
  typed Γ l LockType →
  typed Γ (with_lock e l) (TArrow τ τ').
Proof.
  intros ??.
  do 3 econstructor; eauto using acquire_type.
  - eapply (context_weakening [_]); eauto.
  - econstructor; eauto using typed.
    eapply (context_weakening [_]); eauto.
  - econstructor; eauto using typed.
    econstructor; eauto using release_type.
    eapply (context_weakening [_;_]); eauto.
Qed.

Section proof.
  Context `{cfgSG Σ}.
  Context `{heapIG Σ}.

  Lemma steps_newlock E j K :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K newlock
      ⊢ |={E}=> ∃ l, j ⤇ fill K (Loc l) ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec Hj]".
    by iMod (step_alloc _ j K with "[Hj]") as "Hj"; eauto.
  Qed.

  Typeclasses Opaque newlock.
  Global Opaque newlock.

  Lemma steps_acquire E j K l :
    nclose specN ⊆ E →
    spec_ctx ∗ l ↦ₛ (#♭v false) ∗ j ⤇ fill K (App acquire (Loc l))
      ⊢ |={E}=> j ⤇ fill K Unit ∗ l ↦ₛ (#♭v true).
  Proof.
    iIntros (HNE) "[#Hspec [Hl Hj]]". unfold acquire.
    iMod (step_rec _ j K with "[Hj]") as "Hj"; eauto; first done.
    iMod (step_cas_suc _ j ((IfCtx _ _) :: K)
                       _ _ _ _ _ _ _ _ _ with "[Hj Hl]") as "[Hj Hl]"; trivial.
    { simpl. iFrame "Hspec Hj Hl"; eauto. }
    iMod (step_if_true _ j K _ _ _ with "[Hj]") as "Hj"; trivial.
    { by iFrame. }
    by iIntros "!> {$Hj $Hl}".
    Unshelve. all:trivial.
  Qed.

  Typeclasses Opaque acquire.
  Global Opaque acquire.

  Lemma steps_release E j K l b:
    nclose specN ⊆ E →
    spec_ctx ∗ l ↦ₛ (#♭v b) ∗ j ⤇ fill K (App release (Loc l))
      ⊢ |={E}=> j ⤇ fill K Unit ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hl Hj]]". unfold release.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto; try done.
    iMod (step_store with "[$Hj $Hl]") as "[Hj Hl]"; eauto.
    by iIntros "!> {$Hj $Hl}".
  Qed.

  Typeclasses Opaque release.
  Global Opaque release.

  Lemma steps_with_lock E j K e l P Q v w:
    nclose specN ⊆ E →
    (* (∀ f, e.[f] = e) (* e is a closed term *) → *)
    (∀ K', spec_ctx ∗ P ∗ j ⤇ fill K' (App e (of_val w))
            ⊢ |={E}=> j ⤇ fill K' (of_val v) ∗ Q) →
    spec_ctx ∗ P ∗ l ↦ₛ (#♭v false)
                ∗ j ⤇ fill K (App (with_lock e (Loc l)) (of_val w))
      ⊢ |={E}=> j ⤇ fill K (of_val v) ∗ Q ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE He) "[#Hspec [HP [Hl Hj]]]".
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (steps_acquire _ j (SeqCtx _ :: K) with "[$Hj Hl]") as "[Hj Hl]";
      auto. simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iMod (He (LetInCtx _ :: K) with "[$Hj HP]") as "[Hj HQ]"; eauto.
    simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (steps_release _ j (SeqCtx _ :: K) _ _ with "[$Hj $Hl]")
      as "[Hj Hl]"; eauto.
    simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iModIntro; by iFrame.
  Qed.

  Typeclasses Opaque with_lock.
  Global Opaque with_lock.
End proof.

Global Hint Rewrite newlock_closed : autosubst.
Global Hint Rewrite acquire_closed : autosubst.
Global Hint Rewrite release_closed : autosubst.
Global Hint Rewrite with_lock_subst : autosubst.
