From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth list.
From iris.program_logic Require Import adequacy.
From iris_examples.logrel.F_mu_ref_conc.binary.examples Require Export lock.
From iris_examples.logrel.F_mu_ref_conc.binary Require Import soundness.
From iris.prelude Require Import options.

Definition CG_increment (x : expr) : expr :=
  Lam (Store x.[ren (+ 1)] (BinOp Add (#n 1) (Load x.[ren (+ 1)]))).

Definition CG_locked_increment (x l : expr) : expr :=
  with_lock (CG_increment x) l.
Definition CG_locked_incrementV (x l : expr) : val :=
  with_lockV (CG_increment x) l.

Definition counter_read (x : expr) : expr := Lam (Load x.[ren (+1)]).
Definition counter_readV (x : expr) : val := LamV (Load x.[ren (+1)]).

Definition CG_counter_body (x l : expr) : expr :=
  Pair (CG_locked_increment x l) (counter_read x).
Definition CG_counter : expr :=
  LetIn newlock (LetIn (Alloc (#n 0)) (CG_counter_body (Var 0) (Var 1))).

Definition FG_increment (x : expr) : expr :=
  Rec (LetIn
         (Load x.[ren (+2)]) (* read the counter *)
         (* try increment *)
         (If (CAS x.[ren (+3)] (Var 0) (BinOp Add (#n 1) (Var 0)))
             Unit (* increment succeeds we return unit *)
             (App (Var 1) (Var 2)) (* increment fails, we try again *))).
Definition FG_counter_body (x : expr) : expr :=
  Pair (FG_increment x) (counter_read x).
Definition FG_counter : expr :=
  LetIn (Alloc (#n 0)) (FG_counter_body (Var 0)).

Section CG_Counter.
  Context `{heapIG Σ, cfgSG Σ}.

  Notation D := (persistent_predO (val * val) (iPropI Σ)).
  Implicit Types Δ : listO D.

  (* Coarse-grained increment *)
  Lemma CG_increment_type x Γ :
    typed Γ x (Tref TNat) →
    typed Γ (CG_increment x) (TArrow TUnit TUnit).
  Proof.
    intros H1. repeat econstructor.
    - eapply (context_weakening [_]); eauto.
    - eapply (context_weakening [_]); eauto.
  Qed.

  Lemma CG_increment_closed (x : expr) :
    (∀ f, x.[f] = x) → ∀ f, (CG_increment x).[f] = CG_increment x.
  Proof. intros Hx f. unfold CG_increment. asimpl. rewrite ?Hx; trivial. Qed.

  Hint Rewrite CG_increment_closed : autosubst.

  Lemma CG_increment_subst (x : expr) f :
    (CG_increment x).[f] = CG_increment x.[f].
  Proof. unfold CG_increment; asimpl; trivial. Qed.

  Hint Rewrite CG_increment_subst : autosubst.

  Lemma steps_CG_increment E j K x n:
    nclose specN ⊆ E →
    spec_ctx ∗ x ↦ₛ (#nv n) ∗ j ⤇ fill K (App (CG_increment (Loc x)) Unit)
      ⊢ |={E}=> j ⤇ fill K (Unit) ∗ x ↦ₛ (#nv (S n)).
  Proof.
    iIntros (HNE) "[#Hspec [Hx Hj]]". unfold CG_increment.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iMod (step_load _ j ((BinOpRCtx _ (#nv _) :: StoreRCtx (LocV _) :: K))
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    { iFrame "Hspec Hj"; trivial. }
    simpl.
    iMod (do_step_pure _ _ ((StoreRCtx (LocV _)) :: K)  with "[$Hj]") as "Hj";
      eauto.
    simpl.
    iMod (step_store _ j K with "[$Hj $Hx]") as "[Hj Hx]"; eauto.
    iModIntro; iFrame.
  Qed.

  Global Opaque CG_increment.

  Lemma CG_locked_increment_to_val x l :
    to_val (CG_locked_increment x l) = Some (CG_locked_incrementV x l).
  Proof. by rewrite with_lock_to_val. Qed.

  Lemma CG_locked_increment_of_val x l :
    of_val (CG_locked_incrementV x l) = CG_locked_increment x l.
  Proof. by rewrite with_lock_of_val. Qed.

  Global Opaque CG_locked_incrementV.

  Lemma CG_locked_increment_type x l Γ :
    typed Γ x (Tref TNat) →
    typed Γ l LockType →
    typed Γ (CG_locked_increment x l) (TArrow TUnit TUnit).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; auto using CG_increment_type.
  Qed.

  Lemma CG_locked_increment_subst (x l : expr) f :
  (CG_locked_increment x l).[f] = CG_locked_increment x.[f] l.[f].
  Proof.
    unfold CG_locked_increment. simpl.
    rewrite with_lock_subst CG_increment_subst. asimpl; trivial.
  Qed.

  Hint Rewrite CG_locked_increment_subst : autosubst.

  Lemma steps_CG_locked_increment E j K x n l :
    nclose specN ⊆ E →
    spec_ctx ∗ x ↦ₛ (#nv n) ∗ l ↦ₛ (#♭v false)
      ∗ j ⤇ fill K (App (CG_locked_increment (Loc x) (Loc l)) Unit)
    ={E}=∗ j ⤇ fill K Unit ∗ x ↦ₛ (#nv S n) ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hx [Hl Hj]]]".
    iMod (steps_with_lock
            _ j K _ _ _ _ UnitV UnitV with "[$Hj Hx $Hl]") as "Hj"; eauto.
    - iIntros (K') "[#Hspec Hxj]".
      iApply steps_CG_increment; by try iFrame.
    - by iFrame.
  Qed.

  Global Opaque CG_locked_increment.

  Lemma counter_read_to_val x : to_val (counter_read x) = Some (counter_readV x).
  Proof. trivial. Qed.

  Lemma counter_read_of_val x : of_val (counter_readV x) = counter_read x.
  Proof. trivial. Qed.

  Global Opaque counter_readV.

  Lemma counter_read_type x Γ :
    typed Γ x (Tref TNat) → typed Γ (counter_read x) (TArrow TUnit TNat).
  Proof.
    intros H1. repeat econstructor.
    eapply (context_weakening [_]); trivial.
  Qed.

  Lemma counter_read_closed (x : expr) :
    (∀ f, x.[f] = x) → ∀ f, (counter_read x).[f] = counter_read x.
  Proof. intros H1 f. asimpl. unfold counter_read. by rewrite ?H1. Qed.

  Hint Rewrite counter_read_closed : autosubst.

  Lemma counter_read_subst (x: expr) f :
    (counter_read x).[f] = counter_read x.[f].
  Proof. unfold counter_read. by asimpl. Qed.

  Hint Rewrite counter_read_subst : autosubst.

  Lemma steps_counter_read E j K x n :
    nclose specN ⊆ E →
    spec_ctx ∗ x ↦ₛ (#nv n)
               ∗ j ⤇ fill K (App (counter_read (Loc x)) Unit)
    ={E}=∗ j ⤇ fill K (#n n) ∗ x ↦ₛ (#nv n).
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold counter_read.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (step_load _ j K with "[$Hj Hx]") as "[Hj Hx]"; eauto.
    by iFrame.
  Qed.

  Local Opaque counter_read.

  Lemma CG_counter_body_type x l Γ :
    typed Γ x (Tref TNat) →
    typed Γ l LockType →
    typed Γ (CG_counter_body x l)
            (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    intros H1 H2; repeat econstructor;
      eauto using CG_locked_increment_type, counter_read_type.
  Qed.

  Lemma CG_counter_body_subst (x l : expr) f :
    (CG_counter_body x l).[f] = CG_counter_body x.[f] l.[f].
  Proof. by asimpl. Qed.

  Hint Rewrite CG_counter_body_subst : autosubst.

  Lemma CG_counter_type Γ :
    typed Γ CG_counter (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    econstructor; eauto using newlock_type.
    econstructor; first eauto using typed.
    apply CG_counter_body_type; eauto using typed.
  Qed.

  Lemma CG_counter_closed f : CG_counter.[f] = CG_counter.
  Proof. by asimpl. Qed.

  Hint Rewrite CG_counter_closed : autosubst.

  (* Fine-grained increment *)
  Lemma FG_increment_type x Γ :
    typed Γ x (Tref TNat) →
    typed Γ (FG_increment x) (TArrow TUnit TUnit).
  Proof.
    intros Hx. do 3 econstructor; eauto using typed.
    - eapply (context_weakening [_; _]); eauto.
    - econstructor; [| |repeat econstructor |].
      + constructor.
      + eapply (context_weakening [_; _; _]); eauto.
      + repeat constructor.
  Qed.

  Lemma FG_increment_subst (x : expr) f :
    (FG_increment x).[f] = FG_increment x.[f].
  Proof. rewrite /FG_increment. by asimpl. Qed.

  Hint Rewrite FG_increment_subst : autosubst.

  Lemma FG_counter_body_type x Γ :
    typed Γ x (Tref TNat) →
    typed Γ (FG_counter_body x)
            (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    intros H1; econstructor.
    - apply FG_increment_type; trivial.
    - apply counter_read_type; trivial.
  Qed.

  Lemma FG_counter_body_subst (x : expr) f :
    (FG_counter_body x).[f] = FG_counter_body x.[f].
  Proof. rewrite /FG_counter_body /FG_increment. by asimpl. Qed.

  Hint Rewrite FG_counter_body_subst : autosubst.

  Lemma FG_counter_type Γ :
    Γ ⊢ₜ FG_counter : (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    econstructor; eauto using newlock_type, typed.
    apply FG_counter_body_type; by constructor.
  Qed.

  Lemma FG_counter_closed f : FG_counter.[f] = FG_counter.
  Proof. by asimpl. Qed.

  Hint Rewrite FG_counter_closed : autosubst.

  Definition counterN : namespace := nroot .@ "counter".

  Lemma FG_CG_counter_refinement :
    ⊢ [] ⊨ FG_counter ≤log≤ CG_counter : TProd (TArrow TUnit TUnit) (TArrow TUnit TNat).
  Proof.
    iIntros (Δ [|??]) "!# #(Hspec & HΓ)"; iIntros (j K) "Hj"; last first.
    { iDestruct (interp_env_length with "HΓ") as %[=]. }
    iClear "HΓ". cbn -[FG_counter CG_counter].
    rewrite ?empty_env_subst /CG_counter /FG_counter.
    iApply fupd_wp.
    iMod (steps_newlock _ j (LetInCtx _ :: K) with "[$Hj]")
      as (l) "[Hj Hl]"; eauto.
    simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (step_alloc _ j (LetInCtx _ :: K) with "[$Hj]")
      as (cnt') "[Hj Hcnt']"; eauto.
    simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_wand_l. iSplitR; [iModIntro; iIntros (v) "Hv"; iExact "Hv"|].
    iApply (wp_alloc); trivial; iFrame "#"; iModIntro; iNext; iIntros (cnt) "Hcnt /=".
    (* establishing the invariant *)
    iAssert ((∃ n, l ↦ₛ (#♭v false) ∗ cnt ↦ᵢ (#nv n) ∗ cnt' ↦ₛ (#nv n) )%I)
      with "[Hl Hcnt Hcnt']" as "Hinv".
    { iExists _. by iFrame. }
    iApply fupd_wp.
    iMod (inv_alloc counterN with "[Hinv]") as "#Hinv"; [iNext; iExact "Hinv"|].
    (* splitting increment and read *)
    iApply wp_pure_step_later; trivial. iModIntro. iNext. iAsimpl.
    iApply wp_value; auto.
    iExists (PairV (CG_locked_incrementV _ _) (counter_readV _)); simpl.
    rewrite CG_locked_increment_of_val counter_read_of_val.
    iFrame "Hj".
    iExists (_, _), (_, _); simpl; repeat iSplit; trivial.
    - (* refinement of increment *)
      iModIntro. clear j K. iIntros (v) "#Heq". iIntros (j K) "Hj".
      rewrite CG_locked_increment_of_val /=.
      destruct v; iDestruct "Heq" as "[% %]"; simplify_eq/=.
      iLöb as "Hlat".
      iApply wp_pure_step_later; trivial. iAsimpl. iNext.
      (* fine-grained reads the counter *)
      iApply (wp_bind (fill [LetInCtx _]));
        iApply wp_wand_l; iSplitR; [iIntros (v) "Hv"; iExact "Hv"|].
      iApply wp_atomic; eauto.
      iInv counterN as (n) ">[Hl [Hcnt Hcnt']]" "Hclose".
      iApply (wp_load with "[Hcnt]"); [iNext; by iFrame|].
      iModIntro. iNext. iIntros "Hcnt".
      iMod ("Hclose" with "[Hl Hcnt Hcnt']").
      { iNext. iExists _. iFrame "Hl Hcnt Hcnt'". }
      iApply wp_pure_step_later; trivial. iAsimpl. iModIntro. iNext.
      (* fine-grained performs increment *)
      iApply (wp_bind (fill [CasRCtx (LocV _) (NatV _); IfCtx _ _]));
        iApply wp_wand_l; iSplitR; [iIntros (v) "Hv"; iExact "Hv"|].
      iApply wp_pure_step_later; auto. iApply wp_value.
      iNext.
      iApply (wp_bind (fill [IfCtx _ _]));
        iApply wp_wand_l; iSplitR; [iIntros (v) "Hv"; iExact "Hv"|].
      iApply wp_atomic; eauto.
      iInv counterN as (n') ">[Hl [Hcnt Hcnt']]" "Hclose".
      (* performing CAS *)
      destruct (decide (n = n')) as [|Hneq]; subst.
      + (* CAS succeeds *)
        (* In this case, we perform increment in the coarse-grained one *)
        iMod (steps_CG_locked_increment
                _ _ _ _ _ _ _ with "[Hj Hl Hcnt']") as "[Hj [Hcnt' Hl]]".
        { iFrame "Hspec Hcnt' Hl Hj"; trivial. }
        iApply (wp_cas_suc with "[Hcnt]"); auto.
        iModIntro. iNext. iIntros "Hcnt".
        iMod ("Hclose" with "[Hl Hcnt Hcnt']").
        { iNext. iExists _. iFrame "Hl Hcnt Hcnt'"; trivial. }
        simpl.
        iApply wp_pure_step_later; trivial.
        iModIntro. iNext. iApply wp_value; trivial.
        iExists UnitV; iFrame; auto.
      + (* CAS fails *)
        (* In this case, we perform a recursive call *)
        iApply (wp_cas_fail _ _ _ (#nv n') with "[Hcnt]"); auto;
        [inversion 1; subst; auto | ].
        iModIntro. iNext. iIntros "Hcnt".
        iMod ("Hclose" with "[Hl Hcnt Hcnt']").
        { iNext. iExists _; iFrame "Hl Hcnt Hcnt'". }
        iApply wp_pure_step_later; trivial. iModIntro. iNext. by iApply "Hlat".
    - (* refinement of read *)
      iModIntro. clear j K. iIntros (v) "#Heq". iIntros (j K) "Hj".
      rewrite ?counter_read_of_val.
      iDestruct "Heq" as "[% %]"; destruct v; simplify_eq/=.
      Local Transparent counter_read. (* HACK *)
      unfold counter_read.
      iApply wp_pure_step_later; trivial. simpl.
      iNext.
      iApply wp_atomic; eauto.
      iInv counterN as (n) ">[Hl [Hcnt Hcnt']]" "Hclose".
      iMod (steps_counter_read with "[Hj Hcnt']") as "[Hj Hcnt']"; first by solve_ndisj.
      { by iFrame "Hspec Hcnt' Hj". }
      iApply (wp_load with "[Hcnt]"); eauto.
      iModIntro. iNext. iIntros "Hcnt".
      iMod ("Hclose" with "[Hl Hcnt Hcnt']").
      { iNext. iExists _; iFrame "Hl Hcnt Hcnt'". }
      iExists (#nv _); eauto.
      Unshelve. solve_ndisj.
  Qed.
End CG_Counter.

Theorem counter_ctx_refinement :
  [] ⊨ FG_counter ≤ctx≤ CG_counter :
         TProd (TArrow TUnit TUnit) (TArrow TUnit TNat).
Proof.
  set (Σ := #[invΣ ; gen_heapΣ loc val ; soundness_binaryΣ ]).
  set (HG := soundness.HeapPreIG Σ _ _).
  eapply (binary_soundness Σ _); auto using FG_counter_type, CG_counter_type.
  intros. apply FG_CG_counter_refinement.
Qed.
