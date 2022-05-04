From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.base_logic Require Export invariants.
From iris.algebra Require Import auth frac agree gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export gen_heap.
From iris_examples.logrel.F_mu_ref_conc Require Export lang.
From iris.prelude Require Import options.

(** The CMRA for the heap of the implementation. This is linked to the
    physical heap. *)
Class heapIG Σ := HeapIG {
  heapI_invG : invGS Σ;
  heapI_gen_heapG :> gen_heapGS loc val Σ;
}.

Global Instance heapIG_irisG `{heapIG Σ} : irisGS F_mu_ref_conc_lang Σ := {
  iris_invGS := heapI_invG;
  num_laters_per_step _ := 0;
  state_interp σ  _ _ _ := gen_heap_interp σ;
  fork_post _ := True%I;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Notation "l ↦ᵢ{ dq } v" := (mapsto (L:=loc) (V:=val) l dq v)
  (at level 20, format "l  ↦ᵢ{ dq }  v") : bi_scope.
Notation "l ↦ᵢ□ v" := (mapsto (L:=loc) (V:=val) l DfracDiscarded v)
  (at level 20, format "l  ↦ᵢ□  v") : bi_scope.
Notation "l ↦ᵢ{# q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) v)
  (at level 20, format "l  ↦ᵢ{# q }  v") : bi_scope.
Notation "l ↦ᵢ v" := (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v)
  (at level 20, format "l  ↦ᵢ  v") : bi_scope.

Section lang_rules.
  Context `{heapIG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v w : val.

  Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

  Local Hint Extern 0 (atomic _) => solve_atomic : core.
  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.

  Local Hint Constructors head_step : core.
  Local Hint Resolve alloc_fresh : core.
  Local Hint Resolve to_of_val : core.

  (** Base axioms for core primitives of the language: Stateful reductions. *)
  Lemma wp_alloc E e v :
    IntoVal e v →
    {{{ True }}} Alloc e @ E {{{ l, RET (LocV l); l ↦ᵢ v }}}.
  Proof.
    iIntros (<- Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "Hσ !>"; iSplit; first by auto.
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iMod (@gen_heap_alloc with "Hσ") as "(Hσ & Hl & _)"; first done.
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_load E l dq v :
    {{{ ▷ l ↦ᵢ{dq} v }}} Load (Loc l) @ E {{{ RET v; l ↦ᵢ{dq} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
    iSplit; first by eauto.
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_store E l v' e v :
    IntoVal e v →
    {{{ ▷ l ↦ᵢ v' }}} Store (Loc l) e @ E
    {{{ RET UnitV; l ↦ᵢ v }}}.
  Proof.
    iIntros (<- Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
    iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
    iModIntro. iSplit=>//. by iApply "HΦ".
  Qed.

  Lemma wp_cas_fail E l dq v' e1 v1 e2 v2 :
    IntoVal e1 v1 → IntoVal e2 v2 → v' ≠ v1 →
    {{{ ▷ l ↦ᵢ{dq} v' }}} CAS (Loc l) e1 e2 @ E
    {{{ RET (BoolV false); l ↦ᵢ{dq} v' }}}.
  Proof.
    iIntros (<- <- ? Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
    iSplit; first by eauto.
    iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_cas_suc E l e1 v1 e2 v2 :
    IntoVal e1 v1 → IntoVal e2 v2 →
    {{{ ▷ l ↦ᵢ v1 }}} CAS (Loc l) e1 e2 @ E
    {{{ RET (BoolV true); l ↦ᵢ v2 }}}.
  Proof.
    iIntros (<- <- Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
    iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
    iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
    iModIntro. iSplit=>//. by iApply "HΦ".
  Qed.

  Lemma wp_FAA E l m e2 k :
    IntoVal e2 (#nv k) →
    {{{ ▷ l ↦ᵢ (#nv m) }}} FAA (Loc l) e2 @ E
    {{{ RET (#nv m); l ↦ᵢ #nv (m + k) }}}.
  Proof.
    iIntros (<- Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 ????) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
    iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
    iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
    iModIntro. iSplit=>//. by iApply "HΦ".
  Qed.

  Lemma wp_fork E e Φ :
    ▷ (|={E}=> Φ UnitV) ∗ ▷ WP e {{ _, True }} ⊢ WP Fork e @ E {{ Φ }}.
  Proof.
    iIntros "[He HΦ]". iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1 ????) "Hσ !>"; iSplit; first by eauto.
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. by iFrame.
  Qed.

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_pure_exec :=
    unfold IntoVal in *;
    repeat match goal with H : AsVal _ |- _ => destruct H as [??] end; subst;
    intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_rec e1 e2 `{!AsVal e2} :
    PureExec True 1 (App (Rec e1) e2) e1.[(Rec e1), e2 /].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_lam e1 e2 `{!AsVal e2} :
    PureExec True 1 (App (Lam e1) e2) e1.[e2 /].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_LetIn e1 e2 `{!AsVal e1} :
    PureExec True 1 (LetIn e1 e2) e2.[e1 /].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_seq e1 e2 `{!AsVal e1} :
    PureExec True 1 (Seq e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_tlam e : PureExec True 1 (TApp (TLam e)) e.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_pack e1 `{!AsVal e1} e2:
    PureExec True 1 (UnpackIn (Pack e1) e2) e2.[e1/].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fold e `{!AsVal e}:
    PureExec True 1 (Unfold (Fold e)) e.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Fst (Pair e1 e2)) e1.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Snd (Pair e1 e2)) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjL e0) e1 e2) e1.[e0/].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inr e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjR e0) e1 e2) e2.[e0/].
  Proof. solve_pure_exec. Qed.

  Global Instance wp_if_true e1 e2 :
    PureExec True 1 (If (#♭ true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.

  Global Instance wp_if_false e1 e2 :
    PureExec True 1 (If (#♭ false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance wp_nat_binop op a b :
    PureExec True 1 (BinOp op (#n a) (#n b)) (of_val (binop_eval op a b)).
  Proof. solve_pure_exec. Qed.

End lang_rules.
