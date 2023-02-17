From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Export tactics proofmode.
From WBLogrel.heap_lang Require Export derived_laws.
From iris.heap_lang Require Import notation.
From iris.prelude Require Import options.
Import uPred.

Lemma tac_wbwp_expr_eval `{!wbheapGS Σ} Δ E out Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WBWP e' @ out; E {{ Φ }}) → envs_entails Δ (WBWP e @ out; E {{ Φ }}).
Proof. by intros ->. Qed.

Tactic Notation "wbwp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    notypeclasses refine (tac_wbwp_expr_eval _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wbwp_expr_eval: not a 'wbwp'"
  end.
Ltac wbwp_expr_simpl := wbwp_expr_eval simpl.

Lemma tac_wbwp_pure `{!wbheapGS Σ} Δ Δ' E out K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WBWP (fill K e2) @ out; E {{ Φ }}) →
  envs_entails Δ (WBWP (fill K e1) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wbwp_pure_step_later //.
  iIntros "Hwp !> _" => //.
Qed.

Lemma tac_wbwp_pure_credit `{!wbheapGS Σ} Δ Δ' E out j K e1 e2 ϕ Φ :
  PureExec ϕ 1 e1 e2 →
  ϕ →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  match envs_app false (Esnoc Enil j (£ 1)) Δ' with
  | Some Δ'' =>
     envs_entails Δ'' (WBWP fill K e2 @ out; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WBWP (fill K e1) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ.
  pose proof @pure_exec_fill.
  rewrite -lifting.wbwp_pure_step_later; last done.
  rewrite into_laterN_env_sound /=. apply later_mono.
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  rewrite right_id. apply wand_intro_r. by rewrite wand_elim_l.
Qed.

Lemma tac_wbwp_value_nofupd `{!wbheapGS Σ} Δ E out Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WBWP (Val v) @ out; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by apply wbwp_value. Qed.

Lemma tac_wbwp_value `{!wbheapGS Σ} Δ E out (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WBWP (Val v) @ out; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by rewrite wbwp_value_fupd. Qed.

(** Simplify the goal if it is [WP] of a value.
  If the postcondition already allows a fupd, do not add a second one.
  But otherwise, *do* add a fupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac wbwp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wbwp ?E ?out (Val _) (λ _, wp _ ?E _ _)) =>
      eapply tac_wbwp_value_nofupd
  | |- envs_entails _ (wbwp ?E ?out (Val _) _) =>
      eapply tac_wp_value
  end.

Ltac wbwp_finish :=
  wbwp_expr_simpl;      (* simplify occurences of subst/fill *)
  try wbwp_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "wbwp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wbwp_pure _ _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |wbwp_finish                      (* new goal *)
      ])
    || fail "wbwp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wbwp_pure: not a 'wbwp'"
  end.
Tactic Notation "wbwp_pure" :=
  wbwp_pure _.

Tactic Notation "wbwp_pure" open_constr(efoc) "credit:" constr(H) :=
  iStartProof;
  let Htmp := iFresh in
  let finish _ :=
    pm_reduce;
    (iDestructHyp Htmp as H || fail 2 "wbwp_pure:" H "is not fresh");
    wp_finish
    in
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wbwp_pure_credit _ _ _ _ Htmp K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |finish ()                      (* new goal *)
      ])
    || fail "wbwp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wbwp_pure: not a 'wp'"
  end.
Tactic Notation "wbwp_pure" "credit:" constr(H) :=
  wbwp_pure _ credit: H.

(* TODO: do this in one go, without [repeat]. *)
Ltac wbwp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wbwp_pure _; [])
        | wbwp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
        ].

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "wbwp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  wbwp_pure (App _ _);
  clear H.

Tactic Notation "wbwp_if" := wbwp_pure (If _ _ _).
Tactic Notation "wbwp_if_true" := wbwp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "wbwp_if_false" := wbwp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "wbwp_unop" := wbwp_pure (UnOp _ _).
Tactic Notation "wbwp_binop" := wbwp_pure (BinOp _ _ _).
Tactic Notation "wbwp_op" := wbwp_unop || wbwp_binop.
Tactic Notation "wbwp_lam" := wbwp_rec.
Tactic Notation "wbwp_let" := wbwp_pure (Rec BAnon (BNamed _) _); wbwp_lam.
Tactic Notation "wbwp_seq" := wbwp_pure (Rec BAnon BAnon _); wbwp_lam.
Tactic Notation "wbwp_proj" := wbwp_pure (Fst _) || wbwp_pure (Snd _).
Tactic Notation "wbwp_case" := wbwp_pure (Case _ _ _).
Tactic Notation "wbwp_match" := wbwp_case; wp_pure (Rec _ _ _); wbwp_lam.
Tactic Notation "wbwp_inj" := wbwp_pure (InjL _) || wbwp_pure (InjR _).
Tactic Notation "wbwp_pair" := wbwp_pure (Pair _ _).
Tactic Notation "wbwp_closure" := wbwp_pure (Rec _ _ _).

Lemma tac_wbwp_bind `{!wbheapGS Σ} K Δ E out Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WBWP e @ out; E {{ v, WBWP f (Val v) @ out; E {{ Φ }} }})%I →
  envs_entails Δ (WBWP fill K e @ out; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: wbwp_bind. Qed.

Ltac wbwp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wbwp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wbwp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wbwp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

(** Heap tactics *)
Section heap.
Context `{!wbheapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.

Lemma tac_wbwp_allocN Δ Δ' E out j K v n Φ :
  (0 < n)%Z →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l,
    match envs_app false (Esnoc Enil j (array l (DfracOwn 1) (replicate (Z.to_nat n) v))) Δ' with
    | Some Δ'' =>
       envs_entails Δ'' (WBWP fill K (Val $ LitV $ LitLoc l) @ out; E {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WBWP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? ? HΔ.
  rewrite -wbwp_bind. eapply wand_apply; first exact: wbwp_allocN.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦∗ _)%I) right_id wand_elim_r.
Qed.

Lemma tac_wbwp_alloc Δ Δ' E out j K v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l,
    match envs_app false (Esnoc Enil j (l ↦ v)) Δ' with
    | Some Δ'' =>
       envs_entails Δ'' (WBWP fill K (Val $ LitV l) @ out; E {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WBWP fill K (Alloc (Val v)) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΔ.
  rewrite -wbwp_bind. eapply wand_apply; first exact: wbwp_alloc.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦ v)%I) right_id wand_elim_r.
Qed.

Lemma tac_wbwp_free Δ Δ' E out i K l v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  (let Δ'' := envs_delete false i false Δ' in
   envs_entails Δ'' (WBWP fill K (Val $ LitV LitUnit) @ out; E {{ Φ }})) →
  envs_entails Δ (WBWP fill K (Free (LitV l)) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? Hlk Hfin.
  rewrite -wbwp_bind. eapply wand_apply; first exact: wbwp_free.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  rewrite -Hfin wand_elim_r (envs_lookup_sound' _ _ _ _ _ Hlk).
  apply later_mono, sep_mono_r, wand_intro_r. rewrite right_id //.
Qed.

Lemma tac_wbwp_load Δ Δ' E out i K b l q v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (b, l ↦{q} v)%I →
  envs_entails Δ' (WBWP fill K (Val v) @ out; E {{ Φ }}) →
  envs_entails Δ (WBWP fill K (Load (LitV l)) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? Hi.
  rewrite -wbwp_bind. eapply wand_apply; first exact: wbwp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  apply later_mono.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
  * by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wbwp_store Δ Δ' E out i K l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' with
  | Some Δ'' => envs_entails Δ'' (WBWP fill K (Val $ LitV LitUnit) @ out; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WBWP fill K (Store (LitV l) (Val v')) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wbwp_bind. eapply wand_apply; first by eapply wbwp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wbwp_xchg Δ Δ' E out i K l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' with
  | Some Δ'' => envs_entails Δ'' (WBWP fill K (Val $ v) @ out; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WBWP fill K (Xchg (LitV l) (Val v')) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wbwp_bind. eapply wand_apply; first by eapply wbwp_xchg.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wbwp_cmpxchg Δ Δ' E out i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  vals_compare_safe v v1 →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' with
  | Some Δ'' =>
     v = v1 →
     envs_entails Δ'' (WBWP fill K (Val $ PairV v (LitV $ LitBool true)) @ out; E {{ Φ }})
  | None => False
  end →
  (v ≠ v1 →
   envs_entails Δ' (WBWP fill K (Val $ PairV v (LitV $ LitBool false)) @ out; E {{ Φ }})) →
  envs_entails Δ (WBWP fill K (CmpXchg (LitV l) (Val v1) (Val v2)) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? Hsuc Hfail.
  destruct (envs_simple_replace _ _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  destruct (decide (v = v1)) as [Heq|Hne].
  - rewrite -wbwp_bind. eapply wand_apply.
    { eapply wbwp_cmpxchg_suc; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_simple_replace_sound //; simpl.
    apply later_mono, sep_mono_r. rewrite right_id. apply wand_mono; auto.
  - rewrite -wbwp_bind. eapply wand_apply.
    { eapply wbwp_cmpxchg_fail; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_lookup_split //; simpl.
    apply later_mono, sep_mono_r. apply wand_mono; auto.
Qed.

Lemma tac_wbwp_cmpxchg_fail Δ Δ' E out i K l q v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  v ≠ v1 → vals_compare_safe v v1 →
  envs_entails Δ' (WBWP fill K (Val $ PairV v (LitV $ LitBool false)) @ out; E {{ Φ }}) →
  envs_entails Δ (WBWP fill K (CmpXchg (LitV l) v1 v2) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?????.
  rewrite -wbwp_bind. eapply wand_apply; first exact: wbwp_cmpxchg_fail.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wbwp_cmpxchg_suc Δ Δ' E out i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  v = v1 → vals_compare_safe v v1 →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' with
  | Some Δ'' =>
     envs_entails Δ'' (WBWP fill K (Val $ PairV v (LitV $ LitBool true)) @ out; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WBWP fill K (CmpXchg (LitV l) v1 v2) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?????; subst.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wbwp_bind. eapply wand_apply.
  { eapply wbwp_cmpxchg_suc; eauto. }
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wbwp_faa Δ Δ' E out i K l z1 z2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ LitV z1)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ LitV (LitInt (z1 + z2)))) Δ' with
  | Some Δ'' => envs_entails Δ'' (WBWP fill K (Val $ LitV z1) @ out; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WBWP fill K (FAA (LitV l) (LitV z2)) @ out; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wbwp_bind. eapply wand_apply; first exact: (wbwp_faa _ _ _ z1 z2).
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
End heap.

(** The tactic [wp_apply_core lem tac_suc tac_fail] evaluates [lem] to a
hypothesis [H] that can be applied, and then runs [wp_bind_core K; tac_suc H]
for every possible evaluation context [K].

- The tactic [tac_suc] should do [iApplyHyp H] to actually apply the hypothesis,
  but can perform other operations in addition (see [wp_apply] and [awp_apply]
  below).
- The tactic [tac_fail cont] is called when [tac_suc H] fails for all evaluation
  contexts [K], and can perform further operations before invoking [cont] to
  try again.

TC resolution of [lem] premises happens *after* [tac_suc H] got executed. *)
Ltac wbwp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         wbwp_bind_core K; tac_suc H)
     | _ => fail 1 "wbwp_apply: not a 'wp'"
     end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "wbwp_apply: cannot apply" lem ":" P ].

Tactic Notation "wbwp_apply" open_constr(lem) :=
  wbwp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wbwp_expr_simpl)
                    ltac:(fun cont => fail).
Tactic Notation "wbwp_smart_apply" open_constr(lem) :=
  wbwp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wbwp_expr_simpl)
                    ltac:(fun cont => wbwp_pure _; []; cont ()).

(* (** Tactic tailored for atomic triples: the first, simple one just runs *)
(* [iAuIntro] on the goal, as atomic triples always have an atomic update as their *)
(* premise. The second one additionaly does some framing: it gets rid of [Hs] from *)
(* the context, reducing clutter. You get them all back in the continuation of the *)
(* atomic operation. *) *)
(* Tactic Notation "awp_apply" open_constr(lem) := *)
(*   wp_apply_core lem ltac:(fun H => iApplyHyp H) ltac:(fun cont => fail); *)
(*   last iAuIntro. *)
(* Tactic Notation "awp_apply" open_constr(lem) "without" constr(Hs) := *)
(*   (* Convert "list of hypothesis" into specialization pattern. *) *)
(*   let Hs := words Hs in *)
(*   let Hs := eval vm_compute in (INamed <$> Hs) in *)
(*   wp_apply_core lem *)
(*     ltac:(fun H => *)
(*       iApply (wp_frame_wand with *)
(*         [SGoal $ SpecGoal GSpatial false [] Hs false]); [iAccu|iApplyHyp H]) *)
(*     ltac:(fun cont => fail); *)
(*   last iAuIntro. *)

Tactic Notation "wbwp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wbwp_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "wbwp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; wbwp_finish
    end in
  wbwp_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_wp_alloc] (respectively, [tac_twp_alloc]).
     If that fails, it tries to use the lemma [tac_wp_allocN]
     (respectively, [tac_twp_allocN]) for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦∗ [v] instead of
     l ↦ v for single references. These are logically equivalent assertions
     but are not equal. *)
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wbwp_alloc _ _ _ _ Htmp K))
          |fail 1 "wbwp_alloc: cannot find 'Alloc' in" e];
        [tc_solve
        |finish ()]
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wbwp_allocN _ _ _ _ Htmp K))
          |fail 1 "wbwp_alloc: cannot find 'Alloc' in" e];
        [idtac|tc_solve
         |finish ()]
    in (process_single ()) || (process_array ())
  | _ => fail "wbwp_alloc: not a 'wbwp'"
  end.

Tactic Notation "wbwp_alloc" ident(l) :=
  wbwp_alloc l as "?".

Tactic Notation "wbwp_free" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wbwp_free: cannot find" l "↦ ?" in
  wbwp_pures;
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wbwp_free _ _ _ _ _ K))
      |fail 1 "wbwp_free: cannot find 'Free' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reduce; wbwp_finish]
  | _ => fail "wbwp_free: not a 'wbwp'"
  end.

Tactic Notation "wbwp_load" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wbwp_load: cannot find" l "↦ ?" in
  wbwp_pures;
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wbwp_load _ _ _ _ _ K))
      |fail 1 "wbwp_load: cannot find 'Load' in" e];
    [tc_solve
    |solve_mapsto ()
    |wbwp_finish]
  | _ => fail "wbwp_load: not a 'wbwp'"
  end.

Tactic Notation "wbwp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wbwp_store: cannot find" l "↦ ?" in
  wbwp_pures;
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wbwp_store _ _ _ _ _ K))
      |fail 1 "wbwp_store: cannot find 'Store' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reduce; first [wbwp_seq|wbwp_finish]]
  | _ => fail "wbwp_store: not a 'wbwp'"
  end.

Tactic Notation "wbwp_xchg" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wbwp_xchg: cannot find" l "↦ ?" in
  wbwp_pures;
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wbwp_xchg _ _ _ _ _ K))
      |fail 1 "wbwp_xchg: cannot find 'Xchg' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reduce; first [wbwp_seq|wbwp_finish]]
  | _ => fail "wbwp_xchg: not a 'wbwp'"
  end.

Tactic Notation "wbwp_cmpxchg" "as" simple_intropattern(H1) "|" simple_intropattern(H2) :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wbwp_cmpxchg: cannot find" l "↦ ?" in
  wbwp_pures;
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wbwp_cmpxchg _ _ _ _ _ K))
      |fail 1 "wbwp_cmpxchg: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_mapsto ()
    |try solve_vals_compare_safe
    |pm_reduce; intros H1; wbwp_finish
    |intros H2; wbwp_finish]
  | _ => fail "wbwp_cmpxchg: not a 'wbwp'"
  end.

Tactic Notation "wbwp_cmpxchg_fail" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wbwp_cmpxchg_fail: cannot find" l "↦ ?" in
  wbwp_pures;
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wbwp_cmpxchg_fail _ _ _ _ _ K))
      |fail 1 "wbwp_cmpxchg_fail: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_mapsto ()
    |try (simpl; congruence) (* value inequality *)
    |try solve_vals_compare_safe
    |wbwp_finish]
  | _ => fail "wbwp_cmpxchg_fail: not a 'wbwp'"
  end.

Tactic Notation "wbwp_cmpxchg_suc" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wbwp_cmpxchg_suc: cannot find" l "↦ ?" in
  wbwp_pures;
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wbwp_cmpxchg_suc _ _ _ _ _ K))
      |fail 1 "wbwp_cmpxchg_suc: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_mapsto ()
    |try (simpl; congruence) (* value equality *)
    |try solve_vals_compare_safe
    |pm_reduce; wbwp_finish]
  | _ => fail "wbwp_cmpxchg_suc: not a 'wbwp'"
  end.

Tactic Notation "wbwp_faa" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wbwp_faa: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wbwp ?E ?out ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wbwp_faa _ _ _ _ _ K))
      |fail 1 "wbwp_faa: cannot find 'FAA' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reduce; wbwp_finish]
  | _ => fail "wbwp_faa: not a 'wbwp'"
  end.
