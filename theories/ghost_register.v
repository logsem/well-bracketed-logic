From iris.algebra Require Import auth gmap agree frac.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import adequacy notation proofmode.
From iris.bi.lib Require Import fractional.
From iris.staging.algebra Require Import monotone.


Definition ghost_id := positive.

Definition ghost_reg := gmap ghost_id gname.

Definition ghost_regUR := gmapUR ghost_id (prodR fracR (agreeR gnameO)).

Class ghost_regG Σ := {ghost_reg_inG :> inG Σ (authUR ghost_regUR); ghost_reg_name : gname}.

Definition ghost_regΣ := #[GFunctor (authUR ghost_regUR)].

Global Instance ghost_map_subΣ_inG Σ : subG ghost_regΣ Σ → inG Σ (authUR ghost_regUR).
Proof. solve_inG. Qed.

Section named_ghost.
  Context `{!ghost_regG Σ}.

  Definition ghost_reg_full (M : ghost_reg) : iProp Σ :=
    own ghost_reg_name (● ((λ x : gname, (1%Qp, to_agree x)) <$> M : ghost_regUR)).

  Definition named_ghost (id : ghost_id) (q : Qp) (name : gname) : iProp Σ :=
    own ghost_reg_name (◯ {[id := (q, to_agree name) ]}).

  Typeclasses Opaque named_ghost ghost_reg_full.

  Global Instance ghost_reg_Timeless id q name : Timeless (named_ghost id q name).
  Proof. rewrite /named_ghost; apply _. Qed.

  Global Instance ghost_reg_full_Timeless M : Timeless (ghost_reg_full M).
  Proof. rewrite /ghost_reg_full; apply _. Qed.

  Global Instance named_ghost_Fractional id name : Fractional (λ q, named_ghost id q name).
  Proof.
    intros p q.
    rewrite /named_ghost -own_op -auth_frag_op gmap_op.
    do 2 f_equiv.
    apply map_equiv_iff.
    intros j.
    destruct (decide (j = id)) as [->|].
    - rewrite lookup_merge !lookup_insert /= -Some_op -pair_op /= agree_idemp //.
    - rewrite lookup_merge !lookup_insert_ne //.
  Qed.

  Global Instance named_ghost_as_fractional id q name :
    AsFractional (named_ghost id q name) (λ q, named_ghost id q name) q.
  Proof. by constructor; last apply _. Qed.

  Lemma named_ghost_agree M id q name :
    ghost_reg_full M -∗ named_ghost id q name -∗ ⌜M !! id = Some name⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hvl _]%auth_both_valid_discrete; iPureIntro.
    apply singleton_included_l in Hvl as ([p n] & Hpn1 & Hpn2).
    apply Some_included in Hpn2.
    destruct Hpn2 as [[Hpn21 Hpn22]|Hpn2]; simpl in *.
    - setoid_subst.
      rewrite lookup_fmap in Hpn1.
      revert Hpn1; case: (M !! id); simpl; last by inversion 1.
      intros ? [? ->%to_agree_inj%leibniz_equiv]%Some_equiv_inj; done.
    - apply pair_included in Hpn2 as [_ Hpn2].
      rewrite lookup_fmap in Hpn1.
      revert Hpn1; case: (M !! id); simpl; last by inversion 1.
      intros ? [? ?]%Some_equiv_inj; simpl in *; setoid_subst.
      apply to_agree_included, leibniz_equiv in Hpn2 as ->; done.
  Qed.

  Lemma named_ghost_update M id name name':
    ghost_reg_full M -∗ named_ghost id 1%Qp name ==∗
    ghost_reg_full (<[id := name']>M) ∗ named_ghost id 1%Qp name'.
  Proof.
    rewrite /ghost_reg_full /named_ghost.
    iIntros "H1 H2".
    iMod (own_update_2
            _ _ _ (● ((λ x : gname, (1%Qp, to_agree x)) <$> <[id := name']>M : ghost_regUR) ⋅
                     ◯ {[id := (1%Qp, to_agree name') ]}) with "H1 H2") as "[$ $]"; last done.
    apply auth_update.
    rewrite fmap_insert.
    apply singleton_local_update_any.
    intros ? ?. apply exclusive_local_update; done.
  Qed.

  Lemma res_name_alloc M name :
    ghost_reg_full M ==∗
    ∃ id, ⌜id ∉ dom (gset ghost_id) M⌝ ∗ ghost_reg_full (<[id := name]>M) ∗ named_ghost id 1%Qp name.
  Proof.
    rewrite /ghost_reg_full /named_ghost.
    set (id := fresh (dom (gset ghost_id) M)).
    iIntros "H".
    iMod (own_update
            _ _ (● ((λ x : gname, (1%Qp, to_agree x)) <$> <[id := name]>M : ghost_regUR) ⋅
                   ◯ {[id := (1%Qp, to_agree name) ]}) with "H") as "[? ?]".
    - apply auth_update_alloc.
      rewrite fmap_insert.
      apply alloc_singleton_local_update; last done.
      rewrite -(not_elem_of_dom (D := gset ghost_id)) dom_fmap.
      apply is_fresh.
    - iModIntro; iExists _; iFrame.
      iPureIntro. apply is_fresh.
  Qed.

End named_ghost.

Lemma ghost_reg_init `{!inG Σ (authUR ghost_regUR)}: ⊢ |==> ∃ _ : ghost_regG Σ, ghost_reg_full ∅.
Proof.
  iMod own_alloc as (γ) "Hγ"; last by iModIntro; iExists {|ghost_reg_name := γ|}.
  rewrite fmap_empty; apply auth_auth_valid; done.
Qed.
