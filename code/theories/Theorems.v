From Stdlib Require Import Relations Arith Lia Bool List RelationClasses.
From Interpolation Require Import Utils Syntax Languages Notations Reduction Equations Typing Bidir MetaTheory Interpolation.

(** The most precise result, stated using reduction *)
Corollary interpolation `{Lang} (A C : type) (t : term) (c : const_split) :
  ([A] ⊢ t :: C) ->
  exists B u r l,
    (forall p, atoms_ty p B ⊆
      (atoms_ty p A ∪ atoms_const p c.(pconst_l))
      ∩ (atoms_ty p C ∪ atoms_const (negp p) c.(pconst_r)))
    /\ ([A] ⊢ l :: B) /\ (atoms_tm l ⊆ c.(pconst_l))
    /\ ([B] ⊢ r :: C) /\ (atoms_tm r ⊆ c.(pconst_r))
    /\ (r[l..] ⤳* u) /\ t ⤳* u.
Proof.
  intros Ht.
  pose proof (normalisation _ _ _ Ht) as (u&?&Hnorm).
  assert (splits ([A]) ([A]) ε (split_s split_emp))
    by repeat constructor.
  destruct (interpolate (split_s split_emp) c ([A]) C u) as ((M&l)&r) eqn:e.
  exists M, u, r, l.
  prod_splitter.
  - eapply interpolation_lang_ty in Hnorm ; tea.
    rewrite e in Hnorm ; cbn in *.
    set_solver.
  - eapply interpolation_ty in Hnorm ; tea.
    now rewrite e in Hnorm.
  - eapply interpolation_lang_tm in Hnorm ; tea.
    now rewrite e in Hnorm.
  - eapply interpolation_ty in Hnorm ; tea.
    now rewrite e in Hnorm.
  - eapply interpolation_lang_tm in Hnorm ; tea.
    now rewrite e in Hnorm.
  - pose proof (Hnorm' := Hnorm). 
    eapply interpolation_red in Hnorm ; tea.
    eapply interpolation_ty in Hnorm' ; tea.
    rewrite e in Hnorm, Hnorm'.
    destruct Hnorm'.
    etransitivity ; tea.
    apply ereflexivity.
    substify ; asimpl ; refold.
    eapply term_ext_closed ; tea.
    intros [|] ? Hin ; cbv in Hin.
    2: cbv in Hin ; congruence.
    inversion Hin ; subst.
    cbn.
    asimpl ; refold.
    symmetry.
    apply subst_id.
    now intros [|].
  - assumption.
Qed.

(** A “model-theoretic” version, stated with equality with respect to an arbitrary theory *)
Corollary interpolation_eq `{Theory} (A C : type) (t : term) (c : const_split) :
  ([A] ⊢ t :: C) ->
  exists B r l,
    (forall p, atoms_ty p B ⊆
      (atoms_ty p A ∪ atoms_const p c.(pconst_l))
      ∩ (atoms_ty p C ∪ atoms_const (negp p) c.(pconst_r)))
    /\ ([A] ⊢ l :: B) /\ (atoms_tm l ⊆ c.(pconst_l))
    /\ ([B] ⊢ r :: C) /\ (atoms_tm r ⊆ c.(pconst_r))
    /\ ([A] ⊢ r[l..] ≡ t :: C).
Proof.
  intros Ht.
  epose proof Ht as Ht'.
  eapply interpolation in Ht' as (B&u&r&l&?&?&?&?&?&?&?).
  do 3 eexists ; prod_splitter ; eauto.
  transitivity u.
  - eauto using subject_reduction_conv with typing.
  - symmetry.
    eauto using subject_reduction_conv with typing.
Qed.

Section Empty.
  Context `{b : Base}.
  Existing Instances EmptyLang EmptyTheory.

  (** A simplified version for the empty theory *)
  Corollary interpolation_empty (A C : type) (t : term) :
    ([A] ⊢ t :: C) ->
    exists (B : type) (r l : term),
      (forall p, (atoms_ty p B) ⊆ (atoms_ty p A) ∩ (atoms_ty p C))
    /\ ([A] ⊢ l :: B) /\ ([B] ⊢ r :: C) /\ ([A] ⊢ r[l..] ≡ t :: C).
  Proof.
    unshelve eintros (?&?&?&?&?&?&?&?&?)%interpolation_eq.
    1:{
      unshelve econstructor ; cbn in *.
      1-2: exact ⊤.
      intros [].
    }
    cbn in *.
    do 3 eexists ; prod_splitter ; tea.
    assert (forall p, atoms_const p ⊤ ≡ ∅).
    {
      intros.
      unfold atoms_const.
      set_unfold.
      now intros ? [].
    }
    intros.
    set_solver.
  Qed.

End Empty.