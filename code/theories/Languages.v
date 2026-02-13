From Stdlib Require Import Relations Arith Lia Bool List RelationClasses.
From stdpp Require Import propset.
From Interpolation Require Import Utils Syntax.

(** ** Atoms of a type/context *)

Section AtomsTy.
  Context `{Ba : Base}.

  Fixpoint atoms_ty (p : polarity) (A : type) {struct A} : propset base :=
    match A with
    | TBase b => if p then {[b]} else ∅
    | TUnit | TEmp => ∅
    | TFun A B => atoms_ty (negp p) A ∪ atoms_ty p B
    | TProd A B | TSum A B => atoms_ty p A ∪ atoms_ty p B
    end.

  Fixpoint atoms_ctx (p : polarity) (Γ : context) : propset base :=
    match Γ with
    | nil => ∅
    | cons A Γ => atoms_ctx p Γ ∪ (atoms_ty p A)
    end.

  Lemma atoms_in n Γ T :
    in_context n Γ T ->
    (forall p, atoms_ty p T ⊆ atoms_ctx p Γ).
  Proof.
    intros H.
    unfold in_context in *.
    induction n in Γ, H |- * ; cbn.
    - destruct Γ ; cbn in * ; [congruence|].
      intros ? ? ?.
      set_solver.
    - destruct Γ ; cbn in * ; [congruence|].
      intros ?.
      set_solver.
  Qed.

End AtomsTy.

Section AtomsTm.
  Context `{Lang}.

  Definition atoms_const (p : polarity) (P : propset const) : propset base :=
    {[ b | exists c, (c ∈ P) /\ b ∈ atoms_ty p (const_type c) ]}.

  Record const_split :=
  {
    pconst_l : propset const ;
    pconst_r : propset const ;
    const_cover : forall c, (c ∈ pconst_l) + (c ∈ pconst_r) 
  }.

  Definition flip_csplit (s : const_split) := {|
    pconst_l := s.(pconst_r) ;
    pconst_r := s.(pconst_l) ;
    const_cover := (fun c => match (s.(const_cover) c) with | inl p => inr p | inr p => inl p end)
  |}.

  Fixpoint atoms_tm (t : term) {struct t} : propset const :=
    match t with
    | tConst c => {[c]}
    | tVar _ | tStar => ∅
    | tProj _ t | tLam t | tAbort t | tIn _ t => atoms_tm t
    | tPair t t' | tApp t t' => atoms_tm t ∪ atoms_tm t'
    | tIf s bl br => atoms_tm s ∪ atoms_tm bl ∪ atoms_tm br
    end.

  Lemma atoms_ren t ρ : atoms_tm (t⟨ρ⟩) ≡ atoms_tm t.
  Proof.
    set_unfold.
    intros c.
    induction t in ρ |- * ; cbn ; set_solver.
  Qed.

  Definition atoms_subst (σ : subst) : propset const :=
    {[ c | exists i, c ∈ atoms_tm (σ i) ]}.

  Instance atoms_subst_ext : Proper (pointwise_relation _ (=) ==> (≡)) atoms_subst.
  Proof.
    intros ?? e.
    unfold atoms_subst.
    set_unfold.
    intros c.
    now setoid_rewrite e.
  Qed.

  Lemma atoms_subst_ren ρ : atoms_subst (ρ >> ids) ≡ ∅.
  Proof.
    set_unfold.
    intros ? [] ; now cbn in *.
  Qed.
    
  Corollary atoms_subst_id : atoms_subst ids ≡ ∅.
  Proof.
    set_unfold.
    intros ? [] ; now cbn in *.
  Qed.

  Lemma atoms_subst_cons t σ : atoms_subst (t .: σ) ≡ (atoms_tm t) ∪ (atoms_subst σ).
  Proof.
    set_unfold.
    intros c.
    split.
    - intros [[|] ] ; cbn in * ; cbn.
      all: set_solver.
    - intros [|[]].
      1: exists 0.
      2: eexists (S _).
      all: cbn; set_solver.
  Qed.

  Corollary atoms_subst_tip f : atoms_subst (tip f) ≡ atoms_tm (f (tVar 0)).
  Proof.
    unfold tip.
    rewrite atoms_subst_cons, atoms_subst_ren.
    set_solver.
  Qed.

  Corollary atoms_subst_up (σ : subst) : atoms_subst (⇑ σ) ≡ atoms_subst σ.
  Proof.
    set_unfold.
    intros c.
    split.
    - intros [[|] Hin] ; cbn in * ; refold.
      1: exfalso ; now set_solver.
      eexists.
      now rewrite atoms_ren in Hin.
    - intros [].
      eexists (S _) ; cbn ; refold.
      now rewrite atoms_ren.
  Qed.

  Lemma atoms_tm_subst (t : term) (σ : subst) :
    atoms_tm (t[σ]) ⊆ atoms_tm t ∪ atoms_subst σ.
  Proof.
    induction t in σ |- * ; cbn.
    - unfold atoms_subst.
      set_unfold.
      intros.
      right.
      now eexists.
    - set_solver.
    - set_solver.
    - specialize (IHt1 σ).
      specialize (IHt2 σ).
      set_solver.
    - specialize (IHt σ).
      set_solver.
    - refold.
      specialize (IHt (⇑ σ)).
      rewrite atoms_subst_up in IHt.
      set_solver.
    - specialize (IHt1 σ).
      specialize (IHt2 σ).
      set_solver.
    - specialize (IHt σ).
      set_solver.
    - specialize (IHt σ).
      set_solver.
    - refold.
      specialize (IHt1 σ).
      specialize (IHt2 (⇑ σ)).
      specialize (IHt3 (⇑ σ)).
      rewrite atoms_subst_up in IHt2, IHt3.
      set_solver.
  Qed.

  Lemma atoms_tm_subst_inv (t : term) (σ : subst) :
    atoms_tm t ⊆ atoms_tm (t[σ]).
  Proof.
    induction t in σ |- * ; cbn ; set_solver.
  Qed.

  Lemma atoms_tm_subst_eq (t : term) (σ : subst) :
    atoms_subst σ ≡ ∅ ->
    atoms_tm t[σ] ≡ atoms_tm t.
  Proof.
    intros.
    pose proof (atoms_tm_subst t σ).
    pose proof (atoms_tm_subst_inv t σ).
    set_solver.
  Qed.

  Lemma atoms_subst_tip_eq t f :
    atoms_tm (f (tVar 0)) ≡ ∅ ->
    atoms_tm (t[tip f]) ≡ atoms_tm t.
  Proof.
    intros.
    apply atoms_tm_subst_eq.
    now rewrite atoms_subst_tip.
  Qed.

End AtomsTm.