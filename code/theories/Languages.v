(** * Interpolation.Languages: definition and properties of the atoms/constants of a type, context, term *)
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

  (** Atoms of a set of constants *)
Definition atoms_const `{Lang} (p : polarity) (P : propset const) : propset base :=
  {[ b | exists c, (c ∈ P) /\ b ∈ atoms_ty p (const_type c) ]}.

(** ** Constants of a term *)

Section ConstantTm.
  Context `{Lang}.

  (** *** Splitting of a constant set *)
  (** It is not necessary for the splitting to be non-overlapping, however it
    needs to be relevant to compute the interpolant *)
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

  (** *** Constants in a term *)
  Fixpoint const_tm (t : term) {struct t} : propset const :=
    match t with
    | tConst c => {[c]}
    | tVar _ | tStar => ∅
    | tProj _ t | tLam t | tAbort t | tIn _ t => const_tm t
    | tPair t t' | tApp t t' => const_tm t ∪ const_tm t'
    | tIf s bl br => const_tm s ∪ const_tm bl ∪ const_tm br
    end.

  (** *** Interaction of this with renamings and substitutions *)

  Lemma const_ren t ρ : const_tm (t⟨ρ⟩) ≡ const_tm t.
  Proof.
    set_unfold.
    intros c.
    induction t in ρ |- * ; cbn ; set_solver.
  Qed.

  Definition const_subst (σ : subst) : propset const :=
    {[ c | exists i, c ∈ const_tm (σ i) ]}.

  Instance const_subst_ext : Proper (pointwise_relation _ (=) ==> (≡)) const_subst.
  Proof.
    intros ?? e.
    unfold const_subst.
    set_unfold.
    intros c.
    now setoid_rewrite e.
  Qed.

  Lemma const_subst_ren ρ : const_subst (ρ >> ids) ≡ ∅.
  Proof.
    set_unfold.
    intros ? [] ; now cbn in *.
  Qed.
    
  Corollary const_subst_id : const_subst ids ≡ ∅.
  Proof.
    set_unfold.
    intros ? [] ; now cbn in *.
  Qed.

  Lemma const_subst_cons t σ : const_subst (t .: σ) ≡ (const_tm t) ∪ (const_subst σ).
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

  Corollary const_subst_tip f : const_subst (tip f) ≡ const_tm (f (tVar 0)).
  Proof.
    unfold tip.
    rewrite const_subst_cons, const_subst_ren.
    set_solver.
  Qed.

  Corollary const_subst_up (σ : subst) : const_subst (⇑ σ) ≡ const_subst σ.
  Proof.
    set_unfold.
    intros c.
    split.
    - intros [[|] Hin] ; cbn in * ; refold.
      1: exfalso ; now set_solver.
      eexists.
      now rewrite const_ren in Hin.
    - intros [].
      eexists (S _) ; cbn ; refold.
      now rewrite const_ren.
  Qed.

  Lemma const_tm_subst (t : term) (σ : subst) :
    const_tm (t[σ]) ⊆ const_tm t ∪ const_subst σ.
  Proof.
    induction t in σ |- * ; cbn.
    - unfold const_subst.
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
      rewrite const_subst_up in IHt.
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
      rewrite const_subst_up in IHt2, IHt3.
      set_solver.
  Qed.

  Lemma const_tm_subst_inv (t : term) (σ : subst) :
    const_tm t ⊆ const_tm (t[σ]).
  Proof.
    induction t in σ |- * ; cbn ; set_solver.
  Qed.

  Lemma const_tm_subst_eq (t : term) (σ : subst) :
    const_subst σ ≡ ∅ ->
    const_tm t[σ] ≡ const_tm t.
  Proof.
    intros.
    pose proof (const_tm_subst t σ).
    pose proof (const_tm_subst_inv t σ).
    set_solver.
  Qed.

  Lemma const_subst_tip_eq t f :
    const_tm (f (tVar 0)) ≡ ∅ ->
    const_tm (t[tip f]) ≡ const_tm t.
  Proof.
    intros.
    apply const_tm_subst_eq.
    now rewrite const_subst_tip.
  Qed.

End ConstantTm.