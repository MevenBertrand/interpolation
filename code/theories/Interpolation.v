From Interpolation Require Import Utils Syntax Notations Reduction Typing Bidir.
From Stdlib Require Import Relations Arith Lia Bool List RelationClasses.

(** ** Primitives for context splitting *)

Inductive side : Set := | source | target.

Inductive split : context -> context -> context -> Set :=
  | split_emp : split ε ε ε
  | split_s {Γ Γs Γt A} : split Γ Γs Γt -> split (Γ,,,A) (Γs,,,A) Γt
  | split_t {Γ Γs Γt A} : split Γ Γs Γt -> split (Γ,,,A) Γs (Γt,,,A).

Fixpoint find_side {Γ Γs Γt} (n : nat) (s : split Γ Γs Γt) : option side :=
  match n, s with
  | _, split_emp => None
  | 0, split_s _ => Some source
  | 0, split_t _ => Some target
  | S n', split_s s' | S n', split_t s' => find_side n' s'
  end.

Lemma in_context_find {Γ Γs Γt} (n : nat) (s : split Γ Γs Γt) T :
  in_context n Γ T ->
  find_side n s = None ->
  False.
Proof.
  induction s in n |- * ; [|destruct n | destruct n] ; cbn.
  - intros ; now eapply var_empty.
  - congruence.
  - intros Hin ?%IHs.
    1: easy.
    exact Hin.
  - congruence.
  - intros Hin ?%IHs.
    1: easy.
    exact Hin.
Qed.

Fixpoint flip_split {Γ Γs Γt} (s : split Γ Γs Γt) : split Γ Γt Γs :=
  match s with
  | split_emp => split_emp
  | split_s s => split_t (flip_split s)
  | split_t s => split_s (flip_split s)
  end.

Fixpoint split_ren_s {Γ Γs Γt} (s : split Γ Γs Γt) : ren :=
  match s with
  | split_emp => id
  | split_s s' => up_ren (split_ren_s s')
  | split_t s' => (split_ren_s s') >> ↑
  end.

Fixpoint split_ren_t {Γ Γs Γt} (s : split Γ Γs Γt) : ren :=
  match s with
  | split_emp => id
  | split_t s' => up_ren (split_ren_t s')
  | split_s s' => (split_ren_t s') >> ↑
  end.

Lemma flip_split_inv {Γ Γs Γt} (s : split Γ Γs Γt) :
  flip_split (flip_split s) = s.
Proof.
  induction s ; cbn.
  1: easy.
  all: now rewrite IHs.
Qed.

Lemma split_ren_s_flip {Γ Γs Γt} (s : split Γ Γs Γt) :
  split_ren_s (flip_split s) = split_ren_t s.
Proof.
  induction s ; cbn.
  1: easy.
  all: now rewrite IHs.
Qed.

Lemma split_ren_t_split {Γ Γs Γt} (s : split Γ Γs Γt) :
  split_ren_t (flip_split s) = split_ren_s s.
Proof.
  rewrite <- (flip_split_inv s) at 2.
  rewrite split_ren_s_flip.
  reflexivity.
Qed.

Lemma split_ren_s_ty {Γ Γs Γt} (s : split Γ Γs Γt) :
  Γ |- (split_ren_s s) :: Γs.
Proof.
  induction s ; cbn.
  - apply id_ren_has_type.
  - now apply ren_lift_has_type.
  - eapply ren_comp_has_type ; tea.
    apply shift_has_type.
Qed.

Lemma split_ren_t_ty {Γ Γs Γt} (s : split Γ Γs Γt) :
  Γ |- (split_ren_t s) :: Γt.
Proof.
  eapply ren_has_type_ext.
  2: eapply split_ren_s_ty.
  rewrite split_ren_s_flip.
  reflexivity.
Qed.

(** ** Atoms of a type/context *)

Fixpoint atoms_ty (p : polarity) (A : type) {struct A} : base -> Prop :=
  match A with
  | TBase b => if p then (sing b) else ∅
  | TUnit => ∅
  | TFun A B => atoms_ty (negp p) A ∪ atoms_ty p B
  | TProd A B => atoms_ty p A ∪ atoms_ty p B
  end.

Fixpoint atoms_ctx (p : polarity) (Γ : context) : base -> Prop :=
  match Γ with
  | nil => ∅
  | cons A Γ => atoms_ctx p Γ ∪ (atoms_ty p A)
  end.

Section Interpolation.

(** With the splitting of the context given by Γs and Γt and the type A,
  I is a valid interpolating type. *)
Definition interpolate_ty Γs Γt A M :=
  forall p, atoms_ty p M ⊆ (atoms_ctx p Γs) ∩ (atoms_ctx (negp p) Γt ∪ atoms_ty p A).

Definition interpolate_tm {Γ Γs Γt} (s : split Γ Γs Γt) M A t l r :=
  (Γs |- l :: M) /\ (Γt ,,, M |- r :: A) /\
  r⟨up_ren (split_ren_t s)⟩[l⟨split_ren_s s⟩..] ⤳* t.

Let Pcheck Γ T t := forall Γs Γt (s : split Γ Γs Γt),
  exists M l r,
    (forall p, atoms_ty p M ⊆ (atoms_ctx p Γs) ∩ (atoms_ctx (negp p) Γt ∪ atoms_ty p T)) /\ interpolate_tm s M T t l r.

Let Pinf Γ T t := forall Γs Γt (s : split Γ Γs Γt),
  (
    (forall p, atoms_ty p T ⊆ atoms_ctx (negp p) Γt) /\
    (exists M l r, 
      (forall p, atoms_ty p M ⊆ (atoms_ctx p Γs) ∩ (atoms_ctx (negp p) Γt)) /\
      interpolate_tm s M T t l r)
  ) \/ (
    (forall p, atoms_ty p T ⊆ atoms_ctx p Γs) /\
    (exists M l r, 
      (forall p, atoms_ty p M ⊆ (atoms_ctx (negp p) Γs) ∩ (atoms_ctx p Γt)) /\
      interpolate_tm (flip_split s) M T t l r)
  ).

Definition swap_var : ren :=
  fun n => match n with
  | 0 => 1
  | 1 => 0
  | n => n
  end.

Lemma swap_var_ty : forall Γ (A B : type),
  ((Γ,,,A),,,B) |- swap_var :: ((Γ,,,B),,,A).
Proof.
  intros Γ A B i T Hin.
  destruct i as [|[|i]] ; cbn in *.
  all: exact Hin.
Qed.

(* Hypothesis swap_var_eq : forall t u, t [u..] = t [swap_var] [⇑ (u..)]. *)

Theorem interpolation : bidir_concl Pcheck Pinf.
Proof.
  apply bidir_ind.
  - intros Γ Γs Γt s.
    exists TUnit, tStar, tStar.
    split.
    + intros ; cbn.
      intros ? [].
    + red.
      prod_splitter.
      all: solve [constructor].
  - intros Γ A B t _ IH Γs Γt s.
    destruct (IH Γs (Γt,,,A) (split_t s)) as (M&l&r&HM&Ht).
    exists M, l, (tLam (r⟨swap_var⟩)).
    split.
    (* the good-looking proof would do setoid rewriting with subset equivalence… *)
    + intros p b Hb.
      specialize (HM p b Hb).
      now cbn in *.
    + unfold interpolate_tm in * ; cbn in *.
      destruct Ht as (?&?&e).
      prod_splitter.
      1: easy.
      * constructor.
        eapply ren_typing ; [eassumption|].
        apply swap_var_ty.
      * apply R_Lam_cong.
        etransitivity ; tea.
        apply ereflexivity.
        substify.
        asimpl.
        apply ext_term.
        intros [|[|]] ; reflexivity.
  - intros Γ A B t t' _ IHA _ IHB Γs Γt s.
    destruct (IHA Γs Γt s) as (M & l & r & HM & Ht).
    destruct (IHB Γs Γt s) as (M' & l' & r' & HM' & Ht').
    exists (TProd M M'), (tPair l l'),
      (tPair (r[(tFst (tVar 0)).: (↑ >> tVar)]) (r'[(tSnd (tVar 0)) .: (↑ >> tVar)])).
    split.
    + intros p b [Hb|Hb'].
      1: specialize (HM p b Hb).
      2: specialize (HM' p b Hb').
      all: now cbn in *.
    + unfold interpolate_tm in * ; cbn in *.
      prod_splitter.
      1: now constructor.
      * constructor.
        all: eapply subst_typing ; [easy|].
        all: eapply subst_cons_has_type ; [|apply ren_subst_has_type, shift_has_type].
        all: repeat econstructor.
      * apply R_Pair_cong.
        all: etransitivity ; [|easy].
        -- substify.
           asimpl.
           apply R_subst ; try reflexivity.
           apply R_cons ; try reflexivity.
           do 2 constructor.
        -- substify.
           asimpl.
           apply R_subst ; try reflexivity.
           apply R_cons ; try reflexivity.
           do 2 constructor.
  - intros * _ IH -> ?? s.
    destruct (IH _ _ s) as [[? (M&l&r&[HM ?])]|[Hat (M&l&r&[HM ?])]] ; tea.
    + exists M, l, r ; split.
      2: easy.
      intros p b [?%HM Hb]%dup ; cbn in * ; easy.
    + exists (TFun M A), (tLam r), (tApp (tVar 0) l⟨↑⟩).
      split.
      * intros p b [[HΓ%HM Hb]%dup| HA] ; cbn in *.
        1: rewrite negp_inv in HΓ ; easy.
        split ; [|easy].
        now apply Hat.
      * unfold interpolate_tm in *.
        prod_splitter.
        1: now econstructor.
        1: econstructor ; [now econstructor|..] ; eapply ren_typing ; [easy|] ; now apply shift_has_type.
        cbn.
        etransitivity.
        1: constructor ; apply ST_Beta.
        etransitivity ; [|easy].
        rewrite split_ren_s_flip, split_ren_t_split.
        apply ereflexivity.
        substify.
        now asimpl.
  - intros ? n T Hin ?? s.
    destruct (find_side n s) as [[]|] eqn:e.
    3: exfalso ; now eauto using in_context_find.
    + admit.
    + admit.
  - admit.
  - admit.
  - admit.
Admitted.

End Interpolation.