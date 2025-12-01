From Interpolation Require Import Utils Syntax Notations Reduction Typing Bidir.
From Stdlib Require Import Relations Arith Lia Bool List RelationClasses.

(** ** Primitives for context splitting *)

Inductive side : Set := | source | target.

Definition flip_side s := match s with | source => target | target => source end.

Inductive split : context -> context -> context -> Set :=
  | split_emp : split ε ε ε
  | split_s {Γ Γs Γt A} : split Γ Γs Γt -> split (Γ,,,A) (Γs,,,A) Γt
  | split_t {Γ Γs Γt A} : split Γ Γs Γt -> split (Γ,,,A) Γs (Γt,,,A).

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


Fixpoint find_side {Γ Γs Γt} (s : split Γ Γs Γt) (n : nat) : option side :=
  match s, n with
  | split_emp, _ => None
  | split_s _, 0 => Some source
  | split_t _, 0 => Some target
  | split_s s', S n' | split_t s', S n' => find_side s' n'
  end.

Lemma find_flip {Γ Γs Γt} (s : split Γ Γs Γt) (n : nat) :
  find_side (flip_split s) n = option_map flip_side (find_side s n).
Proof.
  induction s in n |- * ; cbn ; try easy.
  all: now destruct n ; cbn.
Qed.

Lemma in_context_find_none {Γ Γs Γt} (n : nat) (s : split Γ Γs Γt) T :
  in_context n Γ T ->
  find_side s n = None ->
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

Lemma find_side_some_l {Γ Γs Γt} (n : nat) (s : split Γ Γs Γt) :
  find_side s n = Some source ->
  {n' & {T & in_context n' Γs T /\ n = split_ren_s s n'}}.
Proof.
  intros Hside.
  induction s in n, Hside |- * ; [|destruct n | destruct n] ; cbn in *.
  - congruence.
  - eexists 0, _ ; split ; reflexivity.
  - edestruct IHs as (n'&e&[]) ; tea.
    subst.
    eexists (S n'),_ ; split ; cbn ; tea ; reflexivity.
  - congruence.
  - edestruct IHs as (n'&e&[]) ; tea.
    subst.
    eexists n',_ ; split ; cbn ; tea ; reflexivity.
Qed.

Lemma find_side_some_r {Γ Γs Γt} (n : nat) (s : split Γ Γs Γt) :
  find_side s n = Some target ->
  {n' & {T & in_context n' Γt T /\ n = split_ren_t s n'}}.
Proof.
  intros e.
  rewrite <- split_ren_s_flip.
  apply find_side_some_l.
  rewrite find_flip, e.
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

Lemma atoms_in n Γ T :
  in_context n Γ T ->
  (forall p, atoms_ty p T ⊆ atoms_ctx p Γ).
Proof.
  intros H.
  unfold in_context in *.
  induction n in Γ, H |- * ; cbn.
  - destruct Γ ; cbn in * ; [congruence|].
    intros ? ? ?.
    right.
    now congruence.
  - destruct Γ ; cbn in * ; [congruence|].
    intros ? ? ?.
    left.
    now apply IHn.
Qed.

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
    (forall p, atoms_ty p T ⊆ atoms_ctx p Γt) /\
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
  - (* case tStar *)
    intros Γ Γs Γt s.
    exists TUnit, tStar, tStar.
    split.
    + intros ; cbn.
      intros ? [].
    + red.
      prod_splitter.
      all: solve [constructor].
  - (* case tLam *)
    intros Γ A B t _ IH Γs Γt s.
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
  - (* case tPair *)
    intros Γ A B t t' _ IHA _ IHB Γs Γt s.
    destruct (IHA Γs Γt s) as (M & l & r & HM & Ht).
    destruct (IHB Γs Γt s) as (M' & l' & r' & HM' & Ht').
    exists (TProd M M'), (tPair l l'),
      (tPair (r[(tFst (tVar 0)).: (↑ >> ids)]) (r'[(tSnd (tVar 0)) .: (↑ >> ids)])).
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
  - (* case demote *)
    intros * _ IH -> ?? s.
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
  - (* case tVar *)
    intros ? n T Hin ?? s.
    destruct (find_side s n) as [[]|] eqn:e.
    3: exfalso ; now eauto using in_context_find_none.
    + right.
      apply find_side_some_l in e as (n'&A&[? ->]).
      eapply in_context_inj in Hin.
      2:now eapply split_ren_s_ty.
      subst.
      split.
      1: now eapply atoms_in.
      exists TUnit, tStar, (tVar (S n')).
      split.
      1: intros ? ? ? ; now cbn in *.
      unfold interpolate_tm.
      prod_splitter.
      * now constructor.
      * constructor ; assumption.
      * cbn.
        rewrite split_ren_t_split.
        reflexivity.
    + left.
      apply find_side_some_r in e as (n'&A&[? ->]).
      eapply in_context_inj in Hin.
      2:now eapply split_ren_t_ty.
      subst.
      split.
      1: now eapply atoms_in.
      exists TUnit, tStar, (tVar (S n')).
      split.
      1: intros ? ? ? ; now cbn in *.
      unfold interpolate_tm.
      prod_splitter.
      * now constructor.
      * constructor ; assumption.
      * reflexivity.
  - (* case tApp *)
    intros Γ A B n u _ Hn _ Hu Γs Γt s.
    destruct (Hn _ _ s) as [[IHpol (Mt&lt&rt&IHt)]|[IHpol (Mt&lt&rt&IHt)]].
    + left.
      cbn in *.
      specialize (Hu _ _ s) as (Mu&lu&ru&IHu).
      split.
      1: now intros ?? Hb ; eapply IHpol ; cbn.
      exists (TProd Mt Mu), (tPair lt lu),
        (tApp (rt[(tFst (tVar 0)).: (↑ >> ids)]) (ru[(tSnd (tVar 0)) .: (↑ >> ids)])).
      cbn.
      split.
      * intros ? b ? ; cbn in *.
        destruct IHt as [IHt _], IHu as [IHu _].
        specialize (IHt p b).
        specialize (IHu p b).
        specialize (IHpol (negp p) b).
        rewrite negp_inv in IHpol.
        cbn in *.
        easy.
      * unfold interpolate_tm in *.
        prod_splitter.
        -- now constructor.
        -- econstructor ; eapply subst_typing ; try easy.
           all: apply subst_cons_has_type ; [now repeat econstructor|].
           all: apply ren_subst_has_type, shift_has_type.
        -- cbn.
           apply R_App_cong.
           all: etransitivity ; [|easy].
           all: substify ; cbn.
           all: asimpl ; refold.
           all: apply R_subst ; [|reflexivity].
           all: intros [|] ; cbn ; [|easy].
           all: now do 2 econstructor.
    + right.
      cbn in *.
      specialize (Hu _ _ (flip_split s)) as (Mu&lu&ru&IHu).
      split.
      1: now intros ?? Hb ; eapply IHpol ; cbn.
      exists (TProd Mt Mu), (tPair lt lu),
        (tApp (rt[(tFst (tVar 0)).: (↑ >> ids)]) (ru[(tSnd (tVar 0)) .: (↑ >> ids)])).
      cbn.
      split.
      * intros ? b ? ; cbn in *.
        destruct IHt as [IHt _], IHu as [IHu _].
        specialize (IHt p b).
        specialize (IHu p b).
        specialize (IHpol (negp p) b).
        rewrite negp_inv in IHpol.
        cbn in *.
        easy.
      * unfold interpolate_tm in *.
        prod_splitter.
        -- now constructor.
        -- econstructor ; eapply subst_typing ; try easy.
           all: apply subst_cons_has_type ; [now repeat econstructor|].
           all: apply ren_subst_has_type, shift_has_type.
        -- cbn.
           apply R_App_cong.
           all: etransitivity ; [|easy].
           all: substify ; cbn.
           all: asimpl ; refold.
           all: apply R_subst ; [|reflexivity].
           all: intros [|] ; cbn ; [|easy].
           all: now do 2 econstructor.
  - (* case tProj *)
    intros * _ IH Γs Γt s.
    destruct (IH _ _ s) as [[IHb (M&l&r&Htm)]|[IHb (M&l&r&Htm)]].
    + left.
      split.
      * intros p.
        destruct b.
        all: intros b Hb ; apply IHb.
        all: now cbn.
      * exists M, l, (tProj b r).
        split ; [easy|].
        unfold interpolate_tm in * ; prod_splitter ; try easy.
        1: destruct b ; cbn ; now econstructor.
        cbn.
        apply R_Proj_cong ; try reflexivity.
        apply Htm.
    + right.
      split.
      * intros p.
        destruct b.
        all: intros b Hb ; apply IHb.
        all: now cbn.
      * exists M, l, (tProj b r).
        split ; [easy|].
        unfold interpolate_tm in * ; prod_splitter ; try easy.
        1: destruct b ; cbn ; now econstructor.
        cbn.
        apply R_Proj_cong ; try reflexivity.
        apply Htm.
Qed.

End Interpolation.