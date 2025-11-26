From Interpolation Require Import core unscoped Utils BasicAst ASExtra.
From Stdlib Require Import Relations Arith Lia Bool List.

Set Structural Injection.
Add Search Blacklist "_ind" "_sind" "_rec" "_rect".
Set Default Goal Selector "!".
Import ListNotations.

Fixpoint nth_error {A} (l : list A) (n : nat) : option A :=
  match l, n with
  | nil, _ => None
  | a :: _, 0 => Some a
  | _ :: l', S n' => nth_error l' n'
  end.

(** ** Evaluation *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : term -> term -> Prop :=
  | ST_Beta t1 v2 :
        tApp (tLam t1) v2 --> t1[v2..]
  | ST_Fun t1 t1' t2 :
         t1 --> t1' ->
         tApp t1 t2 --> tApp t1' t2
  | ST_Fst t t' : tFst (tPair t t') --> t
  | ST_Snd t t' : tSnd (tPair t t') --> t'
  | ST_Proj b t t' :
         t --> t' ->
         tProj b t --> tProj b t'

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (clos_refl_trans term step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Lemma ST_Fun_multi f f' u :
  f -->* f' ->
  tApp f u -->* tApp f' u.
Proof.
  intros Hred.
  induction Hred using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
Qed.

Lemma ST_Proj_multi b t t' :
  t -->* t' ->
  tProj b t -->* tProj b t'.
Proof.
  intros Hred.
  induction Hred using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
Qed.

(** ** Typing *)

Definition context := list type.

Declare Scope context_scope.
Delimit Scope context_scope with con.
Bind Scope context_scope with context.

Definition con_cons (Γ : context) (T : type) := cons T Γ.

Notation "Γ ,,, T" := (con_cons Γ T) (at level 50).

Definition in_context (n : nat) (Γ : context) (T : type) : Prop :=
  nth_error Γ n = Some T.

Lemma in_zero Γ T : in_context 0 (Γ,,,T) T.
Proof. reflexivity. Qed.

Hint Resolve in_zero : core.

Reserved Notation "Γ '|-' t '::' T"
  (at level 101, t at level 59).

Inductive has_type : context -> term -> type -> Prop :=
| T_Var Γ n T :
  in_context n Γ T ->
  Γ |- tVar n :: T

| T_Star Γ : (Γ |- tStar :: TUnit)

| T_Abs Γ A B t :
  (Γ ,,, A |- t :: B) ->
  Γ |- tLam t :: TFun A B

| T_App Γ A B f u :
  (Γ |- f :: TFun A B) ->
  (Γ |- u :: A) ->
  Γ |- tApp f u :: B

| T_Pair Γ A B a b :
  (Γ |- a :: A) ->
  (Γ |- b :: B) ->
  (Γ |- tPair a b :: TProd A B)

| T_Fst Γ A B t :
  (Γ |- t :: TProd A B) ->
  (Γ |- tFst t :: A)

| T_Snd Γ A B t :
  (Γ |- t :: TProd A B) ->
  (Γ |- tSnd t :: B)

where "Γ '|-' t '::' T" := (has_type Γ t T) (Γ in scope context_scope).

Hint Constructors has_type : core.

Lemma var_empty n T : ~ in_context n nil T.
Proof.
  unfold in_context ; cbn.
  discriminate.
Qed.

Hint Immediate var_empty : core.

(** ** Renamings and substitutions preserve types *)

Definition ren_has_type (Δ Γ : context) (r : ren) : Prop :=
  forall i T, in_context i Γ T -> in_context (r i) Δ T.

Lemma shift_has_type (Γ : context) (T : type) : ren_has_type (Γ,,,T) Γ ↑.
Proof.
  intros i T' H.
  cbn.
  unfold in_context.
  cbn.
  exact H.
Qed.

Lemma ren_lift_has_type (Δ Γ : context) (T : type) (r : ren) :
  ren_has_type Δ Γ r ->
  ren_has_type (Δ,,,T) (Γ,,,T) (up_ren r).
Proof.
  intros Hr i T' Hin.
  unfold ren_has_type, in_context in *.
  cbn.
  destruct i ; cbn ; eauto.
Qed.

Lemma ren_typing Δ Γ r t T :
  ren_has_type Δ Γ r ->
  (Γ |- t :: T) ->
  Δ |- t⟨r⟩ :: T.
Proof.
  intros Hr Ht.
  induction Ht in Δ, r, Hr ; cbn ; eauto using ren_lift_has_type.
Qed.

Definition subst_has_type (Δ Γ : context) (s : subst) : Prop :=
  forall i T, in_context i Γ T -> Δ |- s i :: T.

Lemma subst_cons_has_type (Δ Γ : context) (T : type) (σ : subst) (t : term) :
  subst_has_type Δ Γ σ ->
  (Δ |- t :: T) ->
  subst_has_type Δ (Γ,,,T) (t .: σ).
Proof.
  intros Hs Hty [] T' Hin ; cbn.
  - unfold in_context in Hin ; cbn in *.
    injection Hin ; subst.
    assumption.
  - apply Hs, Hin.
Qed.

Lemma id_subst_has_type (Γ : context) :
  subst_has_type Γ Γ tVar.
Proof.
  intros i T Hin ; cbn.
  induction Γ ; auto using var_empty.
Qed.

Lemma subst_one_has_type (Γ : context) (T : type) (t : term) :
  (Γ |- t :: T) -> 
  subst_has_type Γ (Γ,,,T) (t..).
Proof.
  apply subst_cons_has_type, id_subst_has_type.
Qed.

Lemma subst_lift_has_type (Δ Γ : context) (T : type) (s : subst) :
  subst_has_type Δ Γ s ->
  subst_has_type (Δ,,,T) (Γ,,,T) (⇑ s).
Proof.
  intros Hs.
  apply subst_cons_has_type ; eauto.
  intros i T' Hin ; cbn.
  eapply ren_typing ; eauto using shift_has_type.
Qed.

Lemma subst_typing Δ Γ s t T :
  subst_has_type Δ Γ s ->
  (Γ |- t :: T) ->
  Δ |- t[s] :: T.
Proof.
  intros Hr Ht.
  induction Ht in Δ, s, Hr ; cbn ; eauto using subst_lift_has_type.
Qed.

(** ** A certified type-checker *)

Fixpoint eqb_ty (T T' : type) : bool :=
  match T, T' with
  | TBase b, TBase b' => eqb_base b b'
  | TUnit, TUnit => true
  | TFun A B, TFun A' B' | TProd A B, TProd A' B' =>
    eqb_ty A A' && eqb_ty B B'
  | _, _ => false
  end.

Lemma eqb_ty_refl T : eqb_ty T T = true.
Proof.
  induction T ; cbn ; eauto.
  1: apply eqb_base_refl.
  all: rewrite IHT1 ; cbn ; assumption.
Qed.

Lemma eqb_ty_sound T T' : eqb_ty T T' = true -> T = T'.
Proof.
  induction T in T' |- * ; destruct T' ; cbn ; try solve [easy|congruence].
  1: now intros ->%eqb_base_sound.
  all: intros []%andb_prop ; now f_equal.
Qed.

Lemma eqb_ty_correct T T' : reflect (T = T') (eqb_ty T T').
Proof.
  destruct (eqb_ty T T') eqn:e.
  all: constructor.
  - now apply eqb_ty_sound.
  - intros ? ; subst.
    rewrite eqb_ty_refl in e.
    congruence.
Qed.