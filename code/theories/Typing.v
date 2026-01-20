From Stdlib Require Import Relations Arith Lia Bool List
  Relation_Definitions Morphisms RelationClasses.
From Interpolation Require Import Utils Syntax Notations Reduction.

Set Structural Injection.
Add Search Blacklist "_ind" "_sind" "_rec" "_rect".
Set Default Goal Selector "!".
Import ListNotations.

Section Typing.
  Close Scope typing_scope.

  Inductive has_type : context -> type -> term -> Prop :=
  | T_Var Γ n T :
    in_context n Γ T ->
    Γ |- tVar n :: T

  | T_Star Γ : (Γ |- tStar :: TUnit)

  | T_Lam Γ A B t :
    (Γ ,, A |- t :: B) ->
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

  | T_Abort Γ A t :
    (Γ |- t :: TEmp) ->
    (Γ |- tAbort t :: A)

  | T_Left Γ A B t :
    (Γ |- t :: A) ->
    (Γ |- tLeft t :: TSum A B)

  | T_Right Γ A B t :
    (Γ |- t :: B) ->
    (Γ |- tRight t :: TSum A B)

  | T_If Γ A B T s bl br :
    (Γ |- s :: TSum A B) ->
    (Γ,,A |- bl :: T) ->
    (Γ,,B |- br :: T) ->
    (Γ |- tIf s bl br :: T)

  where "Γ '|-' t '::' T" := (has_type Γ T t) (Γ in scope context_scope).

End Typing.

Hint Constructors has_type : core.

#[export] Instance HasTypingTm : HasTyping context type term := has_type.

#[export] Instance HasTypingRen : HasTyping context context ren :=
  fun (Δ Γ : context) (r : ren) =>
  forall i T, in_context i Γ T -> in_context (r i) Δ T.

#[export] Instance HasTypingSubst : HasTyping context context subst :=
 fun (Δ Γ : context) (s : subst) =>
  forall i T, in_context i Γ T -> Δ |- s i :: T.

Ltac fold_typing := change has_type with (typing (Ctx := context) (Ty := type) (Obj := term)) in *.

Smpl Add fold_typing : refold.

Lemma var_empty n T : ~ in_context n ε T.
Proof.
  unfold in_context ; cbn.
  discriminate.
Qed.

Hint Immediate var_empty : core.

(** ** Renamings and substitutions preserve types *)


Lemma shift_has_type (Γ : context) (T : type) : (Γ,,T) |- ↑ :: Γ.
Proof.
  intros ? ** ; assumption.
Qed.

Lemma ren_lift_has_type (Δ Γ : context) (T : type) (r : ren) :
  (Δ |- r :: Γ) ->
  (Δ,,T) |- (up_ren r) ::  (Γ,,T).
Proof.
  intros Hr i T' Hin.
  unfold typing, HasTypingRen, in_context in *.
  now destruct i ; cbn.
Qed.

Lemma ren_typing (Δ Γ : context) (T : type) (t : term) (r : ren) :
  (Γ |- t :: T) ->
  (Δ |- r :: Γ) ->
  Δ |- t⟨r⟩ :: T.
Proof.
  intros Ht Hr.
  induction Ht in Δ, r, Hr ; cbn ; econstructor ; eauto using ren_lift_has_type.
Qed.

Lemma id_ren_has_type (Δ : context) :
  Δ |- id :: Δ.
Proof.
  now intros i T Hin ; cbn.
Qed.

Lemma ren_comp_has_type (Δ Γ Θ : context) (r r' : ren) :
  (Δ |- r :: Γ) ->
  (Γ |- r' :: Θ) ->
  (Δ |- (r' >> r) :: Θ).
Proof.
  intros * Hr Hr' i T Hin.
  apply Hr', Hr in Hin.
  assumption.
Qed.

Instance ren_has_type_ext (Δ Γ : context) :
  Proper ((pointwise_relation _ eq) ==> iff) (typing (Obj := ren) Δ Γ).
Proof.
  intros ?? Hren. 
  split ; intros e i T Hin.
  1: rewrite <- Hren.
  2: rewrite Hren.
  all: now apply e.
Qed.

Instance subst_has_type_ext (Δ Γ : context) :
  Proper ((pointwise_relation _ eq) ==> iff) (typing (Obj := subst) Δ Γ).
Proof.
  intros ?? Hsubst. 
  split ; intros e i T Hin.
  1: rewrite <- Hsubst.
  2: rewrite Hsubst.
  all: now apply e.
Qed.

Lemma subst_cons_has_type (Δ Γ : context) (T : type) (σ : subst) (t : term) :
  (Δ |- t :: T) ->
  (Δ |- σ :: Γ) ->
  Δ |- (t .: σ) :: (Γ,,T).
Proof.
  intros Hty Hs [] T' Hin ; cbn.
  - unfold in_context in Hin ; cbn in *.
    injection Hin ; subst.
    assumption.
  - apply Hs, Hin.
Qed.

Lemma ren_subst_has_type (Δ Γ : context) r :
  (Δ |- r :: Γ) ->
  (Δ |- (r >> ids) :: Γ).
Proof.
  intros Hr i T Hin ; cbn.
  constructor.
  now apply Hr.
Qed.

Lemma id_subst_has_type (Γ : context) :
  Γ |- ids :: Γ.
Proof.
  eapply subst_has_type_ext.
  1: reflexivity.
  apply ren_subst_has_type, id_ren_has_type.
Qed.

Lemma subst_one_has_type (Γ : context) (T : type) (t : term) :
  (Γ |- t :: T) -> 
  Γ |- (t..) ::  (Γ,,T).
Proof.
  intros.
  now apply subst_cons_has_type, id_subst_has_type.
Qed.

Lemma subst_lift_has_type (Δ Γ : context) (T : type) (σ : subst) :
  (Δ |- σ :: Γ) ->
  (Δ,,T) |- (⇑ σ) ::  (Γ,,T).
Proof.
  intros Hs.
  apply subst_cons_has_type.
  1: now econstructor.
  intros i T' Hin ; cbn.
  eapply ren_typing ; eauto using shift_has_type.
Qed.

Lemma subst_typing (Δ Γ : context) t T (σ : subst) :
  (Γ |- t :: T) ->
  (Δ |- σ :: Γ) ->
  Δ |- t[σ] :: T.
Proof.
  intros Ht Hσ.
  induction Ht in Δ, σ, Hσ ; cbn ; eauto using subst_lift_has_type.
  all: econstructor ; eauto using subst_lift_has_type.
Qed.

Lemma subst_comp_has_type (Δ Γ Θ : context) (σ σ' : subst) :
  (Δ |- σ :: Γ) ->
  (Γ |- σ' :: Θ) ->
  (Δ |- (σ' >> (subst_term σ)) :: Θ).
Proof.
  intros * Hσ Hσ' i T Hin ; cbn ; refold.
  eapply subst_typing ; tea.
  now apply Hσ'.
Qed.

Lemma tip_has_type (Γ : context) (A B : type) (f : term -> term) :
  (Γ,,A |- f (tVar 0) :: B) ->
  (Γ,,A |- tip f :: Γ,,B).
Proof.
  unfold tip.
  intros.
  apply subst_cons_has_type, ren_subst_has_type, shift_has_type.
  assumption.
Qed.

Lemma swap_var_ty Γ (A B : type) :
  ((Γ,,A),,B) |- swap_var :: ((Γ,,B),,A).
Proof.
  intros i T Hin.
  destruct i as [|[|i]] ; cbn in *.
  all: exact Hin.
Qed.

(** ** Types have decidable equality *)

Fixpoint eqb_ty (T T' : type) : bool :=
  match T, T' with
  | TBase b, TBase b' => eqb_base b b'
  | TUnit, TUnit | TEmp, TEmp => true
  | TFun A B, TFun A' B' | TProd A B, TProd A' B' | TSum A B, TSum A' B' =>
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