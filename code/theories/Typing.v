From Stdlib Require Import Relations Arith Lia Bool List
  Relation_Definitions Morphisms RelationClasses.
From Interpolation Require Import Utils Syntax Notations Reduction.

Set Structural Injection.
Add Search Blacklist "_ind" "_sind" "_rec" "_rect".
Set Default Goal Selector "!".
Import ListNotations.

Create HintDb typing discriminated. 

Section Typing.
  Close Scope typing_scope.

  Inductive has_type : context -> type -> term -> Prop :=
  | _T_Var Γ n T :
    in_context n Γ T ->
    Γ ⊢ tVar n :: T

  | _T_Star Γ : (Γ ⊢ tStar :: TUnit)

  | _T_Lam Γ A B t :
    (Γ ,, A ⊢ t :: B) ->
    Γ ⊢ tLam t :: TFun A B

  | _T_App Γ A B f u :
    (Γ ⊢ f :: TFun A B) ->
    (Γ ⊢ u :: A) ->
    Γ ⊢ tApp f u :: B

  | _T_Pair Γ A B a b :
    (Γ ⊢ a :: A) ->
    (Γ ⊢ b :: B) ->
    (Γ ⊢ tPair a b :: TProd A B)

  | _T_Fst Γ A B t :
    (Γ ⊢ t :: TProd A B) ->
    (Γ ⊢ tFst t :: A)

  | _T_Snd Γ A B t :
    (Γ ⊢ t :: TProd A B) ->
    (Γ ⊢ tSnd t :: B)

  | _T_Abort Γ A t :
    (Γ ⊢ t :: TEmp) ->
    (Γ ⊢ tAbort t :: A)

  | _T_Left Γ A B t :
    (Γ ⊢ t :: A) ->
    (Γ ⊢ tLeft t :: TSum A B)

  | _T_Right Γ A B t :
    (Γ ⊢ t :: B) ->
    (Γ ⊢ tRight t :: TSum A B)

  | _T_If Γ A B T s bl br :
    (Γ ⊢ s :: TSum A B) ->
    (Γ,,A ⊢ bl :: T) ->
    (Γ,,B ⊢ br :: T) ->
    (Γ ⊢ tIf s bl br :: T)

  where "Γ '⊢' t '::' T" := (has_type Γ T t) (Γ in scope context_scope).

End Typing.

#[export] Instance HasTypingTm : HasTyping context type term := has_type.

#[export] Instance HasTypingRen : HasTyping context context ren :=
  fun (Δ Γ : context) (r : ren) =>
  forall i T, in_context i Γ T -> in_context (r i) Δ T.

#[export] Instance HasTypingSubst : HasTyping context context subst :=
 fun (Δ Γ : context) (s : subst) =>
  forall i T, in_context i Γ T -> Δ ⊢ s i :: T.

Ltac fold_typing := change has_type with (typing (Ctx := context) (Ty := type) (Obj := term)) in *.

Smpl Add fold_typing : refold.

Lemma T_Var Γ n T :
    in_context n Γ T ->
    Γ ⊢ tVar n :: T.
Proof ltac:(now constructor).

Lemma T_Star Γ : (Γ ⊢ tStar :: TUnit).
Proof ltac:(now constructor).

Lemma T_Lam Γ A B t :
    (Γ ,, A ⊢ t :: B) ->
    Γ ⊢ tLam t :: TFun A B.
Proof ltac:(now constructor).

Lemma T_App Γ A B f u :
    (Γ ⊢ f :: TFun A B) ->
    (Γ ⊢ u :: A) ->
    Γ ⊢ tApp f u :: B.
Proof ltac:(now econstructor).

Lemma T_Pair Γ A B a b :
    (Γ ⊢ a :: A) ->
    (Γ ⊢ b :: B) ->
    (Γ ⊢ tPair a b :: TProd A B).
Proof ltac:(now constructor).

Lemma T_Fst Γ A B t :
    (Γ ⊢ t :: TProd A B) ->
    (Γ ⊢ tFst t :: A).
Proof ltac:(now econstructor).

Lemma T_Snd Γ A B t :
    (Γ ⊢ t :: TProd A B) ->
    (Γ ⊢ tSnd t :: B).
Proof ltac:(now econstructor).

Lemma T_Abort Γ A t :
    (Γ ⊢ t :: TEmp) ->
    (Γ ⊢ tAbort t :: A).
Proof ltac:(now constructor).

Lemma T_Left Γ A B t :
    (Γ ⊢ t :: A) ->
    (Γ ⊢ tLeft t :: TSum A B).
Proof ltac:(now constructor).

Lemma T_Right Γ A B t :
    (Γ ⊢ t :: B) ->
    (Γ ⊢ tRight t :: TSum A B).
Proof ltac:(now constructor).

Lemma T_If Γ A B T s bl br :
    (Γ ⊢ s :: TSum A B) ->
    (Γ,,A ⊢ bl :: T) ->
    (Γ,,B ⊢ br :: T) ->
    (Γ ⊢ tIf s bl br :: T).
Proof ltac:(now econstructor).

Hint Resolve T_Var T_Star T_Lam T_App T_Pair T_Fst T_Snd T_Abort T_Left T_Right T_If : typing.

Lemma var_empty n T : ~ in_context n ε T.
Proof.
  unfold in_context ; cbn.
  discriminate.
Qed.

Hint Extern 0 (False) => (eapply var_empty) : typing.

Hint Extern 0 (in_context _ _ _) => reflexivity : typing.

(** ** Typing for renamings and substitutions *)

(** Not in the [typing] hint database because it is too wild, needs to be applied directly *)
Instance ren_has_type_ext (Δ Γ : context) :
  Proper ((pointwise_relation _ eq) ==> iff) (typing (Obj := ren) Δ Γ).
Proof.
  intros ?? Hren. 
  split ; intros e i T Hin.
  1: rewrite <- Hren.
  2: rewrite Hren.
  all: now apply e.
Qed.

Lemma ren_id_has_type (Δ : context) :
  Δ ⊢ id :: Δ.
Proof.
  now intros i T Hin ; cbn.
Qed.

Lemma ren_comp_has_type (Δ Γ Θ : context) (r r' : ren) :
  (Δ ⊢ r :: Γ) ->
  (Γ ⊢ r' :: Θ) ->
  (Δ ⊢ (r' >> r) :: Θ).
Proof.
  intros * Hr Hr' i T Hin.
  apply Hr', Hr in Hin.
  assumption.
Qed.

Lemma shift_has_type (Γ : context) (T : type) : (Γ,,T) ⊢ ↑ :: Γ.
Proof.
  intros ? ** ; assumption.
Qed.

Lemma ren_cons_has_type (Δ Γ : context) (T : type) (ρ : ren) (n : nat) :
  in_context n Δ T ->
  (Δ ⊢ ρ :: Γ) ->
  Δ ⊢ (n .: ρ) :: (Γ,,T).
Proof.
  intros Hty Hs [] T' Hin ; cbn.
  - unfold in_context in Hin ; cbn in *.
    injection Hin ; subst.
    assumption.
  - apply Hs, Hin.
Qed.

Hint Resolve ren_id_has_type ren_comp_has_type shift_has_type ren_cons_has_type : typing.

Lemma ren_lift_has_type (Δ Γ : context) (T : type) (r : ren) :
  (Δ ⊢ r :: Γ) ->
  (Δ,,T) ⊢ (⇑ r) ::  (Γ,,T).
Proof.
  intros.
  change (Δ,, T ⊢ 0 .: r >> S :: Γ,, T).
  eauto with typing.
Qed.

Hint Resolve ren_lift_has_type : typing.

Lemma ren_typing (Δ Γ : context) (T : type) (t : term) (r : ren) :
  (Γ ⊢ t :: T) ->
  (Δ ⊢ r :: Γ) ->
  Δ ⊢ t⟨r⟩ :: T.
Proof.
  intros Ht Hr.
  induction Ht in Δ, r, Hr ; cbn ; eauto 10 with typing.
Qed.

Hint Resolve ren_typing : typing.

(** Same, not in the hint database because it is too wild *)
Instance subst_has_type_ext (Δ Γ : context) :
  Proper ((pointwise_relation _ eq) ==> iff) (typing (Obj := subst) Δ Γ).
Proof.
  intros ?? Hsubst.
  split ; intros e i T Hin.
  1: rewrite <- Hsubst.
  2: rewrite Hsubst.
  all: now apply e.
Qed.

Lemma ren_subst_has_type (Δ Γ : context) (r : ren) :
  (Δ ⊢ r :: Γ) ->
  (Δ ⊢ (r >> ids) :: Γ).
Proof.
  intros Hr i T Hin ; cbn.
  constructor.
  now apply Hr.
Qed.

Lemma subst_cons_has_type (Δ Γ : context) (T : type) (σ : subst) (t : term) :
  (Δ ⊢ t :: T) ->
  (Δ ⊢ σ :: Γ) ->
  Δ ⊢ (t .: σ) :: (Γ,,T).
Proof.
  intros Hty Hs [] T' Hin ; cbn.
  - unfold in_context in Hin ; cbn in *.
    injection Hin ; subst.
    assumption.
  - apply Hs, Hin.
Qed.

Hint Resolve ren_subst_has_type subst_cons_has_type : typing.

Lemma id_subst_has_type (Γ : context) :
  Γ ⊢ ids :: Γ.
Proof.
  eauto with typing.
Qed.

Lemma subst_one_has_type (Γ : context) (T : type) (t : term) :
  (Γ ⊢ t :: T) -> 
  Γ ⊢ (t..) ::  (Γ,,T).
Proof.
  intros.
  eauto with typing.
Qed.

Lemma subst_lift_has_type (Δ Γ : context) (T : type) (σ : subst) :
  (Δ ⊢ σ :: Γ) ->
  (Δ,,T) ⊢ (⇑ σ) :: (Γ,,T).
Proof.
  intros.
  eapply subst_cons_has_type.
  1: eauto with typing.
  do 2 red ; cbn.
  eauto with typing.
Qed.

Hint Resolve id_subst_has_type subst_one_has_type subst_lift_has_type : typing.

Lemma subst_typing (Δ Γ : context) t T (σ : subst) :
  (Γ ⊢ t :: T) ->
  (Δ ⊢ σ :: Γ) ->
  Δ ⊢ t[σ] :: T.
Proof.
  intros Ht Hσ.
  induction Ht in Δ, σ, Hσ ; cbn ; eauto 10 with typing.
Qed.

Hint Resolve subst_typing : typing.

Lemma subst_comp_has_type (Δ Γ Θ : context) (σ σ' : subst) :
  (Δ ⊢ σ :: Γ) ->
  (Γ ⊢ σ' :: Θ) ->
  (Δ ⊢ (σ' >> (subst_term σ)) :: Θ).
Proof.
  do 2 red.
  eauto with typing.
Qed.

Lemma tip_has_type (Γ : context) (A B : type) (f : term -> term) :
  (Γ,,A ⊢ f (tVar 0) :: B) ->
  (Γ,,A ⊢ tip f :: Γ,,B).
Proof.
  unfold tip.
  eauto with typing.
Qed.

Lemma swap_var_has_type Γ (A B : type) :
  ((Γ,,A),,B) ⊢ swap_var :: ((Γ,,B),,A).
Proof.
  unfold swap_var.
  eauto with typing.
Qed.

Hint Resolve subst_comp_has_type tip_has_type swap_var_has_type : typing.

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