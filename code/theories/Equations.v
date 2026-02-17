(** * Interpolation.Equations: definition and properties of conversion *)
From Interpolation Require Import Utils Syntax Notations Elim Context Typing Reduction.

Import ListNotations.
Set Primitive Projections.

Class Theory `{Lang} : Type := {
  equations : Set ;
  eq_ctx : equations -> context ;
  eq_ty : equations -> type ;
  eq_left : equations -> term ;
  eq_left_ok : forall e, (eq_ctx e) ⊢ (eq_left e) :: (eq_ty e) ;
  eq_right : equations -> term ;
  eq_right_ok : forall e, (eq_ctx e) ⊢ (eq_right e) :: (eq_ty e) ;
}.

#[refine,local]Instance EmptyTheory `{Lang} : Theory := {
  equations := False ;
}.
Proof.
  all: intros ; now exfalso.
Defined.

Section Equations.
  Disable Notation "≡" : typing_scope.

  Context `{l : Lang} `{! Theory}.

  Inductive conversion (Γ : context) : type -> relation term :=
    (** beta rules *)
    | E_Beta_Fun A B t u :
      (Γ,,A ⊢ t :: B) ->
      (Γ ⊢ u :: A) ->
      (Γ ⊢ tApp (tLam t) u ≡ t[u..] :: B)

    | E_Beta_Fst A B t t' :
      (Γ ⊢ t :: A) ->
      (Γ ⊢ t' :: B) ->
      (Γ ⊢ tFst (tPair t t') ≡ t :: A)

    | E_Beta_Snd A B t t' :
        (Γ ⊢ t :: A) ->
        (Γ ⊢ t' :: B) ->
        (Γ ⊢ tSnd (tPair t t') ≡ t' :: B)

    | E_Beta_Left A B C a bl br :
      (Γ ⊢ a :: A) ->
      (Γ,,A ⊢ bl :: C) ->
      (Γ,,B ⊢ br :: C) ->
      (Γ ⊢ tIf (tLeft a) bl br ≡ bl[a..] :: C)

    | E_Beta_Right A B C b bl br :
      (Γ ⊢ b :: B) ->
      (Γ,,A ⊢ bl :: C) ->
      (Γ,,B ⊢ br :: C) ->
      (Γ ⊢ tIf (tRight b) bl br ≡ br[b..] :: C)

    (** eta laws *)
    | E_Eta_Unit t :
      (Γ ⊢ t :: TUnit) ->
      (Γ ⊢ t ≡ tStar :: TUnit)

    | E_Eta_Fun A B f :
      (Γ ⊢ f :: TFun A B) ->
      (Γ ⊢ f ≡ tLam (tApp f⟨↑⟩ (tVar 0)) :: TFun A B)

    | E_Eta_Prod A B p :
      (Γ ⊢ p :: TProd A B) ->
      (Γ ⊢ p ≡ tPair (tFst p) (tSnd p) :: TProd A B)

    | E_Eta_Emp e A t :
      (Γ ⊢ e :: TEmp) ->
      (Γ ⊢ t :: A) ->
      (Γ ⊢ t ≡ tAbort e :: A)
    
    | E_Eta_Sum A B C s e :
      (Γ ⊢ s :: TSum A B) ->
      (Γ,,TSum A B ⊢ e :: C) ->
      (Γ ⊢ e[s..] ≡ tIf s e[tip tLeft] e[tip tRight] :: C)

    (** theory *)
    | E_Theory (e : equations) (σ : subst) :
      (Γ ⊢ σ :: eq_ctx e) ->
      (Γ ⊢ (eq_left e)[σ] ≡ (eq_right e)[σ] :: eq_ty e)


    | E_Refl A t :
      (Γ ⊢ t :: A) ->
      (Γ ⊢ t ≡ t :: A)

    (** congruences *)
    | E_Lam A B t t' :
      (Γ ,, A ⊢ t ≡ t' :: B) ->
      Γ ⊢ tLam t ≡ tLam t' :: TFun A B

    | E_App A B f f' u u' :
      (Γ ⊢ f ≡ f' :: TFun A B) ->
      (Γ ⊢ u ≡ u' :: A) ->
      Γ ⊢ tApp f u ≡ tApp f' u' :: B

    | E_Pair A B a a' b b' :
      (Γ ⊢ a ≡ a' :: A) ->
      (Γ ⊢ b ≡ b' :: B) ->
      (Γ ⊢ tPair a b ≡ tPair a' b' :: TProd A B)

    | E_Fst A B t t' :
      (Γ ⊢ t ≡ t' :: TProd A B) ->
      (Γ ⊢ tFst t ≡ tFst t' :: A)

    | E_Snd A B t t' :
      (Γ ⊢ t ≡ t' :: TProd A B) ->
      (Γ ⊢ tSnd t ≡ tSnd t' :: B)

    | E_Abort A t t' :
      (Γ ⊢ t ≡ t':: TEmp) ->
      (Γ ⊢ tAbort t ≡ tAbort t' :: A)

    | E_Left A B t t' :
      (Γ ⊢ t ≡ t' :: A) ->
      (Γ ⊢ tLeft t ≡ tLeft t' :: TSum A B)

    | E_Right A B t t' :
      (Γ ⊢ t ≡ t' :: B) ->
      (Γ ⊢ tRight t ≡ tRight t' :: TSum A B)

    | E_If A B T s s' bl bl' br br' :
      (Γ ⊢ s ≡ s' :: TSum A B) ->
      (Γ,,A ⊢ bl ≡ bl' :: T) ->
      (Γ,,B ⊢ br ≡ br' :: T) ->
      (Γ ⊢ tIf s bl br ≡ tIf s' bl' br' :: T)

    | E_Sym A t t' :
      (Γ ⊢ t ≡ t' :: A) ->
      (Γ ⊢ t' ≡ t :: A)
    | E_Trans A t t' t'' :
      (Γ ⊢ t ≡ t' :: A) ->
      (Γ ⊢ t' ≡ t'' :: A) ->
      (Γ ⊢ t ≡ t'' :: A)

  where "Γ '⊢' t '≡' t' '::' T" := (conversion Γ T t t').

End Equations.

#[export] Instance HasConvTm `{Theory} : HasConv context type term := conversion.

#[export] Instance HasConvRen `{Lang} : HasConv context context ren :=
  fun (Δ Γ : context) (r r' : ren) =>
  (Δ ⊢ r :: Γ) /\ (Δ ⊢ r' :: Γ) /\
  (forall i T, in_context i Γ T -> r i = r' i).

#[export] Instance HasTypingSubst `{Theory} : HasConv context context subst :=
 fun (Δ Γ : context) (σ σ' : subst) =>
  forall i T, in_context i Γ T -> Δ ⊢ σ i ≡ σ' i :: T.


Ltac fold_conv := change conversion with (conv (Ctx := context) (Ty := type) (Obj := term)) in *.

Smpl Add fold_conv : refold.

Section Congruences.
  Context `{Theory}.

  Instance PER_conv (Γ : context) (T : type) : RelationClasses.PER (conv Γ T).
  Proof.
    split.
    - intros ???.
      now constructor.
    - intros ??? ??.
      now econstructor.
  Qed.

  Instance Lam_Proper (Γ : context) (A B : type) : Proper (conv (Γ,,A) B ==> conv Γ (TFun A B)) tLam.
  Proof ltac:(now constructor).

  Instance App_Proper Γ A B : Proper (conv Γ (TFun A B) ==> conv Γ A ==> conv Γ B) tApp.
  Proof ltac:(now econstructor).

  Instance Pair_Proper Γ A B : Proper (conv Γ A ==> conv Γ B ==> conv Γ (TProd A B)) tPair.
  Proof ltac:(now econstructor).

  Instance Fst_Proper Γ A B : Proper (conv Γ (TProd A B) ==> conv Γ A) tFst.
  Proof ltac:(now econstructor).

  Instance Snd_Proper Γ A B : Proper (conv Γ (TProd A B) ==> conv Γ B) tSnd.
  Proof ltac:(now econstructor).

  Instance Abort_Proper Γ A : Proper (conv Γ TEmp ==> conv Γ A) tAbort.
  Proof ltac:(now econstructor).

  Instance Left_Proper Γ A B : Proper (conv Γ A ==> conv Γ (TSum A B)) tLeft.
  Proof ltac:(now econstructor).

  Instance Right_Proper Γ A B : Proper (conv Γ B ==> conv Γ (TSum A B)) tRight.
  Proof ltac:(now econstructor).

  Instance If_Proper (Γ : context) (A B C : type) :
    Proper (conv Γ (TSum A B) ==> conv (Γ,,A) C ==> conv (Γ,,B) C ==> conv Γ C) tIf.
  Proof ltac:(now econstructor).


  Lemma term_refl (Γ : context) (T : type) (t : term) : (Γ ⊢ t :: T) -> Γ ⊢ t ≡ t :: T.
  Proof.
    now constructor.
  Qed.

  Instance ProperProxy_conv (Γ : context) (T : type) (t : term) :
    (Γ ⊢ t :: T) -> ProperProxy (conv Γ T) t.
  Proof.
    intros.
    now constructor.
  Qed.

  Instance ProperProxy_conv_subst (Γ Δ : context) (σ : subst) :
    (Γ ⊢ σ :: Δ) -> ProperProxy (conv Γ Δ) σ.
  Proof.
    intros.
    now constructor.
  Qed.

    Instance ProperProxy_conv_ren (Γ Δ : context) (ρ : ren) :
    (Γ ⊢ ρ :: Δ) -> ProperProxy (conv Γ Δ) ρ.
  Proof.
    intros.
    now constructor.
  Qed.

End Congruences.

Hint Resolve term_refl : typing.

Existing Instances PER_conv Lam_Proper App_Proper Pair_Proper Fst_Proper Snd_Proper Abort_Proper Left_Proper Right_Proper If_Proper.

(** These hints are used to help setoid rewriting with conversion.
  Since conversion is non-transitive, the usual attempt at solving side-goals generated
  by [Proper] instances using [Reflexivity] instances fails. Instead, we hook into
  the corresponding proxy, use the “quasi-reflexivity” of conversion which generates
  a typing subgoal, and solve that goal with [eauto with typing]. *)
Hint Extern 0 (ProperProxy (conv (Obj := term) _ _) _) =>
  apply ProperProxy_conv ; eauto with typing : typeclass_instances.

Hint Extern 0 (ProperProxy (conv (Obj := ren) _ _) _) =>
  apply ProperProxy_conv_ren ; eauto with typing : typeclass_instances.

Hint Extern 0 (ProperProxy (conv (Obj := subst) _ _) _) =>
  apply ProperProxy_conv_subst ; eauto with typing : typeclass_instances.


Lemma conv_typing `{th : Theory} Γ T (t t' : term) :
  (Γ ⊢ t ≡ t' :: T) -> (Γ ⊢ t :: T) /\ (Γ ⊢ t' :: T).
Proof.
  intros Hty.
  pose proof th.(eq_left_ok).
  pose proof th.(eq_right_ok).
  induction Hty ; cbn ; refold ; split ;
      rewrite ?subst1_ren, ?up_lift_ren, ?up_lift_up_ren, ?tip_up_ren.
  all: eauto 20 with typing.
Qed.

Corollary conv_typing_l `{th : Theory} Γ T (t t' : term) :
  (Γ ⊢ t ≡ t' :: T) -> Γ ⊢ t :: T.
Proof.
  now intros ?%conv_typing.
Qed.

Corollary conv_typing_r `{th : Theory} Γ T (t t' : term) :
  (Γ ⊢ t ≡ t' :: T) -> Γ ⊢ t' :: T.
Proof.
  now intros ?%conv_typing.
Qed.

Hint Resolve conv_typing_l conv_typing_r : typing.

(** ** Equations for renamings and substitutions *)

Section EquationsSubst.
  Context `{Theory}.

  Lemma ren_conv_typing_l Δ Γ (ρ ρ' : ren) : (Δ ⊢ ρ ≡ ρ' :: Γ) -> Δ ⊢ ρ :: Γ.
  Proof.
    now intros [].
  Qed.

  Lemma ren_conv_typing_r Δ Γ (ρ ρ' : ren) : (Δ ⊢ ρ ≡ ρ' :: Γ) -> Δ ⊢ ρ' :: Γ.
  Proof.
    now intros [].
  Qed.

  Hint Immediate ren_conv_typing_l ren_conv_typing_r : typing.

  Instance ren_conv_ext (Δ Γ : context) :
    Proper ((`=1`) ==> (pointwise_relation _ eq) ==> iff) (conv (Obj := ren) Δ Γ).
  Proof.
    intros ?? Hren ?? Hren'.
    split ; intros (?&?&?).
    all: split ; [|split].
    1-2: now (eapply ren_typing_ext) ; [symmetry|] ; eauto.
    2-3: now (eapply ren_typing_ext).
    all: intros.
    - now erewrite <- Hren, <- Hren'.
    - now erewrite Hren, Hren'.
  Qed.

  Lemma ren_refl (Γ Δ : context) (ρ : ren) : (Γ ⊢ ρ :: Δ) -> Γ ⊢ ρ ≡ ρ :: Δ.
  Proof.
    intros ?.
    now do 2 red.
  Qed.

  Hint Resolve ren_refl : typing.

  Instance ren_conv_PER (Γ Δ : context) : PER (conv (Obj := ren) Δ Γ).
  Proof.
    split.
    - intros ?? (?&?&e).
      do 2 red ; prod_splitter ; tea.
      intros.
      now erewrite e.
    - intros ??? (?&?&e) (?&?&e').
      do 2 red ; prod_splitter ; tea.
      intros.
      now erewrite e.
  Qed.

  Instance Proper_comp (Δ Γ Θ : context) :
    Proper (conv (Obj := ren) Δ Γ ==> conv (Obj := ren) Γ Θ ==> conv (Obj := ren) Δ Θ) funcomp.
  Proof.
    repeat red.
    intros ?? (?&?&Hr) ?? (?&?&Hr') ** ; cbn.
    prod_splitter.
    1-2: eauto with typing.
    intros.
    erewrite Hr' ; tea.
    now erewrite Hr.
  Qed.

  Instance Proper_cons (Δ Γ : context) (T : type) (n : nat) :
    in_context n Δ T ->
    Proper (conv (Obj := ren) Δ Γ ==> conv (Obj := ren) Δ (Γ,,T)) (scons n).
  Proof.
    intros Hty ?? Hs.
    do 2 red.
    prod_splitter.
    1-2: now eauto with typing.
    intros [] T' Hin ; cbn.
    - reflexivity.
    - destruct Hs as (_&_&Hs).
      now eapply Hs.
  Qed.

  Instance _ren_up_conv (Δ Γ : context) (T : type) :
    Proper (conv (Obj := ren) Δ Γ ==> conv (Obj := ren) (Δ,,T) (Γ,,T)) up_term.
  Proof.
    intros r r' e.
    change (Δ,, T ⊢ (0 .: r >> ↑) ≡ (0 .: r' >> ↑) :: Γ,, T).
    apply Proper_cons ; eauto with typing.
    rewrite e.
    now eauto with typing.
  Qed.

  Lemma ren_up_conv (Δ Γ : context) (T : type) (r r' : ren) :
    (Δ ⊢ r ≡ r' :: Γ) ->
    (Δ,,T) ⊢ (⇑ r) ≡ (⇑ r') :: (Γ,,T).
  Proof.
    intros e.
    now apply _ren_up_conv.
  Qed.

  Hint Resolve ren_up_conv : typing.

  Lemma ren_conv_ren (Δ Γ : context) (T : type) (t : term) (r r' : ren) :
    (Γ ⊢ t :: T) ->
    (Δ ⊢ r ≡ r' :: Γ) ->
    Δ ⊢ t⟨r⟩ ≡ t⟨r'⟩ :: T.
  Proof.
    intros Ht Hr.
    induction Ht in Δ, r, r', Hr |- * ; cbn ; refold ;
      rewrite ?subst1_ren, ?up_lift_ren, ?up_lift_up_ren.
    all: try solve [econstructor ; eauto 10 with typing].
    destruct Hr as (?&?&e).
    erewrite e ; tea.
    econstructor ; eauto with typing.
  Qed.

  Lemma ren_conv_tm (Δ Γ : context) (T : type) (t t' : term) (r : ren) :
    (Γ ⊢ t ≡ t' :: T) ->
    (Δ ⊢ r :: Γ) ->
    Δ ⊢ t⟨r⟩ ≡ t'⟨r⟩ :: T.
  Proof.
    intros Ht Hr.
    induction Ht in Δ, r, Hr |- * ; cbn ; refold ;
      rewrite ?subst1_ren, ?up_lift_ren, ?up_lift_up_ren, ?tip_up_ren.
    all: try solve [econstructor ; eauto with typing].
    asimpl ; refold.
    constructor.
    eauto with typing.
  Qed.

  Instance ren_conv (Δ Γ : context) (T : type) :
    Proper (conv (Obj := ren) Δ Γ ==> conv Γ T ==> conv Δ T) ren1.
  Proof.
    intros ?? e ?? e'.
    etransitivity.
    1: eapply ren_conv_tm.
    1,2: now eauto with typing.
    eapply ren_conv_ren.
    all: eauto with typing.
  Qed.

  Instance subst_conv_ext (Δ Γ : context) :
    Proper ((`=1`) ==> (pointwise_relation _ eq) ==> iff) (conv (Obj := subst) Δ Γ).
  Proof.
    intros ?? Hsubst ?? Hsubst'.
    split ; intros e i T Hin.
    1: rewrite <- Hsubst, <- Hsubst'.
    2: rewrite Hsubst, Hsubst'.
    all: now apply e.
  Qed.

  Lemma subst_conv_typing_l Δ Γ (σ σ' : subst) : (Δ ⊢ σ ≡ σ' :: Γ) -> Δ ⊢ σ :: Γ.
  Proof.
    intros ** ? **.
    eauto with typing.
  Qed.

  Lemma subst_conv_typing_r Δ Γ (σ σ' : subst) : (Δ ⊢ σ ≡ σ' :: Γ) -> Δ ⊢ σ' :: Γ.
  Proof.
    intros ** ? **.
    eauto with typing.
  Qed.

  Hint Immediate subst_conv_typing_l subst_conv_typing_r : typing.

  Lemma subst_refl Γ Δ (σ : subst) :
    (Γ ⊢ σ :: Δ) -> 
    (Γ ⊢ σ ≡ σ :: Δ).
  Proof.
    intros Hs ?? Hin.
    constructor.
    now apply Hs.
  Qed.

  Hint Resolve subst_refl : typing.

  Instance ren_subst_conv (Δ Γ Θ : context) :
    Proper (conv (Obj := subst) Δ Γ ==> conv (Obj := ren) Γ Θ ==> conv (Obj := subst) Δ Θ) funcomp.
  Proof.
    intros ?? Hs ?? (?&Hr'&e) i T Hin ; cbn.
    erewrite e ; tea.
    eapply Hs.
    eauto with typing.
  Qed.

  Instance subst_ren_conv (Δ Γ Θ : context) :
    Proper (conv (Obj := ren) Δ Γ ==> conv (Obj := subst) Γ Θ ==> conv (Obj := subst) Δ Θ) (fun ρ σ => σ >> (ren1 ρ)).
  Proof.
    intros ?? Hr ?? Hs i T Hin ; cbn.
    now eapply ren_conv.
  Qed.

  Instance subst_cons_conv (Δ Γ : context) (T : type) :
    Proper (conv Δ T ==> conv (Obj := subst) Δ Γ ==> conv (Obj := subst) Δ (Γ,,T)) scons.
  Proof.
    intros ?? Ht ?? Hs [] T' Hin ; cbn.
    - unfold in_context in Hin ; cbn in *.
      injection Hin ; subst.
      assumption.
    - apply Hs, Hin.
  Qed.

  Lemma subst_one_conv (Γ : context) (T : type) (t t' : term) :
    (Γ ⊢ t ≡ t' :: T) -> 
    Γ ⊢ (t..) ≡ (t'..) ::  (Γ,,T).
  Proof.
    intros e.
    apply subst_cons_conv ; eauto with typing.
  Qed.

  Instance _subst_up_conv (Δ Γ : context) (T : type) :
    Proper (conv (Obj := subst) Δ Γ ==> conv (Obj := subst) (Δ,,T) (Γ,,T)) up_term.
  Proof.
    intros ?? ?.
    eapply subst_cons_conv.
    1: now eauto with typing.
    eapply subst_ren_conv ; eauto with typing.
  Qed.

  Lemma subst_up_conv (Δ Γ : context) (T : type) (σ σ' : subst) :
    (Δ ⊢ σ ≡ σ' :: Γ) ->
    (Δ,,T) ⊢ (⇑ σ) ≡ (⇑ σ') :: (Γ,,T).
  Proof.
    intros.
    now apply _subst_up_conv.
  Qed.

  Hint Resolve subst_up_conv : typing.

  Lemma subst_conv_subst (Δ Γ : context) (T : type) (t : term) (σ σ' : subst) :
    (Γ ⊢ t :: T) ->
    (Δ ⊢ σ ≡ σ' :: Γ) ->
    Δ ⊢ t[σ] ≡ t[σ'] :: T.
  Proof.
    intros Ht Hs.
    induction Ht in Δ, σ, σ', Hs |- * ; cbn ; refold.
    all: solve [econstructor ; eauto 10 with typing].
  Qed.

  Lemma subst_conv_tm (Δ Γ : context) (T : type) (t t' : term) (σ : subst) :
    (Γ ⊢ t ≡ t' :: T) ->
    (Δ ⊢ σ :: Γ) ->
    Δ ⊢ t[σ] ≡ t'[σ] :: T.
  Proof.
    intros Ht Hs.
    induction Ht in Δ, σ, Hs |- * ; cbn ; refold;
      rewrite ?subst1_subst, ?up_lift_subst, ?up_lift_up_subst, ?tip_up_subst.
    all: try solve [econstructor ; eauto with typing].
    asimpl ; refold.
    constructor.
    eauto with typing.
  Qed.

  Instance _subst_conv (Δ Γ : context) (T : type) :
    Proper (conv (Obj := subst) Δ Γ ==> conv Γ T ==> conv Δ T) subst1.
  Proof.
    intros ?? e ?? e'.
    etransitivity.
    1: eapply subst_conv_tm.
    1-2: now eauto with typing.
    eapply subst_conv_subst.
    all: eauto with typing.
  Qed.

  Lemma subst_conv (Δ Γ : context) t t' T (σ σ' : subst) :
    (Γ ⊢ t ≡ t' :: T) ->
    (Δ ⊢ σ ≡ σ' :: Γ) ->
    Δ ⊢ t[σ] ≡ t'[σ'] :: T.
  Proof.
    intros Ht Hσ.
    now eapply _subst_conv.
  Qed.

  Hint Resolve subst_conv : typing.

  Instance subst_comp_conv (Δ Γ Θ : context) :
    Proper (conv (Obj := subst) Δ Γ ==> conv (Obj := subst) Γ Θ ==> conv (Obj := subst) Δ Θ) (fun σ σ' => σ' >> (subst1 σ)).
  Proof.
    intros ?? Hσ ?? Hσ' ??? ; cbn.
    eauto with typing.
  Qed.

  Lemma tip_conv (Γ : context) (A B : type) (f f' : term -> term) :
    (Γ,,A ⊢ f (tVar 0) ≡ f' (tVar 0) :: B) ->
    (Γ,,A ⊢ tip f ≡ tip f' :: Γ,,B).
  Proof.
    unfold tip.
    intros e.
    apply subst_cons_conv ; tea.
    eapply ren_subst_conv ; eauto with typing.
  Qed.

End EquationsSubst.

(** ** Reduction implies conversion *)

Section ReductionConversion.
  Context `{Theory}.

  Lemma comm_conv_abort Γ A (e : elim) (t : term) :
    (Γ ⊢ zip e (tAbort t) :: A) ->
    (Γ ⊢ zip e (tAbort t) ≡ tAbort t :: A).
  Proof.
    intros Hty.
    apply E_Eta_Emp ; tea.
    destruct e ; cbn in * ; inversion Hty ; subst ; clear Hty ; refold.
    all: now match goal with | Hty : typing _ _ (tAbort _) |- _ => inversion Hty ; subst ; clear Hty ; refold end.
  Qed.

  Lemma tip_shift_elim f (e : elim) : e⟨↑⟩[tip f] = e⟨↑⟩.
  Proof.
    unfold tip.
    asimpl ; refold.
    now renamify.
  Qed.

  Definition elim_typing (Γ : context) (A B : type) (e : elim) : Prop :=
    match e with
    | eApp u => exists A', A = TFun A' B /\ (Γ ⊢ u :: A')
    | eProj true => exists B', A = TProd B B'
    | eProj false => exists B', A = TProd B' B
    | eAbort => A = TEmp
    | eIf bl br => exists A' A'', A = TSum A' A'' /\ (Γ,,A' ⊢ bl :: B) /\ (Γ,,A'' ⊢ br :: B)
    end.

  Lemma zip_typing (Γ : context) (A B : type) e t :
    elim_typing Γ A B e ->
    (Γ ⊢ t :: A) ->
    Γ ⊢ zip e t :: B.
  Proof.
    intros He Ht.
    destruct e ; cbn in * ; subst.
    1: destruct b.
    all: repeat match goal with | H : exists _, _ |- _ => destruct H ; subst | H : _ /\ _ |- _ => destruct H ; subst end.
    all: now eauto with typing.
  Qed.

  Lemma elim_subst_typing (Γ Δ : context) (A B : type) e (σ : subst) :
    (Δ ⊢ σ :: Γ) ->
    elim_typing Γ A B e ->
    elim_typing Δ A B e[σ].
  Proof.
    intros ? He.
    destruct e ; cbn in * ; subst.
    1: destruct b.
    all: repeat match goal with | H : exists _, _ |- _ => destruct H ; subst | H : _ /\ _ |- _ => destruct H ; subst end.
    all: repeat eexists.
    all: refold ; eauto with typing.
  Qed.

  Lemma elim_ren_typing (Γ Δ : context) (A B : type) e (ρ : ren) :
    (Δ ⊢ ρ :: Γ) ->
    elim_typing Γ A B e ->
    elim_typing Δ A B e⟨ρ⟩.
  Proof.
    intros ? He.
    destruct e ; cbn in * ; subst.
    1: destruct b.
    all: repeat match goal with | H : exists _, _ |- _ => destruct H ; subst | H : _ /\ _ |- _ => destruct H ; subst end.
    all: repeat eexists.
    all: refold ; eauto with typing.
  Qed.

  Lemma zip_typing_inv (Γ : context) (B : type) e t :
    (Γ ⊢ zip e t :: B) ->
    exists A, elim_typing Γ A B e /\ (Γ ⊢ t :: A).
  Proof.
    intros Hty.
    destruct e ; cbn in *.
    all: inversion Hty ; subst ; clear Hty ; refold.
    all: now repeat eexists.
  Qed.

  Lemma zip_conv (Γ : context) (A B : type) e t t' :
    elim_typing Γ A B e ->
    (Γ ⊢ t ≡ t' :: A) ->
    Γ ⊢ zip e t ≡ zip e t' :: B.
  Proof.
    intros He Ht.
    destruct e ; cbn in * ; subst.
    1: destruct b.
    all: repeat match goal with | H : exists _, _ |- _ => destruct H ; subst | H : _ /\ _ |- _ => destruct H ; subst end.
    all: econstructor ; eauto with typing.
  Qed.

  Lemma comm_conv_if Γ C (e : elim) (s bl br : term) :
    (Γ ⊢ zip e (tIf s bl br) :: C) ->
    (Γ ⊢ zip e (tIf s bl br) ≡ tIf s (zip e⟨↑⟩ bl) (zip e⟨↑⟩ br) :: C).
  Proof.
    intros Hty.
    set (e' := (zip e⟨↑⟩ (tIf (tVar 0) bl⟨⇑ ↑⟩ br⟨⇑ ↑⟩))).
    
    replace (zip e (tIf s bl br)) with (e'[s..]).
    2:{
      destruct e ; cbn ; try reflexivity.
      all: asimpl ; cbn ; refold.
      all: rewrite !scons_eta'.
      all: now asimpl.
    }
    eapply zip_typing_inv in Hty as (T&?&Hty).
    inversion Hty ; subst ; clear Hty ; refold.
    rewrite E_Eta_Sum ; tea ; cycle -1.
    - eapply zip_typing.
      2: now eauto 15 with typing.
      eapply elim_ren_typing ; eauto with typing.
    - econstructor.
      1: now eauto with typing.
      all: subst e'.
      all: rewrite zip_subst, tip_shift_elim ; cbn ; refold.
      all: eapply zip_conv ; [now eapply elim_ren_typing ; eauto with typing|].
      + rewrite E_Beta_Left ; eauto with typing.
        2-3: eapply subst_typing ; eauto with typing.
        replace (_[_]) with bl.
        1: eauto with typing.
        asimpl ; refold.
        symmetry.
        apply subst_id.
        now intros [|].
      + rewrite E_Beta_Right ; eauto with typing.
        2-3: eapply subst_typing ; eauto with typing.
        replace (_[_]) with br.
        1: eauto with typing.
        asimpl ; refold.
        symmetry.
        apply subst_id.
        now intros [|].
    Unshelve.
    all: easy.
  Qed.

  Lemma subject_reduction_1_conv (Γ : context) (T : type) (t u : term) :
    (Γ ⊢ t :: T) -> t ⤳ u -> (Γ ⊢ t ≡ u :: T).
  Proof.
    intros Hty Hred.
    induction Hred in Γ, T, Hty |- *.
    all: try (match goal with | e : elim |- _ => destruct e ; cbn in * end ; try solve [congruence]).
    all: try (match goal with | e : _ = _ |- _ => inversion e ; subst end).
    all: repeat match goal with | H : (_ ⊢ _ _ :: _) |- _ => inversion H ; subst ; clear H ; refold end.
    all: try solve [econstructor ; eauto with typing].
    all: substify.
    1: eapply (comm_conv_if _ _ (eApp _)).
    2: eapply (comm_conv_if _ _ (eProj _)).
    3: eapply (comm_conv_if _ _ (eProj _)).
    4: eapply (comm_conv_if _ _ eAbort).
    5: assert (⇑ (↑) >> tVar =1 ⇑ (↑ >> tVar)) as -> by
          now intros [|].
    5: eapply (comm_conv_if _ _ (eIf _ _)).
    all: eapply zip_typing ; cbn ; eauto with typing.
    Unshelve.
    all: easy.
  Qed.

  Lemma subject_reduction_conv (Γ : context) (T : type) (t u : term) :
    (Γ ⊢ t :: T) -> t ⤳* u -> (Γ ⊢ t ≡ u :: T).
  Proof.
    induction 2 ; refold.
    - now eapply subject_reduction_1_conv.
    - now constructor.
    - etransitivity ; eauto with typing.
  Qed.

End ReductionConversion.