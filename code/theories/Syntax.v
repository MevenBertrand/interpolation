From smpl Require Import Smpl.
From Stdlib Require Import List.
From Stdlib Require Import Setoid Morphisms Relation_Definitions RelationClasses.
From Interpolation Require Import Utils.
From Interpolation Require Export BasicAst core unscoped Ast Context.

(* Export UnscopedNotations.
#[global] Open Scope subst_scope. *)

Notation "'ren'" := (nat -> nat) (only parsing).
Notation "'subst'" := (nat -> term) (only parsing).

Declare Scope asubst_scope.
Delimit Scope asubst_scope with asub.

Arguments id {_} _/.
Arguments Datatypes.id {_} _/.

Arguments funcomp {X Y Z}%_type_scope (g f)%_function_scope _/.

Notation "f >> g" := (funcomp g f) (at level 50) : function_scope.

Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity) : asubst_scope.

Notation "s ⟨ xi1 ⟩" := (ren1 xi1 s) (at level 7, left associativity, format "s ⟨ xi1 ⟩") : asubst_scope.

Notation "s [ sigma ]" := (subst1 sigma s) (at level 7, left associativity, format "s '/' [ sigma ]") : asubst_scope.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : asubst_scope.

Notation "↑" := (unscoped.shift) : asubst_scope.

Notation "⇑ σ" := (up_term σ) (at level 1) : asubst_scope.

#[global] Instance up_term_ren : Up_term _ _ := up_ren.

Arguments up_term_ren _/.

#[global] Open Scope asubst_scope.

Notation "'tFst'" := (tProj true).
Notation "'tSnd'" := (tProj false).
Notation "'eFst'" := (eProj true).
Notation "'eSnd'" := (eProj false).
Notation "'tLeft'" := (tIn false).
Notation "'tRight'" := (tIn true).

#[global] Instance Ren_elim `{Lang} : (Ren1 (nat -> nat) elim elim) :=
  fun ρ e => @subst_elim _ _ (ρ >> tVar) e.

#[global] Instance Ren1_subst {Y Z : Type} `{Ren1 (nat -> nat) Y Z} :
  (Ren1 (nat -> nat) (nat -> Y) (nat -> Z)) :=
  fun ρ σ i => (σ i)⟨ρ⟩.

Ltac fold_autosubst :=
    fold ren_term ;
    fold subst_term ;
    fold subst_elim.

Smpl Add fold_autosubst : refold.

Ltac change_autosubst :=
    change ren_term with (@ren1 _ _ _ Ren_term) in * ;
    change subst_term with (@subst1 _ _ _ Subst_term) in *;
    change (fun i => (?σ i)⟨?ρ⟩) with (@ren1 _ _ _ Ren1_subst ρ σ) in * ;
    change up_ren with (@up_term _ _ up_term_ren) in * ;
    change (up_term_ren ?t) with (@up_term _ _ up_term_ren t) in * ;
    change upRen_term_term with (@up_term _ _ up_term_ren) in * ;
    change up_term_term with (@up_term _ _ Up_term_term) in *.

Smpl Add 50 change_autosubst : refold.

Arguments ren1 {_ _ _}%_type_scope {Ren1} _ !_/.
(* Ideally, we'd like Ren_term to not be there, and ren_term to be directly the Ren1 instance… *)
Arguments Ren_term _ _ /.
Arguments Ren1_subst {_ _ _} _ _/.
Arguments ids {_ _} {_} _/.
Arguments VarInstance_term _/.

(** ** Lemmas *)

Section Lemmas.
Context `{Lang}.

  Lemma subst_id (σ : subst) (t : term) : σ =1 ids -> t[σ] = t.
  Proof.
    intros Hσ.
    unfold subst1, Subst_term.
    erewrite ext_term ; tea.
    now asimpl.
  Qed.

  Lemma renRen_term (ρ ρ' : ren) (t : term) : t⟨ρ⟩⟨ρ'⟩ = t⟨ρ >> ρ'⟩.
  Proof.
    apply renRen_term.
  Qed.

  Lemma up_up_ren ρ ρ' (t : term) : t⟨⇑ ρ⟩⟨⇑ ρ'⟩ = t⟨⇑ (ρ >> ρ')⟩.
  Proof.
    substify ; asimpl ; refold.
    apply subst_term_morphism.
    1: now intros [|].
    easy.
  Qed.

  Lemma up_up_subst_ren (σ : subst) (ρ : ren) (t : term) :
    t[⇑ σ]⟨⇑ ρ⟩ = t[⇑ (σ >> ren_term ρ)].
  Proof.
    substify ; asimpl ; refold.
    apply subst_term_morphism.
    2: easy.
    intros [|] ; cbn ; refold ; try easy.
    substify ; refold.
    apply subst_term_morphism.
    2: easy.
    now intros [|].
  Qed.

  Lemma up_id (t : term) : t⟨⇑ id⟩ = t.
  Proof.
    enough (⇑ id =1 id) as e by 
      (rewrite e ; now asimpl).
    now intros [|].
  Qed.

  Lemma subst1_ren (t u : term) (ρ : ren) : t[u..]⟨ρ⟩ = t⟨⇑ ρ⟩[u⟨ρ⟩..].
  Proof.
    now substify ; asimpl.
  Qed.

  Lemma subst1_subst (t u : term) (σ : subst) : t[u..][σ] = t[⇑ σ][u[σ]..].
  Proof.
    now asimpl.
  Qed.

  Lemma up_lift_ren (t : term) (ρ : ren) : t⟨↑⟩⟨⇑ ρ⟩ = t⟨ρ⟩⟨↑⟩.
  Proof.
    now asimpl.
  Qed.

  Lemma up_lift_up_ren (t : term) ρ : t⟨⇑ ↑⟩⟨⇑ (⇑ ρ)⟩ = t⟨⇑ ρ⟩⟨⇑ ↑⟩.
  Proof.
    intros ; asimpl ; refold.
    apply ren_term_morphism ; [|reflexivity].
    intros [|] ; reflexivity.
  Qed.

  Lemma up_lift_subst (t : term) σ : t⟨↑⟩[⇑ σ] = t[σ]⟨↑⟩.
  Proof.
    now asimpl.
  Qed.

  Lemma up_lift_up_subst (t : term) σ : t⟨⇑ ↑⟩[⇑ (⇑ σ)] = t[⇑ σ]⟨⇑ ↑⟩.
  Proof.
    intros ; asimpl ; refold.
    apply subst_term_morphism ; [|reflexivity].
    intros [|] ; reflexivity.
  Qed.

  Lemma elim_ren (e : elim) ρ : e⟨ρ⟩ = e[ρ >> tVar].
  Proof.
    substify ; refold.
    reflexivity.
  Qed.

  Definition tip (f : term -> term) : subst :=  (f (tVar 0)).: (↑ >> ids).

  Lemma tip_shift f t : t⟨↑⟩[tip f] = t⟨↑⟩.
  Proof.
    unfold tip.
    asimpl ; refold.
    now renamify.
  Qed.

  Lemma tip_subst (f : term -> term) (t u : term) :
    (forall σ x, (f x) [σ] = f (x[σ])) ->
    u[tip f][t ..] = u[(f t)..].
  Proof.
    intros Hf.
    asimpl ; refold.
    apply ext_term.
    intros x.
    unfold tip.
    asimpl ; cbn ; refold.
    destruct x ; cbn ; [|easy].
    rewrite Hf ; now asimpl.
  Qed.

  Lemma tip_up_ren (f : term -> term) ρ (t : term) :
    (forall σ x, (f x) [σ] = f (x[σ])) ->
    t[tip f]⟨⇑ ρ⟩ = t⟨⇑ ρ⟩[tip f].
  Proof.
    intros Hf.
    unfold tip.
    substify ; asimpl.
    rewrite Hf ; asimpl.
    reflexivity.
  Qed.

  Lemma tip_up_subst (f : term -> term) σ (t : term) :
    (forall σ' x, (f x) [σ'] = f (x[σ'])) ->
    t[tip f][⇑ σ] = t[⇑ σ][tip f].
  Proof.
    intros Hf.
    unfold tip.
    asimpl ; refold.
    rewrite Hf ; asimpl.
    now substify.
  Qed.

  Definition swap_var : ren :=
    1 .: (0 .: (↑ >> ↑)).

  Lemma swap_up2 ρ (t : term) :
    t⟨swap_var⟩⟨⇑ ⇑ ρ⟩ = t⟨⇑ ⇑ ρ⟩⟨swap_var⟩.
  Proof.
    unfold swap_var.
    asimpl ; reflexivity.
  Qed.

  Lemma swap_up1 (t u : term) :
    t⟨swap_var⟩[⇑ (u..)] = t[u⟨↑⟩..].
  Proof.
    unfold swap_var.
    substify ; asimpl ; renamify ; refold.
    now rewrite scons_eta'.
  Qed.

  Lemma swap_subst1 (t u : term) :
    t⟨swap_var⟩[(u⟨↑⟩ ..)] = t[⇑ (u..)].
  Proof.
    unfold swap_var.
    substify ; asimpl ; substify ; reflexivity.
  Qed.

End Lemmas.