From smpl Require Import Smpl.
From Stdlib Require Import ssrbool List.
From Stdlib Require Import Setoid Morphisms Relation_Definitions RelationClasses.
From Interpolation Require Export BasicAst core unscoped Ast Context.
From Interpolation Require Import Utils.

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

Notation "s [ t ]⇑" := (subst_term (scons t (shift >> ids)) s) (at level 7, left associativity, format "s '/' [ t ]⇑") : asubst_scope.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : asubst_scope.

Notation "↑" := (shift) : asubst_scope.

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

#[global] Instance Ren_elim : (Ren1 (nat -> nat) elim elim) := fun ρ e => @subst_elim (ρ >> tVar) e.

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

Lemma subst1_ren (t u : term) (ρ : ren) : t[u..]⟨ρ⟩ = t⟨⇑ ρ⟩[u⟨ρ⟩..].
Proof.
  now substify ; asimpl.
Qed.

Lemma subst1_subst (t u : term) (σ : subst) : t[u..][σ] = t[⇑ σ][u[σ]..].
Proof.
  now asimpl.
Qed.

Lemma elim_ren e ρ : e⟨ρ⟩ = e[ρ >> tVar].
Proof.
  substify ; refold.
  reflexivity.
Qed.

Definition tip (f : term -> term) : subst :=  (f (tVar 0)).: (↑ >> ids).

Lemma tip_subst (f : term -> term) (t u : term) :
  (forall σ x, (f x) [σ] = f (x[σ])) ->
  u[tip f][t ..] = u[(f t)..].
Proof.
  intros Hf.
  rewrite substSubst_term ; refold.
  apply ext_term.
  intros x.
  unfold tip.
  asimpl ; cbn.
  destruct x ; cbn ; [|easy].
  rewrite Hf ; asimpl.
  reflexivity.
Qed.

Lemma tip_shift (f : term -> term) ρ (t : term) :
  (forall σ x, (f x) [σ] = f (x[σ])) ->
  t[tip f]⟨⇑ ρ⟩ = t⟨⇑ ρ⟩[tip f].
Proof.
  intros Hf.
  unfold tip.
  substify ; asimpl.
  rewrite Hf ; asimpl.
  reflexivity.
Qed.

Definition swap_var : ren :=
  1 .: (0 .: (↑ >> ↑)).

Lemma swap_shift2 ρ (t : term) :
  t⟨swap_var⟩⟨⇑ ⇑ ρ⟩ = t⟨⇑ ⇑ ρ⟩⟨swap_var⟩.
Proof.
  unfold swap_var.
  asimpl ; reflexivity.
Qed.

Lemma swap_shift1 (t u : term) :
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