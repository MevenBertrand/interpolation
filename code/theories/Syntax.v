From smpl Require Import Smpl.
From Stdlib Require Import ssrbool List.
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

Notation "s [ t ]⇑" := (subst_term (scons t (shift >> tVar)) s) (at level 7, left associativity, format "s '/' [ t ]⇑") : asubst_scope.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : asubst_scope.

Notation "↑" := (shift) : asubst_scope.

Notation "⇑ σ" := (up_term_term σ) (at level 1) : asubst_scope.

#[global] Open Scope asubst_scope.

Notation "'tFst'" := (tProj true).
Notation "'tSnd'" := (tProj false).

#[global] Instance Ren1_subst {Y Z : Type} `{Ren1 (nat -> nat) Y Z} :
  (Ren1 (nat -> nat) (nat -> Y) (nat -> Z)) :=
  fun ρ σ i => (σ i)⟨ρ⟩.

Ltac fold_autosubst :=
    fold ren_term ;
    fold subst_term.

Smpl Add fold_autosubst : refold.

Ltac change_autosubst :=
    change ren_term with (@ren1 _ _ _ Ren_term) in * ;
    change subst_term with (@subst1 _ _ _ Subst_term) in *;
    change (fun i => (?σ i)⟨?ρ⟩) with (@ren1 _ _ _ Ren1_subst ρ σ) in *.

Smpl Add 50 change_autosubst : refold.

Arguments ren1 {_ _ _}%_type_scope {Ren1} _ !_/.
(* Ideally, we'd like Ren_term to not be there, and ren_term to be directly the Ren1 instance… *)
Arguments Ren_term _ _ /.
Arguments Ren1_subst {_ _ _} _ _/.