From Interpolation Require Import Utils Syntax Notations Typing.
From Stdlib Require Import Relations Arith Lia Bool List.

Reserved Notation "Γ '|-' t ▹ T"
  (at level 101, t at level 59).
Reserved Notation "Γ '|-' t ◃ T"
  (at level 101, t at level 59).

Unset Elimination Schemes.

Inductive normal : context -> type -> term -> Prop :=
| C_Star Γ : (Γ |- tStar ◃ TUnit)

| C_Abs Γ (A B : type) t :
  (Γ ,, A |- t ◃ B) ->
  Γ |- tLam t ◃ TFun A B

| C_Pair Γ A B a b :
  (Γ |- a ◃ A) ->
  (Γ |- b ◃ B) ->
  (Γ |- tPair a b ◃ TProd A B)

| C_Left Γ A B a :
  (Γ |- a ◃ A) ->
  (Γ |- tLeft a ◃ TSum A B)

| C_Right Γ A B b :
  (Γ |- b ◃ B) ->
  (Γ |- tRight b ◃ TSum A B)

| C_Abort Γ A t :
  (Γ |- t ◃ TEmp) ->
  (Γ |- tAbort t ◃ A)

| C_If Γ A B T s bl br :
  (Γ |- s ▹ TSum A B) ->
  (Γ,,A |- bl ◃ T) ->
  (Γ,,B |- br ◃ T) ->
  (Γ |- tIf s bl br ◃ T)

| C_inf Γ A A' t :
  (Γ |- t ▹ A') ->
  A' = A ->
  (Γ |- t ◃ A)

with neutral : context -> type -> term -> Prop :=
| I_Var Γ n T :
  in_context n Γ T ->
  Γ |- tVar n ▹ T

| I_App Γ A B f u :
  (Γ |- f ▹ TFun A B) ->
  (Γ |- u ◃ A) ->
  Γ |- tApp f u ▹ B

| I_Proj Γ A B (b : bool) t :
  (Γ |- t ▹ TProd A B) ->
  (Γ |- tProj b t ▹ (if b then A else B))

where "Γ '|-' t ▹ T" := (neutral Γ T t) (Γ in scope context_scope)
and "Γ '|-' t ◃ T" := (normal Γ T t) (Γ in scope context_scope).

Hint Constructors neutral normal : core.

Scheme 
Minimality for normal Sort Prop with
Minimality for neutral Sort Prop.

Combined Scheme bidir_ind from normal_ind, neutral_ind.

Definition bidir_concl :=
ltac:(
let t := type of bidir_ind in
let t' := remove_steps t in
exact t').

Arguments bidir_concl Pnf Pne : rename.


Theorem bidir_typing : bidir_concl (fun Γ T t => (Γ |- t :: T)) (fun Γ T t => (Γ |- t :: T)).
Proof.
  apply bidir_ind.
  all: try solve [now econstructor].
  - intros ; now subst.
  - intros.
    destruct b.
    all: now econstructor.
Qed.