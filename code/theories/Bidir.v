From Interpolation Require Import Utils Syntax Typing.
From Stdlib Require Import Relations Arith Lia Bool List.

Reserved Notation "Γ '|-' t ▹ T"
  (at level 101, t at level 59).
Reserved Notation "Γ '|-' t ◃ T"
  (at level 101, t at level 59).

Unset Elimination Schemes.

Inductive check : context -> type -> term -> Prop :=
| C_Star Γ : (Γ |- tStar ◃ TUnit)

| C_Abs Γ (A B : type) t :
  (Γ ,,, A |- t ◃ B) ->
  Γ |- tLam t ◃ TFun A B

| C_Pair Γ A B a b :
  (Γ |- a ◃ A) ->
  (Γ |- b ◃ B) ->
  (Γ |- tPair a b ◃ TProd A B)

| C_inf Γ A A' t :
  (Γ |- t ▹ A') ->
  A' = A ->
  (Γ |- t ◃ A)

with infer : context -> type -> term -> Prop :=
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

where "Γ '|-' t ▹ T" := (infer Γ T t) (Γ in scope context_scope)
and "Γ '|-' t ◃ T" := (check Γ T t) (Γ in scope context_scope).

Hint Constructors check infer : core.

Scheme 
Minimality for check Sort Prop with
Minimality for infer Sort Prop.

Combined Scheme bidir_ind from check_ind, infer_ind.

Definition bidir_concl :=
ltac:(
let t := type of bidir_ind in
let t' := remove_steps t in
exact t').

Arguments bidir_concl Pcheck Pinf : rename.