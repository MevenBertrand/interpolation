From Interpolation Require Import Utils Syntax Context.
From Stdlib Require Import Relation_Definitions.

Declare Scope typing_scope.
Delimit Scope typing_scope with ty.

Open Scope typing_scope.

Class HasTyping (Ctx Ty Obj : Type) := typing : Ctx -> Ty -> Obj -> Prop.
Class HasSemTyping (Ctx Ty Obj : Type) := sem_typing : Ctx -> Ty -> Obj -> Prop.
Class HasClosedSemTyping (Ty Obj : Type) := cl_sem_typing : Ty -> Obj -> Prop.
Class HasRed (Obj : Type) := red : relation Obj.
Class HasORed (Obj : Type) := ored : relation Obj.
Class HasConv (Ctx Ty Obj : Type) := conv : Ctx -> Ty -> Obj -> Obj -> Prop.

(** The object t has type A in Γ *)
Notation "Γ '⊢' t '::' T" := (typing Γ T t)
  (at level 101, t at level 59) : typing_scope.

(** The objects t and t' are convertible at type A in Γ *)
Notation "Γ '⊢' t '≡' t' '::' T" := (conv Γ T t t') (at level 101, t, t' at level 59) : typing_scope.

(** The object t is semantically well-typed in Γ *)
Notation "Γ '⊩' t '::' T" := (sem_typing Γ T t)
  (at level 101, t at level 59) : typing_scope.

(** Term t one-step reduces to term t' *)
Notation "t '⤳' t'" := (ored t t') (at level 40) : typing_scope.
(** Term t multi-step reduces to term t' *)
Notation "t '⤳*' t'" := (red t t') (at level 40) : typing_scope.