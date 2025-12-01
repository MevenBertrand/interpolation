From Stdlib Require Import List.
From Interpolation Require Import Ast.

Import ListNotations.

Fixpoint nth_error {A} (l : list A) (n : nat) : option A :=
  match l, n with
  | nil, _ => None
  | a :: _, 0 => Some a
  | _ :: l', S n' => nth_error l' n'
  end.

(** ** Typing *)

Definition context := list type.

Notation "'ε'" := (@nil type).
Notation "Γ ,,, T" := (@cons type T Γ) (at level 50).
(* 
Notation "'ε'" := (nil :> context) (only parsing).
Notation "Γ ,,, T" := (cons T Γ :> context) (at level 50, only parsing). *)

Definition in_context (n : nat) (Γ : context) (T : type) : Prop :=
  nth_error Γ n = Some T.

Lemma in_zero Γ T : in_context 0 (Γ,,,T) T.
Proof. reflexivity. Qed.

Hint Resolve in_zero : core.