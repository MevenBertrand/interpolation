From Stdlib Require Import List.
From Interpolation Require Import BasicAst.

Import ListNotations.

Fixpoint nth_error {A} (l : list A) (n : nat) : option A :=
  match l, n with
  | nil, _ => None
  | a :: _, 0 => Some a
  | _ :: l', S n' => nth_error l' n'
  end.

(** ** Contexts *)


Definition context `{b : Base} := list type.

Notation "'ε'" := (@nil type).
Notation "Γ ,, T" := (@cons type T Γ : context) (at level 50).
(* 
Notation "'ε'" := (nil :> context) (only parsing).
Notation "Γ ,, T" := (cons T Γ :> context) (at level 50, only parsing). *)

Section Context.
Context `{b : Base}.

Definition in_context (n : nat) (Γ : context) (T : type) : Prop :=
  nth_error Γ n = Some T.

Lemma in_zero Γ T : in_context 0 (Γ,,T) T.
Proof. reflexivity. Qed.

Hint Resolve in_zero : core.

Lemma in_context_inj (n : nat) (Γ : context) (T T' : type) :
  in_context n Γ T ->
  in_context n Γ T' ->
  T = T'.
Proof.
  intros.
  unfold in_context in *.
  congruence.
Qed.

End Context.