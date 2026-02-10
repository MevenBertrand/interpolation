(** * Interpolation.BasicAst: parameters for the AST of terms *)

Set Primitive Projections.

Class Base : Type := {base : Set}.
(* Axiom eqb_base : base -> base -> bool.
Axiom eqb_base_refl : forall b, eqb_base b b = true.
Axiom eqb_base_sound : forall b b', eqb_base b b' = true -> b = b'. *)

Inductive type `{b : Base} :=
  | TBase : base -> type
  | TUnit : type
  | TProd : type -> type -> type
  | TFun : type -> type -> type
  | TEmp : type
  | TSum : type -> type -> type.

Class Lang `{ba : Base} : Type := {
  const : Set ;
  const_type : const -> type
}.

Definition EmptyLang `{b : Base} : Lang := {|
  const := False ;
  const_type := fun (e : False) => False_rec _ e
|}.

Inductive polarity := | pos | neg.

Definition negp (p : polarity) := if p then neg else pos.

Lemma negp_inv p : negp (negp p) = p.
Proof.
  now destruct p.
Qed.