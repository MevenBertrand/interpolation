(** * Interpolation.BasicAst: parameters for the AST of terms *)

Axiom base : Set.
Axiom eqb_base : base -> base -> bool.
Axiom eqb_base_refl : forall b, eqb_base b b = true.
Axiom eqb_base_sound : forall b b', eqb_base b b' = true -> b = b'.