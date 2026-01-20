From Interpolation Require Import Utils Syntax Notations.
From Stdlib Require Import Setoid Morphisms Relation_Definitions RelationClasses.
From Stdlib Require Import Relations Arith Lia Bool List.

Import ListNotations.

Definition zip (e : elim) (t : term) : term :=
  match e with
  | eProj b => tProj b t
  | eApp u => tApp t u
  | eAbort => tAbort t
  | eIf bl br => tIf t bl br
  end.

Lemma zip_subst e t (σ : subst) : (zip e t)[σ] = zip (e[σ]) (t[σ]).
Proof.
  destruct e ; reflexivity.
Qed.

Lemma zip_ren e t (ρ : ren) : (zip e t)⟨ρ⟩ = zip (e⟨ρ⟩) (t⟨ρ⟩).
Proof.
  substify ; apply zip_subst.
Qed.