(** * Interpolation.Elim: operations on eliminators *)
From Interpolation Require Import Utils Syntax.

Import ListNotations.

Section Elims.
Context `{Lang}.

  Definition zip (e : elim) (t : term) : term :=
    match e with
    | eApp u => tApp t u
    | eProj b => tProj b t
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

End Elims.