From Stdlib Require Import Morphisms List CRelationClasses.
From smpl Require Import Smpl.

(** ** Tactics *)

(* To use in intro patterns, similar to SSReflects' /dup view *)
Definition dup {A : Type} : A -> A * A := fun x => (x,x).

Ltac tea := try eassumption.
#[global] Ltac easy ::= solve [intuition eauto 3 with core crelations].

Ltac prod_splitter :=
  repeat match goal with
  | |- sigT _ => eexists
  | |- prod _ _ => split
  | |- _ /\ _ => split
  end.

(** A general refolding tactic to recover lost typeclasses
  (due for instance to the cbn or constructor tactics).
  Updated on the fly using the Smpl plugin. *)
Smpl Create refold [progress].

Ltac refold := repeat (smpl refold).

Ltac core_constructor := constructor.
Tactic Notation "constructor" := core_constructor ; refold.

Ltac core_econstructor := econstructor.
Tactic Notation "econstructor" := core_econstructor ; refold.