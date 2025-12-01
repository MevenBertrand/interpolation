From Stdlib Require Import Morphisms List RelationClasses.
From smpl Require Import Smpl.

#[export] Set Structural Injection.
#[export] Add Search Blacklist "_ind" "_sind" "_rec" "_rect".
#[export] Set Default Goal Selector "!".

(** ** Subtypes *)

Definition incl {A : Type} : (A -> Prop) -> (A -> Prop) -> Prop :=
  fun P Q => forall x, P x -> Q x.

Notation "P ⊆ Q" := (incl P Q) (at level 90).

Definition inter {A : Type} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
  fun P Q x => P x /\ Q x.

Notation "P ∩ Q" := (inter P Q) (at level 80).

Arguments inter _ _ _ _/.

Definition union {A : Type} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
  fun P Q x => P x \/ Q x.

Notation "P ∪ Q" := (union P Q) (at level 85).

Arguments union _ _ _ _/.

Definition empty {A : Type} : A -> Prop := fun _ => False.

Notation "∅" := empty.

Definition sing {A : Type} (a : A) : A -> Prop := fun x => x = a.

Arguments sing _ _ _/.

(** ** Notations *)

Notation "`=1`" := (pointwise_relation _ Logic.eq) (at level 80).
Infix "=1" := (pointwise_relation _ Logic.eq) (at level 70).

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

(** An arbitrary reflexive relation relates equal terms *)
Lemma ereflexivity {A} {R} `{Reflexive A R} {x y} :
  x = y -> R x y.
Proof.
  intros ->.
  reflexivity.
Qed.

(** A general refolding tactic to recover lost typeclasses
  (due for instance to the cbn or constructor tactics).
  Updated on the fly using the Smpl plugin. *)
Smpl Create refold [progress].

Ltac refold := repeat (smpl refold).

Ltac core_constructor := constructor.
Tactic Notation "constructor" := core_constructor ; refold.

Ltac core_econstructor := econstructor.
Tactic Notation "econstructor" := core_econstructor ; refold.

(** Tactics used to create good induction principles using Scheme *)

Ltac remove_steps t :=
  lazymatch t with
  | _ -> ?T => remove_steps T
  | forall x : ?Hyp, @?T x => constr:(fun  x : Hyp => ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := remove_steps T' in exact T''))
  | ?t' => t'
  end.