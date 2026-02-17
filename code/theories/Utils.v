(** * Interpolation.Utils: Generic utilities *)
From stdpp Require Export propset.
From Stdlib Require Export Bool List Lia Morphisms Relations RelationClasses.
From smpl Require Import Smpl.

#[export] Set Structural Injection.
#[export] Add Search Blacklist "_ind" "_sind" "_rec" "_rect".
#[export] Set Default Goal Selector "!".
#[export] Set Keyed Unification.

(** ** Notations *)

Disable Notation "↑".

Notation "`=1`" := (pointwise_relation _ Logic.eq) (at level 80).
Infix "=1" := (pointwise_relation _ Logic.eq) (at level 70).

(** ** Tactics *)

Hint Constructors eq : core.
Hint Extern 10 => reflexivity : core.

#[global]Hint Unfold notT: core.
#[global] Hint Resolve eq_refl eq_sym : core.
#[global] Hint Constructors and : core. 
#[global]Hint Extern 10 =>
  match goal with
    | H : False |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | H : ~ _ |- False => apply H
  end : core.

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