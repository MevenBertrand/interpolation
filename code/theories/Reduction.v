From Interpolation Require Import Utils Syntax.
From Stdlib Require Import Relations Arith Lia Bool List RelationClasses.

Import ListNotations.

(** ** Reduction *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : term -> term -> Prop :=
  | ST_Beta t1 v2 :
        tApp (tLam t1) v2 --> t1[v2..]
  | ST_App_l t1 t1' t2 :
         t1 --> t1' ->
         tApp t1 t2 --> tApp t1' t2
  | ST_App_r t1 t2 t2' :
         t2 --> t2' ->
         tApp t1 t2 --> tApp t1 t2'
  | ST_Lam t t' :
    t --> t' ->
    tLam t --> tLam t'
  | ST_Fst t t' : tFst (tPair t t') --> t
  | ST_Snd t t' : tSnd (tPair t t') --> t'
  | ST_Proj b t t' :
         t --> t' ->
         tProj b t --> tProj b t'
  | ST_Pair_l t1 t1' t2 :
         t1 --> t1' ->
         tPair t1 t2 --> tPair t1' t2
  | ST_Par_r t1 t2 t2' :
         t2 --> t2' ->
         tPair t1 t2 --> tPair t1 t2'

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (clos_refl_trans term step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Instance red_po : PreOrder multistep.
Proof.
  constructor.
  all: now econstructor.
Qed.

Lemma R_App_cong f f' u u':
  f -->* f' ->
  u -->* u' ->
  tApp f u -->* tApp f' u'.
Proof.
  intros Hf Hu.
  induction Hf using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
  induction Hu using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
Qed.

Lemma R_Lam_cong t t':
  t -->* t' ->
  tLam t -->* tLam t'.
Proof.
  intros Ht.
  induction Ht using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
Qed.

Lemma R_Proj_cong b t t' :
  t -->* t' ->
  tProj b t -->* tProj b t'.
Proof.
  intros Hred.
  induction Hred using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
Qed.

Lemma R_Pair_cong p p' q q':
  p -->* p' ->
  q -->* q' ->
  tPair p q -->* tPair p' q'.
Proof.
  intros Hp Hq.
  induction Hp using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
  induction Hq using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
Qed.
