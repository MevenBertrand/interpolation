From Interpolation Require Import Utils Syntax Notations Elim Reduction.

(** ** Confluence of commuting conversion *)

Section CommutConfluence.
  Context `{l : Lang}.

  Close Scope typing_scope.

  (** *** Commuting conversion *)
  Inductive commut : relation term :=

    | C_Comm_Abort e t :
      zip e (tAbort t) ⤳ tAbort t

    | C_Comm_If e s bl br :
      zip e (tIf s bl br) ⤳ tIf s (zip e⟨↑⟩ bl) (zip e⟨↑⟩ br)

    (** congruences *)
    | C_Lam t t' :
      t ⤳ t' ->
      tLam t ⤳ tLam t'
    | C_App_l t1 t1' t2 :
          t1 ⤳ t1' ->
          tApp t1 t2 ⤳ tApp t1' t2
    | C_App_r t1 t2 t2' :
          t2 ⤳ t2' ->
          tApp t1 t2 ⤳ tApp t1 t2'
    | C_Proj b t t' :
          t ⤳ t' ->
          tProj b t ⤳ tProj b t'
    | C_Pair_l t1 t1' t2 :
          t1 ⤳ t1' ->
          tPair t1 t2 ⤳ tPair t1' t2
    | C_Pair_r t1 t2 t2' :
          t2 ⤳ t2' ->
          tPair t1 t2 ⤳ tPair t1 t2'
    | C_Abort t t' :
        t ⤳ t' ->
        tAbort t ⤳ tAbort t'
    | C_In b t t' :
      t ⤳ t' ->
      tIn b t ⤳ tIn b t'
    | C_If_s s s' bl br :
      s ⤳ s' ->
      tIf s bl br ⤳ tIf s' bl br
    | C_If_l s bl bl' br :
      bl ⤳ bl' ->
      tIf s bl br ⤳ tIf s bl' br
    | C_If_r s bl br br' :
      br ⤳ br' ->
      tIf s bl br ⤳ tIf s bl br'

  (** In this section we use the reduction symbol for this reduction *)
  where "t '⤳' t'" := (commut t t').

  Notation "t '⤳*' t'" := (clos_refl_trans term commut t t').

  (** *** Size *)

  Fixpoint size (t : term) : nat :=
    match t with
    | tVar _ | tStar | tConst _ => 1
    | tPair p q => 1 + size p + size q
    | tProj _ p => 1 + 3*(size p)
    | tLam t => 1 + size t
    | tApp f u => 1 + (size f)*(3 + size u)
    | tAbort t => 1 + 3*(size t)
    | tIn _ t => 1 + (size t)
    | tIf s bl br => 1 + (size s)*(3 + size bl + size br)
    end.

  Lemma size_ren (t : term) (ρ : ren) : size (t⟨ρ⟩) = size t.
  Proof.
    induction t in ρ |- * ; cbn.
    all: repeat (match goal with | IH : forall ρ, size _ = size _ |- _ => rewrite IH end).
    all: lia.
  Qed.

  Lemma size_ren_subst (t : term) (ρ : ren) : size (t[ρ >> tVar]) = size t.
  Proof.
    renamify ; refold.
    apply size_ren.
  Qed.

  Lemma size_pos (t : term) : 0 < size t.
  Proof.
    destruct t ; cbn ; lia.
  Qed.

  Lemma up_ren_subst (ρ : nat -> nat) : ⇑ (ρ >> tVar) =1 (⇑ ρ) >> tVar.
  Proof.
    asimpl ; unfold up_term_ren ; now asimpl.
  Qed.

  (** Size decreases along reductions *)
  Lemma commut_lt (t t' : term) : t ⤳ t' -> size t' < size t.
  Proof.
    induction 1.
    all: (try match goal with | e : elim |- _ => destruct e end) ;
      cbn -[Nat.add Nat.mul] ; refold.
    all: rewrite ?up_ren_subst, ?size_ren_subst.
    all: try solve [nia].
    - pose proof (size_pos t1).
      nia.
    - pose proof (size_pos s).
      nia.
    - pose proof (size_pos s).
      nia.
  Qed.

  (** Thus the reduction is strongly normalising *)

  Corollary strong_nor : well_founded (flip commut).
  Proof.
    eapply well_founded_lt_compat.
    unfold flip.
    intros *.
    apply commut_lt.
  Qed.

  (** Local confluence is admitted *)
  Lemma loc_confluent (t u u' : term) : t ⤳ u -> t ⤳ u' -> exists v, u ⤳* v /\ u' ⤳* v.
  Proof.
    (** This is proven by CSIho *)
  Admitted.

  Definition nf t := ~ (exists t', t ⤳ t').

  Lemma rt_inv_l {A} {R : relation A} a a' :
    clos_refl_trans _ R a a' ->
    a = a' \/ exists a'', R a a'' /\ clos_refl_trans _ R a'' a'.
  Proof.
    intros H.
    induction H.
    - right.
      now eexists.
    - now left.
    - destruct IHclos_refl_trans1 as [->|(?&?&?)].
      1: easy.
      
      right ; eexists.
      split ; [easy|].
      now etransitivity.
  Qed.
     
  (** We derive confluence *)
  Lemma confluent (t u u' : term) : t ⤳* u -> t ⤳* u' -> exists v, u ⤳* v /\ u' ⤳* v.
  Proof.
    revert u u'.
    pattern t.
    revert t.
    unshelve eapply well_founded_ind.
    2: apply strong_nor.
    intros t IH u u' Hred Hred'.
    unfold flip in IH.
    apply rt_inv_l in Hred as [<- | (t'&Hredt1&Hredt')].
    1: now exists u'.
    apply rt_inv_l in Hred' as [<- | (t''&Hredt2&Hredt'')].
    1: exists u ; split ; [easy|] ; etransitivity ; tea ; now econstructor.
    edestruct (loc_confluent t t' t'') as (v&Hredv1&Hredv2); tea.
    unshelve epose proof (IH t' _ u v _ _) as (v'&Hredu&Hredv); tea.
    unshelve epose proof (IH t'' _ u' v' _ _) as (v''&Hredu'&Hredv'); tea.
    1: now etransitivity.
    exists v'' ; split ; eauto.
    now etransitivity.
  Qed.
  
End CommutConfluence.

(** We do not prove confluence of β or commutation, so we admit confluence
  of the full reduction relation (ie containing β and commuting conversions) *)
Axiom confluence : forall `{Lang} (t u u' : term),
  (t ⤳* u) -> (t ⤳* u') -> exists v, (u ⤳* v) /\ (u' ⤳* v).