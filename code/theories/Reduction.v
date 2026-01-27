From Interpolation Require Import Utils Syntax Notations Elim.
From Stdlib Require Import Setoid Morphisms Relation_Definitions RelationClasses.
From Stdlib Require Import Relations Arith Lia Bool List.

Import ListNotations.

(** ** Reduction *)

Section Reduction.
  Close Scope typing_scope.

  Inductive term_ored : relation term :=
    (** beta rules *)
    | ST_Beta_Fun t1 v2 :
          tApp (tLam t1) v2 ⤳ t1[v2..]

    | ST_Fst t t' : tFst (tPair t t') ⤳ t
    | ST_Snd t t' : tSnd (tPair t t') ⤳ t'

    | ST_Left t bl br : tIf (tLeft t) bl br ⤳ bl[t..]
    | ST_Right t bl br : tIf (tRight t) bl br ⤳ br[t..]

    (** commuting conversions *)
    | ST_App_Abort u t :
      tApp (tAbort t) u ⤳ tAbort t
    | ST_Proj_Abort b t :
      tProj b (tAbort t) ⤳ tAbort t
    | ST_Abort_Abort t :
      tAbort (tAbort t) ⤳ tAbort t
    | ST_If_Abort bl br t :
      tIf (tAbort t) bl br ⤳ tAbort t

    | ST_App_If u s bl br :
      tApp (tIf s bl br) u ⤳ tIf s (tApp bl u⟨↑⟩) (tApp br u⟨↑⟩)
    | ST_Proj_If b s bl br :
      tProj b (tIf s bl br) ⤳ tIf s (tProj b bl) (tProj b br)
    | ST_Abort_If s bl br :
      tAbort (tIf s bl br) ⤳ tIf s (tAbort bl) (tAbort br)
    | ST_If_If bl br s bl' br' :
      tIf (tIf s bl br) bl' br' ⤳ tIf s (tIf bl bl'⟨⇑ ↑⟩ br'⟨⇑ ↑⟩) (tIf br bl'⟨⇑ ↑⟩ br'⟨⇑ ↑⟩)

    (** congruences *)
    | ST_Lam t t' :
      t ⤳ t' ->
      tLam t ⤳ tLam t'
    | ST_App_l t1 t1' t2 :
          t1 ⤳ t1' ->
          tApp t1 t2 ⤳ tApp t1' t2
    | ST_App_r t1 t2 t2' :
          t2 ⤳ t2' ->
          tApp t1 t2 ⤳ tApp t1 t2'
    | ST_Proj b t t' :
          t ⤳ t' ->
          tProj b t ⤳ tProj b t'
    | ST_Pair_l t1 t1' t2 :
          t1 ⤳ t1' ->
          tPair t1 t2 ⤳ tPair t1' t2
    | ST_Pair_r t1 t2 t2' :
          t2 ⤳ t2' ->
          tPair t1 t2 ⤳ tPair t1 t2'
    | ST_Abort t t' :
        t ⤳ t' ->
        tAbort t ⤳ tAbort t'
    | ST_In b t t' :
      t ⤳ t' ->
      tIn b t ⤳ tIn b t'
    | ST_If_s s s' bl br :
      s ⤳ s' ->
      tIf s bl br ⤳ tIf s' bl br
    | ST_If_l s bl bl' br :
      bl ⤳ bl' ->
      tIf s bl br ⤳ tIf s bl' br
    | ST_If_r s bl br br' :
      br ⤳ br' ->
      tIf s bl br ⤳ tIf s bl br'

  where "t '⤳' t'" := (term_ored t t').

End Reduction.

Hint Constructors term_ored : core.

Notation term_red := (clos_refl_trans term term_ored).

#[export] Instance HasORedTm : HasORed term := term_ored.
#[export] Instance HasRedTm : HasRed term := term_red.

#[export] Instance HasRedSubst : HasRed subst :=
  fun σ τ => forall i, σ i ⤳* τ i.

  Ltac fold_red :=
    change term_ored with ored in * ;
    change term_red with red in *.

  Smpl Add fold_red : refold.

Section Properties.
  #[local] Notation red := (Notations.red (Obj := term)) (only parsing).
  #[local] Notation sred := (Notations.red (Obj := subst)) (only parsing).

  Instance red_po : PreOrder red.
  Proof.
    constructor.
    all: now econstructor.
  Qed.

  Instance sred_po : PreOrder sred.
  Proof.
    unfold red, HasRedSubst.
    constructor.
    all: intros ? **.
    1: reflexivity.
    etransitivity ; eauto.
  Qed.

  Instance ored_red : subrelation ored red.
  Proof.
    intros ?? ?.
    now constructor.
  Qed.

  Instance R_App_cong :
    Proper (red ==> red ==> red) tApp.
  Proof.
    intros ?? Hf ?? Hu ; unfold Notations.red, HasRedTm in *.
    induction Hf using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
    induction Hu using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
  Qed.

  Instance R_Lam_cong : Proper (red ==> red) tLam.
  Proof.
    intros ?? Ht ; unfold Notations.red, HasRedTm in *.
    induction Ht using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
  Qed.

  Instance R_Proj_cong : Proper (eq ==> red ==> red) tProj.
  Proof.
    intros ?? -> ?? Hred ; unfold Notations.red, HasRedTm in *.
    induction Hred using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
  Qed.

  Instance R_Pair_cong : Proper (red ==> red ==> red) tPair.
  Proof.
    intros ?? Hp ?? Hq ; unfold Notations.red, HasRedTm in *.
    induction Hp using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
    induction Hq using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
  Qed.

  Instance R_Abort_cong : Proper (red ==> red) tAbort.
  Proof.
    intros ?? Ht ; unfold Notations.red, HasRedTm in *.
    induction Ht using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
  Qed.

  Instance R_In_cong : Proper (eq ==> red ==> red) tIn.
  Proof.
    intros ?? -> ?? Hred ; unfold Notations.red, HasRedTm in *.
    induction Hred using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
  Qed.

  Instance R_If_cong : Proper (red ==> red ==> red ==> red) tIf.
  Proof.
    intros ?? Hs ?? Hl ?? Hr ; unfold Notations.red, HasRedTm in *.
    induction Hs using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
    induction Hl using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
    induction Hr using clos_refl_trans_ind_left ; eauto using rt_refl, rt_step, rt_trans.
  Qed.

  Instance ST_ren : Proper ((pointwise_relation _ eq) ==> ored ==> ored) ren1.
  Proof.
    intros ρ ρ' Hren t t' Ht.
    rewrite <- Hren ; clear ρ' Hren.
    induction Ht in ρ |- * ; cbn ; refold ;
      rewrite ?subst1_ren, ?up_lift_ren, ?up_lift_up_ren ; now constructor.
  Qed.

  Instance R_ren : Proper ((pointwise_relation _ eq) ==> red ==> red) ren1.
  Proof.
    intros ρ ρ' Hren t t' Ht.
    rewrite <- Hren ; clear ρ' Hren.
    induction Ht.
    all: try solve [now econstructor].
    econstructor.
    now apply ST_ren.
  Qed.

  Lemma R_lift : Proper (sred ==> sred) up_term_term.
  Proof.
    intros ?? ? [|] ; cbn.
    - reflexivity.
    - rewrite R_ren ; try reflexivity.
      auto.
  Qed.

  Instance R_scons : Proper (red ==> sred ==> sred) scons.
  Proof.
    intros ?? ? ?? ? [|]; cbn ; easy.
  Qed.

  Instance R_subst_same : Proper (sred ==> @eq term ==> red) subst1.
  Proof.
    intros σ τ Hsubst ? t ->.
    induction t in σ, τ, Hsubst |- * ; cbn.
    all: try solve [reflexivity|rewrite IHt ; tea ; reflexivity].
    - apply Hsubst.
    - erewrite IHt1, IHt2 ; tea ; reflexivity.
    - rewrite IHt.
      1: reflexivity.
      now apply R_lift.
    - erewrite IHt1, IHt2 ; tea ; reflexivity.
    - erewrite IHt1, IHt2, IHt3 ; tea.
      1: reflexivity.
      all: now apply R_lift.
  Qed.

  Instance R_cons : Proper (red ==> sred ==> sred) scons.
  Proof.
    intros ?? Ht ?? Hσ [|] ; now cbn.
  Qed.

  Instance ST_subst : Proper ((pointwise_relation _ eq) ==> ored (Obj := term) ==> ored) subst1.
  Proof.
    intros σ σ' Hsubst t t' Ht.
    rewrite <- Hsubst ; clear σ' Hsubst.
    induction Ht in σ |- * ;
      cbn ; rewrite ?subst1_subst, ?up_lift_subst, ?up_lift_up_subst ; now constructor.
  Qed.

  Instance R_subst : Proper (sred ==> red ==> red) subst1.
  Proof.
    intros σ σ' Hsubst t t' Ht.
    etransitivity.
    1: now apply R_subst_same.
    clear -Ht.
    induction Ht ; try solve [now econstructor].
    constructor.
    now apply ST_subst.
  Qed.

End Properties.

#[global]Existing Instances red_po sred_po ored_red R_App_cong R_Lam_cong R_Proj_cong R_Pair_cong R_Abort_cong R_In_cong R_If_cong R_ren
  R_lift R_cons R_subst.