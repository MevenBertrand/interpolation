From Interpolation Require Import core unscoped.
From Interpolation Require Import BasicAst.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Section Lang.
Context `{Lang}.

Inductive term : Type :=
  | tVar : nat -> term
  | tConst : const -> term
  | tStar : term
  | tPair : term -> term -> term
  | tProj : bool -> term -> term
  | tLam : term -> term
  | tApp : term -> term -> term
  | tAbort : term -> term
  | tIn : bool -> term -> term
  | tIf : term -> term -> term -> term.

Lemma congr_tConst {s0 : const} {t0 : const} (H0 : s0 = t0) :
  tConst s0 = tConst t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tConst x) H0)).
Qed.

Lemma congr_tStar : tStar = tStar.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tPair {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : tPair s0 s1 = tPair t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tPair x s1) H0))
         (ap (fun x => tPair t0 x) H1)).
Qed.

Lemma congr_tProj {s0 : bool} {s1 : term} {t0 : bool} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : tProj s0 s1 = tProj t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tProj x s1) H0))
         (ap (fun x => tProj t0 x) H1)).
Qed.

Lemma congr_tLam {s0 : term} {t0 : term} (H0 : s0 = t0) : tLam s0 = tLam t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tLam x) H0)).
Qed.

Lemma congr_tApp {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : tApp s0 s1 = tApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tApp x s1) H0))
         (ap (fun x => tApp t0 x) H1)).
Qed.

Lemma congr_tAbort {s0 : term} {t0 : term} (H0 : s0 = t0) :
  tAbort s0 = tAbort t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tAbort x) H0)).
Qed.

Lemma congr_tIn {s0 : bool} {s1 : term} {t0 : bool} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : tIn s0 s1 = tIn t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tIn x s1) H0))
         (ap (fun x => tIn t0 x) H1)).
Qed.

Lemma congr_tIf {s0 : term} {s1 : term} {s2 : term} {t0 : term} {t1 : term}
  {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  tIf s0 s1 s2 = tIf t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tIf x s1 s2) H0))
            (ap (fun x => tIf t0 x s2) H1))
         (ap (fun x => tIf t0 t1 x) H2)).
Qed.

Lemma upRen_term_term (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_term (xi_term : nat -> nat) (s : term) {struct s} : term :=
  match s with
  | tVar s0 => tVar (xi_term s0)
  | tConst s0 => tConst s0
  | tStar => tStar
  | tPair s0 s1 => tPair (ren_term xi_term s0) (ren_term xi_term s1)
  | tProj s0 s1 => tProj s0 (ren_term xi_term s1)
  | tLam s0 => tLam (ren_term (upRen_term_term xi_term) s0)
  | tApp s0 s1 => tApp (ren_term xi_term s0) (ren_term xi_term s1)
  | tAbort s0 => tAbort (ren_term xi_term s0)
  | tIn s0 s1 => tIn s0 (ren_term xi_term s1)
  | tIf s0 s1 s2 =>
      tIf (ren_term xi_term s0) (ren_term (upRen_term_term xi_term) s1)
        (ren_term (upRen_term_term xi_term) s2)
  end.

Lemma up_term_term (sigma : nat -> term) : nat -> term.
Proof.
exact (scons (tVar var_zero) (funcomp (ren_term shift) sigma)).
Defined.

Fixpoint subst_term (sigma_term : nat -> term) (s : term) {struct s} : 
term :=
  match s with
  | tVar s0 => sigma_term s0
  | tConst s0 => tConst s0
  | tStar => tStar
  | tPair s0 s1 =>
      tPair (subst_term sigma_term s0) (subst_term sigma_term s1)
  | tProj s0 s1 => tProj s0 (subst_term sigma_term s1)
  | tLam s0 => tLam (subst_term (up_term_term sigma_term) s0)
  | tApp s0 s1 => tApp (subst_term sigma_term s0) (subst_term sigma_term s1)
  | tAbort s0 => tAbort (subst_term sigma_term s0)
  | tIn s0 s1 => tIn s0 (subst_term sigma_term s1)
  | tIf s0 s1 s2 =>
      tIf (subst_term sigma_term s0)
        (subst_term (up_term_term sigma_term) s1)
        (subst_term (up_term_term sigma_term) s2)
  end.

Lemma upId_term_term (sigma : nat -> term) (Eq : forall x, sigma x = tVar x)
  : forall x, up_term_term sigma x = tVar x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_term (sigma_term : nat -> term)
(Eq_term : forall x, sigma_term x = tVar x) (s : term) {struct s} :
subst_term sigma_term s = s :=
  match s with
  | tVar s0 => Eq_term s0
  | tConst s0 => congr_tConst (eq_refl s0)
  | tStar => congr_tStar
  | tPair s0 s1 =>
      congr_tPair (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  | tProj s0 s1 =>
      congr_tProj (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
  | tLam s0 =>
      congr_tLam
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s0)
  | tApp s0 s1 =>
      congr_tApp (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  | tAbort s0 => congr_tAbort (idSubst_term sigma_term Eq_term s0)
  | tIn s0 s1 => congr_tIn (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
  | tIf s0 s1 s2 =>
      congr_tIf (idSubst_term sigma_term Eq_term s0)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s2)
  end.

Lemma upExtRen_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_term_term xi x = upRen_term_term zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(Eq_term : forall x, xi_term x = zeta_term x) (s : term) {struct s} :
ren_term xi_term s = ren_term zeta_term s :=
  match s with
  | tVar s0 => ap (tVar) (Eq_term s0)
  | tConst s0 => congr_tConst (eq_refl s0)
  | tStar => congr_tStar
  | tPair s0 s1 =>
      congr_tPair (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  | tProj s0 s1 =>
      congr_tProj (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
  | tLam s0 =>
      congr_tLam
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s0)
  | tApp s0 s1 =>
      congr_tApp (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  | tAbort s0 => congr_tAbort (extRen_term xi_term zeta_term Eq_term s0)
  | tIn s0 s1 =>
      congr_tIn (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
  | tIf s0 s1 s2 =>
      congr_tIf (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s2)
  end.

Lemma upExt_term_term (sigma : nat -> term) (tau : nat -> term)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_term_term sigma x = up_term_term tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_term (sigma_term : nat -> term) (tau_term : nat -> term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : term) {struct s} :
subst_term sigma_term s = subst_term tau_term s :=
  match s with
  | tVar s0 => Eq_term s0
  | tConst s0 => congr_tConst (eq_refl s0)
  | tStar => congr_tStar
  | tPair s0 s1 =>
      congr_tPair (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  | tProj s0 s1 =>
      congr_tProj (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
  | tLam s0 =>
      congr_tLam
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s0)
  | tApp s0 s1 =>
      congr_tApp (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  | tAbort s0 => congr_tAbort (ext_term sigma_term tau_term Eq_term s0)
  | tIn s0 s1 =>
      congr_tIn (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
  | tIf s0 s1 s2 =>
      congr_tIf (ext_term sigma_term tau_term Eq_term s0)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s2)
  end.

Lemma up_ren_ren_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_term_term zeta) (upRen_term_term xi) x =
  upRen_term_term rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(rho_term : nat -> nat)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : term)
{struct s} : ren_term zeta_term (ren_term xi_term s) = ren_term rho_term s :=
  match s with
  | tVar s0 => ap (tVar) (Eq_term s0)
  | tConst s0 => congr_tConst (eq_refl s0)
  | tStar => congr_tStar
  | tPair s0 s1 =>
      congr_tPair (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | tProj s0 s1 =>
      congr_tProj (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | tLam s0 =>
      congr_tLam
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s0)
  | tApp s0 s1 =>
      congr_tApp (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | tAbort s0 =>
      congr_tAbort (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
  | tIn s0 s1 =>
      congr_tIn (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | tIf s0 s1 s2 =>
      congr_tIf (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s2)
  end.

Lemma up_ren_subst_term_term (xi : nat -> nat) (tau : nat -> term)
  (theta : nat -> term) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_term_term tau) (upRen_term_term xi) x = up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : term)
{struct s} :
subst_term tau_term (ren_term xi_term s) = subst_term theta_term s :=
  match s with
  | tVar s0 => Eq_term s0
  | tConst s0 => congr_tConst (eq_refl s0)
  | tStar => congr_tStar
  | tPair s0 s1 =>
      congr_tPair (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | tProj s0 s1 =>
      congr_tProj (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | tLam s0 =>
      congr_tLam
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s0)
  | tApp s0 s1 =>
      congr_tApp (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | tAbort s0 =>
      congr_tAbort (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
  | tIn s0 s1 =>
      congr_tIn (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | tIf s0 s1 s2 =>
      congr_tIf (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s2)
  end.

Lemma up_subst_ren_term_term (sigma : nat -> term) (zeta_term : nat -> nat)
  (theta : nat -> term)
  (Eq : forall x, funcomp (ren_term zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_term shift (upRen_term_term zeta_term)
                (funcomp shift zeta_term) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_term zeta_term shift (funcomp shift zeta_term)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_term (sigma_term : nat -> term)
(zeta_term : nat -> nat) (theta_term : nat -> term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : term) {struct s} :
ren_term zeta_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | tVar s0 => Eq_term s0
  | tConst s0 => congr_tConst (eq_refl s0)
  | tStar => congr_tStar
  | tPair s0 s1 =>
      congr_tPair
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | tProj s0 s1 =>
      congr_tProj (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | tLam s0 =>
      congr_tLam
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s0)
  | tApp s0 s1 =>
      congr_tApp
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | tAbort s0 =>
      congr_tAbort
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
  | tIn s0 s1 =>
      congr_tIn (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | tIf s0 s1 s2 =>
      congr_tIf
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s2)
  end.

Lemma up_subst_subst_term_term (sigma : nat -> term) (tau_term : nat -> term)
  (theta : nat -> term)
  (Eq : forall x, funcomp (subst_term tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_term shift (up_term_term tau_term)
                (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_term tau_term shift
                      (funcomp (ren_term shift) tau_term) (fun x => eq_refl)
                      (sigma n')))
                (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_term (sigma_term : nat -> term)
(tau_term : nat -> term) (theta_term : nat -> term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : term) {struct s} :
subst_term tau_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | tVar s0 => Eq_term s0
  | tConst s0 => congr_tConst (eq_refl s0)
  | tStar => congr_tStar
  | tPair s0 s1 =>
      congr_tPair
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | tProj s0 s1 =>
      congr_tProj (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | tLam s0 =>
      congr_tLam
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s0)
  | tApp s0 s1 =>
      congr_tApp
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | tAbort s0 =>
      congr_tAbort
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
  | tIn s0 s1 =>
      congr_tIn (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | tIf s0 s1 s2 =>
      congr_tIf
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s2)
  end.

Lemma renRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat) (s : term)
  :
  ren_term zeta_term (ren_term xi_term s) =
  ren_term (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_term_pointwise (xi_term : nat -> nat) (zeta_term : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_term zeta_term) (ren_term xi_term))
    (ren_term (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (ren_term xi_term s) =
  subst_term (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term_pointwise (xi_term : nat -> nat) (tau_term : nat -> term)
  :
  pointwise_relation _ eq (funcomp (subst_term tau_term) (ren_term xi_term))
    (subst_term (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term (sigma_term : nat -> term) (zeta_term : nat -> nat)
  (s : term) :
  ren_term zeta_term (subst_term sigma_term s) =
  subst_term (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term_pointwise (sigma_term : nat -> term)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_term zeta_term) (subst_term sigma_term))
    (subst_term (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s => compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (subst_term sigma_term s) =
  subst_term (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_term tau_term) (subst_term sigma_term))
    (subst_term (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_term_term (xi : nat -> nat) (sigma : nat -> term)
  (Eq : forall x, funcomp (tVar) xi x = sigma x) :
  forall x, funcomp (tVar) (upRen_term_term xi) x = up_term_term sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_term (xi_term : nat -> nat) (sigma_term : nat -> term)
(Eq_term : forall x, funcomp (tVar) xi_term x = sigma_term x) (s : term)
{struct s} : ren_term xi_term s = subst_term sigma_term s :=
  match s with
  | tVar s0 => Eq_term s0
  | tConst s0 => congr_tConst (eq_refl s0)
  | tStar => congr_tStar
  | tPair s0 s1 =>
      congr_tPair (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | tProj s0 s1 =>
      congr_tProj (eq_refl s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | tLam s0 =>
      congr_tLam
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s0)
  | tApp s0 s1 =>
      congr_tApp (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | tAbort s0 => congr_tAbort (rinst_inst_term xi_term sigma_term Eq_term s0)
  | tIn s0 s1 =>
      congr_tIn (eq_refl s0) (rinst_inst_term xi_term sigma_term Eq_term s1)
  | tIf s0 s1 s2 =>
      congr_tIf (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s2)
  end.

Lemma rinstInst'_term (xi_term : nat -> nat) (s : term) :
  ren_term xi_term s = subst_term (funcomp (tVar) xi_term) s.
Proof.
exact (rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_term xi_term)
    (subst_term (funcomp (tVar) xi_term)).
Proof.
exact (fun s => rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_term (s : term) : subst_term (tVar) s = s.
Proof.
exact (idSubst_term (tVar) (fun n => eq_refl) s).
Qed.

Lemma instId'_term_pointwise : pointwise_relation _ eq (subst_term (tVar)) id.
Proof.
exact (fun s => idSubst_term (tVar) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_term (s : term) : ren_term id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma rinstId'_term_pointwise : pointwise_relation _ eq (@ren_term id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma varL'_term (sigma_term : nat -> term) (x : nat) :
  subst_term sigma_term (tVar x) = sigma_term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_term_pointwise (sigma_term : nat -> term) :
  pointwise_relation _ eq (funcomp (subst_term sigma_term) (tVar)) sigma_term.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_term (xi_term : nat -> nat) (x : nat) :
  ren_term xi_term (tVar x) = tVar (xi_term x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_term xi_term) (tVar))
    (funcomp (tVar) xi_term).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive elim : Type :=
  | eProj : bool -> elim
  | eApp : term -> elim
  | eAbort : elim
  | eIf : term -> term -> elim.

Lemma congr_eProj {s0 : bool} {t0 : bool} (H0 : s0 = t0) :
  eProj s0 = eProj t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => eProj x) H0)).
Qed.

Lemma congr_eApp {s0 : term} {t0 : term} (H0 : s0 = t0) : eApp s0 = eApp t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => eApp x) H0)).
Qed.

Lemma congr_eAbort : eAbort = eAbort.
Proof.
exact (eq_refl).
Qed.

Lemma congr_eIf {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : eIf s0 s1 = eIf t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => eIf x s1) H0))
         (ap (fun x => eIf t0 x) H1)).
Qed.

Definition subst_elim (sigma_term : nat -> term) (s : elim) : elim :=
  match s with
  | eProj s0 => eProj s0
  | eApp s0 => eApp (subst_term sigma_term s0)
  | eAbort => eAbort
  | eIf s0 s1 =>
      eIf (subst_term (up_term_term sigma_term) s0)
        (subst_term (up_term_term sigma_term) s1)
  end.

Definition idSubst_elim (sigma_term : nat -> term)
  (Eq_term : forall x, sigma_term x = tVar x) (s : elim) :
  subst_elim sigma_term s = s :=
  match s with
  | eProj s0 => congr_eProj (eq_refl s0)
  | eApp s0 => congr_eApp (idSubst_term sigma_term Eq_term s0)
  | eAbort => congr_eAbort
  | eIf s0 s1 =>
      congr_eIf
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s0)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
  end.

Definition ext_elim (sigma_term : nat -> term) (tau_term : nat -> term)
  (Eq_term : forall x, sigma_term x = tau_term x) (s : elim) :
  subst_elim sigma_term s = subst_elim tau_term s :=
  match s with
  | eProj s0 => congr_eProj (eq_refl s0)
  | eApp s0 => congr_eApp (ext_term sigma_term tau_term Eq_term s0)
  | eAbort => congr_eAbort
  | eIf s0 s1 =>
      congr_eIf
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s0)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
  end.

Definition compSubstSubst_elim (sigma_term : nat -> term)
  (tau_term : nat -> term) (theta_term : nat -> term)
  (Eq_term : forall x,
             funcomp (subst_term tau_term) sigma_term x = theta_term x)
  (s : elim) :
  subst_elim tau_term (subst_elim sigma_term s) = subst_elim theta_term s :=
  match s with
  | eProj s0 => congr_eProj (eq_refl s0)
  | eApp s0 =>
      congr_eApp
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
  | eAbort => congr_eAbort
  | eIf s0 s1 =>
      congr_eIf
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s0)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
  end.

Lemma substSubst_elim (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : elim) :
  subst_elim tau_term (subst_elim sigma_term s) =
  subst_elim (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_elim sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_elim_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_elim tau_term) (subst_elim sigma_term))
    (subst_elim (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_elim sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_elim (s : elim) : subst_elim (tVar) s = s.
Proof.
exact (idSubst_elim (tVar) (fun n => eq_refl) s).
Qed.

Lemma instId'_elim_pointwise : pointwise_relation _ eq (subst_elim (tVar)) id.
Proof.
exact (fun s => idSubst_elim (tVar) (fun n => eq_refl) s).
Qed.

End Lang.

Class Up_elim X Y :=
    up_elim : X -> Y.

Class Up_term X Y :=
    up_term : X -> Y.

#[global] Instance Subst_elim `{Lang} : (Subst1 _ _ _) := @subst_elim _ _.

#[global] Instance Subst_term `{Lang} : (Subst1 _ _ _) := @subst_term _ _.

#[global] Instance Up_term_term `{Lang} : (Up_term _ _) := @up_term_term _ _.

#[global] Instance Ren_term `{Lang} : (Ren1 _ _ _) := @ren_term _ _.

#[global]
Instance VarInstance_term `{Lang} : (Var _ _) := @tVar _ _.

Notation "s [ sigma_term ]" := (subst_elim sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__elim" := up_elim (only printing)  : subst_scope.

Notation "s [ sigma_term ]" := (subst_term sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__term" := up_term (only printing)  : subst_scope.

Notation "↑__term" := up_term_term (only printing)  : subst_scope.

Notation "s ⟨ xi_term ⟩" := (ren_term xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := tVar ( at level 1, only printing)  : subst_scope.

Notation "x '__term'" := (@ids _ _ VarInstance_term x)
( at level 5, format "x __term", only printing)  : subst_scope.

Notation "x '__term'" := (tVar x) ( at level 5, format "x __term")  :
subst_scope.

#[global]
Instance subst_elim_morphism `{Lang} :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_elim _ _)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_elim f_term s = subst_elim g_term t')
         (ext_elim f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_elim_morphism2 `{Lang} :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_elim _ _)).
Proof.
exact (fun f_term g_term Eq_term s => ext_elim f_term g_term Eq_term s).
Qed.

#[global]
Instance subst_term_morphism `{Lang} :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_term _ _)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_term f_term s = subst_term g_term t')
         (ext_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_term_morphism2 `{Lang} :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_term _ _)).
Proof.
exact (fun f_term g_term Eq_term s => ext_term f_term g_term Eq_term s).
Qed.

#[global]
Instance ren_term_morphism `{Lang} :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_term _ _)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_term f_term s = ren_term g_term t')
         (extRen_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_term_morphism2 `{Lang} :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_term _ _)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_term f_term g_term Eq_term s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                      Up_term_term, Up_term, up_term, Subst_term, Subst1,
                      subst1, Subst_elim, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_term, Var, ids,
                                            Ren_term, Ren1, ren1,
                                            Up_term_term, Up_term, up_term,
                                            Subst_term, Subst1, subst1,
                                            Subst_elim, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_elim_pointwise
                 | progress setoid_rewrite substSubst_elim
                 | progress setoid_rewrite substSubst_term_pointwise
                 | progress setoid_rewrite substSubst_term
                 | progress setoid_rewrite substRen_term_pointwise
                 | progress setoid_rewrite substRen_term
                 | progress setoid_rewrite renSubst_term_pointwise
                 | progress setoid_rewrite renSubst_term
                 | progress setoid_rewrite renRen'_term_pointwise
                 | progress setoid_rewrite renRen_term
                 | progress setoid_rewrite instId'_elim_pointwise
                 | progress setoid_rewrite instId'_elim
                 | progress setoid_rewrite varLRen'_term_pointwise
                 | progress setoid_rewrite varLRen'_term
                 | progress setoid_rewrite varL'_term_pointwise
                 | progress setoid_rewrite varL'_term
                 | progress setoid_rewrite rinstId'_term_pointwise
                 | progress setoid_rewrite rinstId'_term
                 | progress setoid_rewrite instId'_term_pointwise
                 | progress setoid_rewrite instId'_term
                 | progress unfold up_term_term, upRen_term_term, up_ren
                 | progress cbn[subst_elim subst_term ren_term]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1,
                  Subst_elim, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_term_pointwise;
                  try setoid_rewrite rinstInst'_term.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_term_pointwise;
                  try setoid_rewrite_left rinstInst'_term.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_elim: rewrite.

#[global] Hint Opaque subst_term: rewrite.

#[global] Hint Opaque ren_term: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

