From Stdlib Require Import Relations Arith Lia Bool List RelationClasses.
From Equations Require Import Equations.
From Interpolation Require Import Utils Syntax Languages Notations Reduction Typing Bidir.

(** ** Primitives for context splitting *)

Section Splitting.
  Context `{Lang}.

  Inductive side : Set := | source | target.

  Definition flip_side s := match s with | source => target | target => source end.

  Inductive split : Set := 
  | split_emp : split
  | split_s : split -> split
  | split_t : split -> split.

  Inductive splits : context -> context -> context -> split -> Prop :=
    | splits_emp : splits ε ε ε split_emp
    | splits_s {Γ Γs Γt A} {s} : splits Γ Γs Γt s -> splits (Γ,,A) (Γs,,A) Γt (split_s s)
    | splits_t {Γ Γs Γt A} {s} : splits Γ Γs Γt s -> splits (Γ,,A) Γs (Γt,,A) (split_t s).

  Fixpoint flip_split s : split :=
    match s with
    | split_emp => split_emp
    | split_s s => split_t (flip_split s)
    | split_t s => split_s (flip_split s)
    end.

  Fixpoint flip_splits {Γ Γs Γt} s : (splits Γ Γs Γt s) -> splits Γ Γt Γs (flip_split s).
  Proof.
    induction 1 ; cbn ; now constructor.
  Qed.

  Fixpoint sren_s (s : split) : ren :=
    match s with
    | split_emp => id
    | split_s s' => ⇑ (sren_s s')
    | split_t s' => (sren_s s') >> ↑
    end.

  Fixpoint sren_t (s : split) : ren :=
    match s with
    | split_emp => id
    | split_t s' => ⇑ (sren_t s')
    | split_s s' => (sren_t s') >> ↑
    end.

  Lemma flip_split_inv (s : split) : flip_split (flip_split s) = s.
  Proof.
    induction s ; cbn.
    1: easy.
    all: now rewrite IHs.
  Qed.

  Lemma sren_s_flip (s : split) :
    sren_s (flip_split s) = sren_t s.
  Proof.
    induction s ; cbn.
    1: easy.
    all: now rewrite IHs.
  Qed.

  Lemma sren_t_split (s : split) :
    sren_t (flip_split s) = sren_s s.
  Proof.
    rewrite <- (flip_split_inv s) at 2.
    rewrite sren_s_flip.
    reflexivity.
  Qed.

  Lemma sren_s_ty {Γ Γs Γt} s :
    splits Γ Γs Γt s ->
    Γ ⊢ (sren_s s) :: Γs.
  Proof.
    induction 1 ; cbn.
    all: eauto with typing.
  Qed.

  Lemma sren_t_ty {Γ Γs Γt} s :
    splits Γ Γs Γt s ->
    Γ ⊢ (sren_t s) :: Γt.
  Proof.
    intros.
    eapply ren_typing_ext.
    2: now eapply sren_s_ty, flip_splits.
    now rewrite sren_s_flip.
  Qed.

  Hint Resolve sren_s_ty sren_t_ty : typing.

  Fixpoint find_side (s : split) (n : nat) : (option side*nat) :=
    match s, n with
    | split_emp, _ => (None,0)
    | split_s _, 0 => (Some source,0)
    | split_t _, 0 => (Some target,0)
    | split_s s', S n' => match (find_side s' n') with
      | (None,_) => (None,0)
      | (Some source,k) => (Some source,S k)
      | (Some target,k) => (Some target,k)
      end
    | split_t s', S n' => match (find_side s' n') with
      | (None,_) => (None,0)
      | (Some source,k) => (Some source,k)
      | (Some target,k) => (Some target,S k)
      end
    end.

  Lemma find_flip (s : split) (n : nat) :
    find_side (flip_split s) n = prod_map (option_map flip_side) id (find_side s n).
  Proof.
    induction s in n |- * ; cbn ; try easy.
    all: destruct n ; cbn ; try easy.
    all: specialize (IHs n).
    all: destruct (find_side (flip_split s) n) as [[[]|]]; cbn in * ; subst.
    all: destruct (find_side _ _) as [[[]|]] ; cbn in * ; congruence.
  Qed.

  Lemma in_context_find_none {Γ Γs Γt} (n : nat) s T n' :
    splits Γ Γs Γt s ->
    in_context n Γ T ->
    find_side s n = (None,n') ->
    False.
  Proof.
    induction 1 in n, n' |- * ; [|destruct n | destruct n] ; cbn.
    - eauto with typing.
    - congruence.
    - intros Hin e.
      destruct find_side as [[[]|]] eqn:? ; cbn in * ; solve [congruence|eauto].
    - congruence.
    - intros Hin e.
      destruct find_side as [[[]|]] eqn:? ; cbn in * ; solve [congruence|eauto].
  Qed.

  Lemma find_side_some_l {Γ Γs Γt} (n : nat) s n':
    splits Γ Γs Γt s ->
    find_side s n = (Some source,n') ->
    exists T, in_context n' Γs T /\ n = sren_s s n'.
  Proof.
    intros Hs Hside.
    induction Hs in n, n', Hside |- * ; [|destruct n | destruct n] ; cbn in *.
    - congruence.
    - injection Hside ; subst.
      eexists ; split ; reflexivity.
    - destruct find_side as [[[]|]] eqn:e ; try solve [congruence].
      injection Hside ; subst.
      edestruct IHHs as (e'&[]) ; tea.
      subst.
      eexists ; split ; cbn ; tea ; reflexivity.
    - congruence.
    - destruct find_side as [[[]|]] eqn:e ; try solve [congruence].
      injection Hside ; subst.
      edestruct IHHs as (e'&[]) ; tea.
      subst.
      eexists ; split ; cbn ; tea ; reflexivity.
  Qed.

  Lemma find_side_some_r {Γ Γs Γt} (n : nat) s n' :
    splits Γ Γs Γt s ->
    find_side s n = (Some target,n') ->
    exists T, in_context n' Γt T /\ n = sren_t s n'.
  Proof.
    intros ? e.
    rewrite <- sren_s_flip.
    eapply find_side_some_l.
    1: now apply flip_splits.
    now rewrite find_flip, e.
  Qed.

End Splitting.

Section Interpolant.
  Context `{Lang}.

  #[derive(eliminator=no)]Equations infer (Γ : context) (t : term) : type :=
  infer Γ (tVar n)
    with (nth_error Γ n) => {
    | None => TUnit ;
    | Some T => T
    } ;
  infer _ (tConst c) := const_type c ;
  infer Γ (tApp f u)
    with (infer Γ f) => {
      | TFun _ B => B
      | _ => TUnit
    } ;
  infer Γ (tProj b t)
    with (infer Γ t) => {
      | TProd A B => if b then A else B
      | _ => TUnit
    } ; 
  infer _ _ => TUnit.

  Lemma infer_infer Γ A t :
  (Γ ⊢ t ▹ A) ->
  infer Γ t = A.
  Proof.
    intros Hty.
    pattern Γ, A, t.
    revert Hty.
    unshelve eapply bidir_ind.
    1: intros ; exact True.
    all: cbn ; try easy.
    all: intros ; simp infer ; cbn.
    - unfold in_context in *.
      destruct nth_error ; cbn ; congruence.
    - now rewrite H1 ; cbn.
    - now rewrite H1 ; cbn.
  Qed.

  Let defaulti : side*type*term*term := (source,TUnit,tStar,tStar).

  #[derive(eliminator=no)]Equations
  _interpolate_infer (interp : forall (s : split) (c : const_split)
      (Γ : context) (A : type) (t : term), type*term*term)
    (s : split) (c : const_split) (Γ : context) (t : term) : side*type*term*term :=

  _interpolate_infer _ s c Γ (tVar n)
    with (find_side s n) => {
      | (Some source,n') := (source,TUnit,tStar,(tVar (S n')))
      | (Some target,n') := (target, TUnit,tStar,(tVar (S n')))
      | (None, _) := defaulti
    } ;
  _interpolate_infer _ s csplit _ (tConst c)
    with (const_cover csplit c) => {
      | inl _ => (source,TUnit,tStar,(tConst c))
      | inr _ => (target,TUnit,tStar,(tConst c))
    } ;
  _interpolate_infer interp s c Γ (tApp f u)
    with (_interpolate_infer interp s c Γ f), (infer Γ f) => {
    | (source,Mf,lf,rf), (TFun A _) :=
        let '(Mu,lu,ru) := (interp (flip_split s) (flip_csplit c) Γ A u) in
        (source,(TProd Mf Mu),(tPair lf lu),(tApp (rf[tip tFst]) (ru[(tip tSnd)])))
    | (target,Mf,lf,rf), (TFun A _) :=
        let '(Mu,lu,ru) := (interp s c Γ A u)
        in (target,(TProd Mf Mu),(tPair lf lu),(tApp (rf[tip tFst]) (ru[(tip tSnd)])))
    | _, _ := defaulti
    } ;

  _interpolate_infer interp s c Γ (tProj b t) :=
    let '(o,M,l,r) := (_interpolate_infer interp s c Γ t) in
    (o,M,l,(tProj b r)) ;

  _interpolate_infer _ _ _ _ _ := defaulti.

  Let default := (TUnit,tStar,tStar).

  #[derive(eliminator=no)]Equations
  interpolate (s : split) (c : const_split) (Γ : context) (A : type) (t : term)
    : type*term*term :=
  
  interpolate s c Γ _ tStar :=
    (TUnit,tStar,tStar) ;

  interpolate s c Γ (TFun A B) (tLam t) =>
    let '(M,l,r) := (interpolate (split_t s) c (Γ,,A) B t)
    in (M,l,tLam (r⟨swap_var⟩)) ;
  interpolate _ _ _ _ (tLam _) =>
    default ;

  interpolate s c Γ (TProd A B) (tPair t t') :=
    let '(M,l,r) := (interpolate s c Γ A t)
    in let '(M',l',r') := (interpolate s c Γ B t')
    in ((TProd M M'),(tPair l l'),(tPair (r[tip tFst]) (r'[tip tSnd]))) ;
  interpolate _ _ _ _ (tPair _ _) =>
    default ;

  interpolate s c Γ (TSum A B) (tIn b t) :=
    let '(M,l,r) := (interpolate s c Γ (if b then A else B) t)
    in (M, l, (tIn b r)) ;
  interpolate _ _ _ _ (tIn b t) :=
    default ;

  interpolate s c Γ _ (tAbort t)
    with (_interpolate_infer interpolate s c Γ t) => {
    | (source,M,l,r) :=
        ((TFun M TEmp),(tLam r),(tAbort (tApp (tVar 0) l⟨↑⟩)))
    | (target,M,l,r) := (M, l, (tAbort r))
    } ;

  interpolate s c Γ C (tIf t bl br)
    with (_interpolate_infer interpolate s c Γ t), (infer Γ t) => {

    | (source,M,l,r), TSum A B :=
      let '(Ml,ll,rl) := interpolate (split_s s) c (Γ,,A) C bl
      in let '(Mr,lr,rr) := interpolate (split_s s) c (Γ,,B) C br
      in ((TFun M (TSum Ml Mr)),
          (tLam (tIf r (tLeft ll⟨↑⟩⟨swap_var⟩) (tRight lr⟨↑⟩⟨swap_var⟩))),
          (tIf (tApp (tVar 0) l⟨↑⟩) rl⟨↑⟩⟨swap_var⟩ rr⟨↑⟩⟨swap_var⟩)) ;

    | (target,M,l,r), TSum A B :=
      let '(Ml,ll,rl) := interpolate (split_t s) c (Γ,,A) C bl
      in let '(Mr,lr,rr) := interpolate (split_t s) c (Γ,,B) C br
      in ((TProd M (TProd Ml Mr)),
          (tPair l (tPair ll lr)),
          ((tIf r[tip tFst]
            rl[(tip (fun x => (tFst (tSnd x))))]⟨swap_var⟩
            rr[(tip (fun x => tSnd (tSnd x)))]⟨swap_var⟩)))

    | _, _ => default ;
    } ;

  interpolate s c Γ A i
    with (_interpolate_infer interpolate s c Γ i) => {
    | (source,M,l,r) :=
        ((TFun M (infer Γ i)), (tLam r), (tApp (tVar 0) l⟨↑⟩))
    | (target,M,l,r) := (M, l, r)
    }.

End Interpolant.

Notation interpolate_infer := (_interpolate_infer interpolate).

Lemma interpolate_infer_eq `{Lang} Γ A i s c :
  (Γ ⊢ i ▹ A) ->
  interpolate s c Γ A i =
    (match (interpolate_infer s c Γ i) with 
      | (source,M,l,r) =>
        ((TFun M (infer Γ i)), (tLam r), (tApp (tVar 0) l⟨↑⟩))
      | (target,M,l,r) => (M, l, r)
    end).
Proof.
  intros Hty.
  inversion Hty ; subst ; cbn.
  - destruct _interpolate_infer_clause_1 as ((([]&?)&?)&?) ; cbn ; reflexivity.
  - destruct _interpolate_infer_clause_2 as ((([]&?)&?)&?) ; cbn ; reflexivity.
  - destruct _interpolate_infer_clause_3 as ((([]&?)&?)&?) ; cbn ; reflexivity.
  - destruct interpolate_infer as ((([]&?)&?)&?) ; cbn ; reflexivity.
Qed.
  
Section Interpolation.
  Context `{Lang}.

    Let Pcheck_lang_ty Γ T t := forall Γs Γt (s : split) (c : const_split),
    splits Γ Γs Γt s ->
    let '(M,l,r) := interpolate s c Γ T t in
    forall p,
    atoms_ty p M ⊆ 
      (atoms_ctx p Γs ∪ atoms_const p c.(pconst_l)) ∩
        (atoms_ctx (negp p) Γt ∪ (atoms_const (negp p) c.(pconst_r)) ∪ atoms_ty p T).

  Let Pinf_lang_ty Γ (T : type) t := forall Γs Γt (s : split) (c : const_split),
    splits Γ Γs Γt s ->
    let '(si,M,l,r) := interpolate_infer s c Γ t in
    match si with
    | target => 
        (forall p, atoms_ty p T ⊆ atoms_ctx p Γt ∪ atoms_const p c.(pconst_r))
        /\ (forall p, atoms_ty p M ⊆ (atoms_ctx p Γs ∪ atoms_const p c.(pconst_l))
                                      ∩ (atoms_ctx (negp p) Γt ∪ atoms_const (negp p) c.(pconst_r)))
    | source =>
        (forall p, atoms_ty p T ⊆ atoms_ctx p Γs ∪ atoms_const p c.(pconst_l))
        /\ (forall p, atoms_ty p M ⊆ (atoms_ctx (negp p) Γs ∪ atoms_const (negp p) c.(pconst_l))
                                      ∩ (atoms_ctx p Γt ∪ atoms_const p c.(pconst_r)))
    end.

  Lemma polarity_reverse (P : polarity -> polarity -> Prop) :
    (forall p, P (negp p) p) ->
    (forall p, P p (negp p)).
  Proof.
    intros HP.
    destruct p ; cbn.
    - apply (HP neg).
    - apply (HP pos).
  Qed.

  Theorem interpolation_lang_ty : bidir_concl Pcheck_lang_ty Pinf_lang_ty.
  Proof.
    subst Pcheck_lang_ty Pinf_lang_ty ; clear.
    apply bidir_ind ; cbn in *.

    - (* case tStar *)
      intros.
      set_solver.

    - (* case tLam *)
      intros * _ IH * Hs ; cbn.
      specialize (IH _ _ _ c (splits_t Hs)).
      destruct interpolate as ((?&?)&?) ; cbn.
      set_solver.
    
    - (* case tPair *)
      intros * _ IHA _ IHB * Hs.
      specialize (IHA _ _ _ c Hs).
      specialize (IHB _ _ _ c Hs).
      destruct interpolate as ((?&?)&?) ; cbn.
      destruct interpolate as ((?&?)&?) ; cbn.
      all: set_solver.
    
    - (* case tLeft *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      (destruct interpolate as ((?&?)&?) ; cbn).
      set_solver.
    
    - (* case tRight *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      (destruct interpolate as ((?&?)&?) ; cbn).
      set_solver.
    
    - (* case tAbort *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      + intros.
        pattern p, (negp p).
        apply polarity_reverse.
        set_solver.
      + set_solver. 

    - (* case tIf *)
      intros * ? IHs _ IHl _ IHr * Hs.
      specialize (IHs _ _ _ c Hs) ; cbn in *.
      destruct interpolate_infer as ((([]&Ms)&rs)&ls) ; cbn in *.
      all: destruct IHs as [IHT IHs].
      all: red ; erewrite infer_infer ; tea ; cbn.
      + specialize (IHl _ _ _ c (splits_s Hs)) ; cbn in *.
        destruct interpolate as ((Ml&ll)&rl) ; cbn in *.
        specialize (IHr _ _ _ c (splits_s Hs)) ; cbn in *.
        destruct interpolate as ((Mr&lr)&rr) ; cbn in *.
        intros.
        repeat apply union_least.
        * clear -IHs.
          pattern p, (negp p).
          apply polarity_reverse.
          intros.
          set_solver.
        * clear -IHT IHl.
          set_solver.
        * clear -IHT IHr.
          set_solver.

      + specialize (IHl _ _ _ c (splits_t Hs)) ; cbn in *.
        destruct interpolate as ((Ml&ll)&rl) ; cbn in *.
        specialize (IHr _ _ _ c (splits_t Hs)) ; cbn in *.
        destruct interpolate as ((Mr&lr)&rr) ; cbn in *.
        intros.
        repeat apply union_least.
        * clear -IHs.
          set_solver.
        * clear -IHT IHl.
          set_solver.
        * clear -IHT IHr.
          set_solver.

    - (* case demote *)
      intros * ? IH -> * Hs.
      specialize (IH _ _ _ c Hs).
      rewrite interpolate_infer_eq ; tea.
      erewrite infer_infer ; tea ; cbn.
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      all: destruct IH.
      + intros.
        apply union_least.
        * pattern p, (negp p).
          apply polarity_reverse.
          set_solver.
        * set_solver.
      + set_solver.

    - (* case tVar *)
      intros * Hin * Hs.
      destruct (find_side s n) as ([[]|]&?) eqn:e.
      + eapply find_side_some_l in e as (A&[? ->]) ; tea ; cbn.
        eapply in_context_inj in Hin.
        2:now eapply sren_s_ty.
        subst.
        split.
        1: intros ; rewrite atoms_in ; tea ; set_solver.
        set_solver.
      + eapply find_side_some_r in e as (A&[? ->]) ; tea ; cbn.
        eapply in_context_inj in Hin.
        2:now eapply sren_t_ty.
        subst.
        split.
        1: intros ; rewrite atoms_in ; tea ; set_solver.
        set_solver.
      + exfalso ; now eauto using in_context_find_none. 

    - (* case tConst *)
      intros * Hs.
      destruct const_cover ; cbn.
      all: set_solver.

    - (* case tApp *)
      intros * ? IHf _ IHu * Hs.
      specialize (IHf _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      all: red ; erewrite infer_infer ; tea ; cbn.
      1: specialize (IHu _ _ _ (flip_csplit c) (flip_splits _ Hs)) ; cbn in *.
      2: specialize (IHu _ _ _ c Hs) ; cbn in *.
      all: destruct interpolate as ((?&?)&?) ; cbn.
      all: split ; [set_solver|].
      all: intros p.
      all: destruct IHf as (IHty&?).
      all: specialize (IHty (negp p)).
      all: rewrite negp_inv in IHty.
      all: set_solver.

    - (* case tProj *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      all: destruct b.
      all: set_solver.
  Qed.

    Let Pcheck_ty Γ T t := forall Γs Γt (s : split) (c : const_split),
    splits Γ Γs Γt s ->
    let '(M,l,r) := interpolate s c Γ T t in
    (Γs ⊢ l :: M) /\ (Γt ,, M ⊢ r :: T).

  Let Pinf_ty Γ (T : type) t := forall Γs Γt (s : split) (c : const_split),
    splits Γ Γs Γt s ->
    let '(si,M,l,r) := interpolate_infer s c Γ t in
    match si with
    | target => (Γs ⊢ l :: M) /\ (Γt ,, M ⊢ r :: T)
    | source => (Γt ⊢ l :: M) /\ (Γs ,, M ⊢ r :: T)
    end.

  Theorem interpolation_ty : bidir_concl Pcheck_ty Pinf_ty.
  Proof.
    subst Pcheck_ty Pinf_ty ; clear.
    apply bidir_ind ; cbn in *.

    - (* case tStar *)
      intros.
      eauto with typing.

    - (* case tLam *)
      intros * _ IH * Hs ; cbn.
      specialize (IH _ _ _ c (splits_t Hs)).
      destruct interpolate as ((?&?)&?) ; cbn.
      eauto with typing.
    
    - (* case tPair *)
      intros * _ IHA _ IHB * Hs.
      specialize (IHA _ _ _ c Hs).
      specialize (IHB _ _ _ c Hs).
      destruct interpolate as ((?&?)&?) ; cbn.
      destruct interpolate as ((?&?)&?) ; cbn.
      eauto 20 with typing.
    
    - (* case tLeft *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      (destruct interpolate as ((?&?)&?) ; cbn).
      eauto 20 with typing.
    
    - (* case tRight *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      (destruct interpolate as ((?&?)&?) ; cbn).
      eauto 20 with typing.
    
    - (* case tAbort *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      destruct interpolate_infer as ((([]&M)&l)&r) ; cbn in *.
      all: eauto 10 with typing.

    - (* case tIf *)
      intros * ? IHs _ IHl _ IHr * Hs.
      specialize (IHs _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&l)&r) ; cbn in *.
      1: specialize (IHl _ _ _ c (splits_s Hs)) ; cbn in *.
      2: specialize (IHl _ _ _ c (splits_t Hs)) ; cbn in *.
      1: specialize (IHr _ _ _ c (splits_s Hs)) ; cbn in *.
      2: specialize (IHr _ _ _ c (splits_t Hs)) ; cbn in *.
      all: red ; erewrite infer_infer ; tea ; cbn.
      all: do 2 (destruct interpolate as ((?&?)&?) ; cbn in *).
      + split ; eauto 20 with typing.
      + split.
        all: eauto 30 with typing.

    - (* case demote *)
      intros * ? IH -> * Hs.
      specialize (IH _ _ _ c Hs).
      rewrite interpolate_infer_eq ; tea.
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      1: erewrite infer_infer ; tea.
      all: split ; eauto 10 with typing.

    - (* case tVar *)
      intros * Hin * Hs.
      destruct (find_side s n) as ([[]|]&?) eqn:e.
      + eapply find_side_some_l in e as (A&[? ->]) ; tea ; cbn.
        eapply in_context_inj in Hin.
        2:now eapply sren_s_ty.
        subst.
        eauto with typing.
      + eapply find_side_some_r in e as (A&[? ->]) ; tea ; cbn.
        eapply in_context_inj in Hin.
        2:now eapply sren_t_ty.
        subst.
        eauto with typing.
      + exfalso ; now eauto using in_context_find_none.

    - (* case tConst *)
      intros * Hs.
      destruct const_cover ; cbn.
      all: eauto with typing.

    - (* case tApp *)
      intros * ? IHf _ IHu * Hs.
      specialize (IHf _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      all: red ; erewrite infer_infer ; tea ; cbn.
      + specialize (IHu _ _ _ (flip_csplit c) (flip_splits _ Hs)) ; cbn in *.
        destruct interpolate as ((?&?)&?) ; cbn.
        eauto 20 with typing.

      + specialize (IHu _ _ _ c Hs) ; cbn in *.
        destruct interpolate as ((?&?)&?) ; cbn.
        eauto 20 with typing.

    - (* case tProj *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      all: destruct b ; eauto 20 with typing.
  Qed.

  Let Pcheck_lang_tm Γ T t := forall Γs Γt (s : split) (c : const_split),
    splits Γ Γs Γt s ->
    let '(M,l,r) := interpolate s c Γ T t in
    (atoms_tm l ⊆ c.(pconst_l)) /\ (atoms_tm r ⊆ c.(pconst_r)).

  Let Pinf_lang_tm Γ (T : type) t := forall Γs Γt (s : split) (c : const_split),
    splits Γ Γs Γt s ->
    let '(si,M,l,r) := interpolate_infer s c Γ t in
    match si with
    | source => (atoms_tm l ⊆ (flip_csplit c).(pconst_l)) /\ (atoms_tm r ⊆ (flip_csplit c).(pconst_r)) 
    | target => (atoms_tm l ⊆ c.(pconst_l)) /\ (atoms_tm r ⊆ c.(pconst_r))
    end.

  Theorem interpolation_lang_tm : bidir_concl Pcheck_lang_tm Pinf_lang_tm.
  Proof.
    subst Pcheck_lang_tm Pinf_lang_tm ; clear.
    apply bidir_ind ; cbn in *.

    - (* case tStar *)
      intros.
      set_solver.

    - (* case tLam *)
      intros * _ IH * Hs ; cbn.
      specialize (IH _ _ _ c (splits_t Hs)).
      destruct interpolate as ((?&?)&?) ; cbn.
      rewrite atoms_ren.
      set_solver.
    
    - (* case tPair *)
      intros * _ IHA _ IHB * Hs.
      specialize (IHA _ _ _ c Hs).
      specialize (IHB _ _ _ c Hs).
      destruct interpolate as ((?&?)&?) ; cbn.
      destruct interpolate as ((?&?)&?) ; cbn.
      rewrite !atoms_subst_tip_eq ; cbn.
      all: set_solver.
    
    - (* case tLeft *)
      intros * ? * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      (destruct interpolate as ((?&?)&?) ; cbn).
      set_solver.
    
    - (* case tRight *)
      intros * ? * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      (destruct interpolate as ((?&?)&?) ; cbn).
      set_solver.
    
    - (* case tAbort *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      1: rewrite atoms_ren.
      all: set_solver.

    - (* case tIf *)
      intros * ? IHs _ IHl _ IHr * Hs.
      specialize (IHs _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      1: specialize (IHl _ _ _ c (splits_s Hs)) ; cbn in *.
      2: specialize (IHl _ _ _ c (splits_t Hs)) ; cbn in *.
      1: specialize (IHr _ _ _ c (splits_s Hs)) ; cbn in *.
      2: specialize (IHr _ _ _ c (splits_t Hs)) ; cbn in *.
      all: red ; erewrite infer_infer ; tea ; cbn.
      all: do 2 (destruct interpolate as ((?&?)&?) ; cbn in *).
      all: rewrite ?atoms_ren, ?atoms_subst_tip_eq ; cbn.
      all: set_solver.

    - (* case demote *)
      intros * ? IH -> * Hs.
      specialize (IH _ _ _ c Hs).
      rewrite interpolate_infer_eq ; tea.
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      all: rewrite ?atoms_ren.
      all: set_solver.

    - (* case tVar *)
      intros * Hin * Hs.
      destruct (find_side s n) as ([[]|]&?) eqn:e.
      3: exfalso ; now eauto using in_context_find_none.
      + eapply find_side_some_l in e as (A&[? ->]) ; tea ; cbn.
        set_solver.
      + eapply find_side_some_r in e as (A&[? ->]) ; tea ; cbn.
        set_solver.

    - (* case tConst *)
      intros * Hs.
      destruct const_cover ; cbn.
      all: set_solver.

    - (* case tApp *)
      intros * ? IHf _ IHu * Hs.
      specialize (IHf _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      all: red ; erewrite infer_infer ; tea ; cbn.
      + specialize (IHu _ _ _ (flip_csplit c) (flip_splits _ Hs)) ; cbn in *.
        destruct interpolate as ((?&?)&?) ; cbn.
        rewrite !atoms_subst_tip_eq ; cbn in *.
        all: set_solver.

      + specialize (IHu _ _ _ c Hs) ; cbn in *.
        destruct interpolate as ((?&?)&?) ; cbn.
        rewrite !atoms_subst_tip_eq ; cbn in *.
        all: set_solver.

    - (* case tProj *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      all: set_solver.
  Qed.


  Let Pcheck_red Γ T t := forall Γs Γt (s : split) (c : const_split),
    splits Γ Γs Γt s ->
    let '(M,l,r) := interpolate s c Γ T t in
    r⟨⇑ (sren_t s)⟩[l⟨sren_s s⟩..] ⤳* t.

  Let Pinf_red Γ (T : type) t := forall Γs Γt (s : split) (c : const_split),
    splits Γ Γs Γt s ->
    let '(si,M,l,r) := interpolate_infer s c Γ t in
    match si with
    | source => r⟨⇑ (sren_s s)⟩[l⟨sren_t s⟩..] ⤳* t
    | target => r⟨⇑ (sren_t s)⟩[l⟨sren_s s⟩..] ⤳* t
    end.

  Theorem interpolation_red : bidir_concl Pcheck_red Pinf_red.
  Proof.
    subst Pcheck_red Pinf_red ; clear.
    apply bidir_ind ; cbn in *.

    - (* case tStar *)
      intros.
      reflexivity.

    - (* case tLam *)
      intros * _ IH * Hs ; cbn.
      specialize (IH _ _ _ c (splits_t Hs)).
      destruct interpolate as ((?&?)&?) ; cbn.
      
      refold.
      now rewrite swap_up2, swap_up1, renRen_term, IH.
    
    - (* case tPair *)
      intros * _ IHA _ IHB * Hs.
      specialize (IHA _ _ _ c Hs).
      specialize (IHB _ _ _ c Hs).
      destruct interpolate as ((?&?)&?) ; cbn.
      destruct interpolate as ((?&?)&?) ; cbn.

      now rewrite !tip_up_ren, !tip_subst, ST_Fst, ST_Snd, IHA, IHB.
    
    - (* case tLeft *)
      intros * ? * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      (destruct interpolate as ((?&?)&?) ; cbn).
      now rewrite IH.
    
    - (* case tRight *)
      intros * ? * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      (destruct interpolate as ((?&?)&?) ; cbn).
      now rewrite IH.
    
    - (* case tAbort *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      destruct interpolate_infer as ((([]&M)&l)&r) ; cbn in *.
      
      2: now rewrite IH.
      refold.
      rewrite ST_Beta_Fun.
      apply R_Abort_cong.
      etransitivity ; [|eassumption].
      apply ereflexivity.
      substify.
      now asimpl.

    - (* case tIf *)
      intros * ? IHs _ IHl _ IHr * Hs.
      specialize (IHs _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&l)&r) ; cbn in *.
      1: specialize (IHl _ _ _ c (splits_s Hs)) ; cbn in *.
      2: specialize (IHl _ _ _ c (splits_t Hs)) ; cbn in *.
      1: specialize (IHr _ _ _ c (splits_s Hs)) ; cbn in *.
      2: specialize (IHr _ _ _ c (splits_t Hs)) ; cbn in *.
      all: red ; erewrite infer_infer ; tea ; cbn.
      all: do 2 (destruct interpolate as ((?&?)&?) ; cbn in *).
      
      all: refold.
      + cbn ; refold.
        rewrite !swap_up2, !swap_up1, !ST_Beta_Fun.
        cbn ; refold.
        rewrite ST_If_If, !ST_Left, !ST_Right, !swap_up2, !swap_up1 ; refold.
        apply R_If_cong.
        all: etransitivity ; [|eassumption].
        all: apply ereflexivity.
        -- now substify ; asimpl.
        -- cbn.
           rewrite !renRen_term ; refold.
           apply subst_term_morphism.
           2: now substify ; asimpl.
           intros [|] ; cbn ; [|easy].
           now substify ; asimpl.
        -- cbn.
           rewrite !renRen_term ; refold.
           apply subst_term_morphism.
           2: now substify ; asimpl.
           intros [|] ; cbn ; [|easy].
           now substify ; asimpl.

      + rewrite !swap_up2, !swap_up1, !tip_up_ren, !tip_subst ; cbn ; try easy.
        now rewrite !ST_Snd, !ST_Fst, renRen_term, renRen_term, IHs, IHl, IHr. 

    - (* case demote *)
      intros * ? IH -> * Hs.
      specialize (IH _ _ _ c Hs).
      rewrite interpolate_infer_eq ; tea.
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.

      all: refold.
      2: easy.
      cbn.
      rewrite ST_Beta_Fun, <- IH.
      apply ereflexivity.
      substify.
      now asimpl.

    - (* case tVar *)
      intros * Hin * Hs.
      destruct (find_side s n) as ([[]|]&?) eqn:e.
      + eapply find_side_some_l in e as (A&[? ->]) ; tea ; cbn.
        reflexivity.
      + eapply find_side_some_r in e as (A&[? ->]) ; tea ; cbn.
        reflexivity.
      + exfalso ; now eauto using in_context_find_none.

    - (* case tConst *)
      intros * Hs.
      destruct const_cover ; cbn.
      all: reflexivity.

    - (* case tApp *)
      intros * ? IHf _ IHu * Hs.
      specialize (IHf _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      all: red ; erewrite infer_infer ; tea ; cbn.
      
      + specialize (IHu _ _ _ (flip_csplit c) (flip_splits _ Hs)) ; cbn in *.
        destruct interpolate as ((?&?)&?) ; cbn.
        rewrite sren_s_flip, sren_t_split in IHu.
        now rewrite !tip_up_ren, !tip_subst, ST_Fst, ST_Snd, IHf, IHu.

      + specialize (IHu _ _ _ c Hs) ; cbn in *.
        destruct interpolate as ((?&?)&?) ; cbn.
        now rewrite !tip_up_ren, !tip_subst, ST_Fst, ST_Snd, IHf, IHu.

    - (* case tProj *)
      intros * _ IH * Hs.
      specialize (IH _ _ _ c Hs).
      destruct interpolate_infer as ((([]&?)&?)&?) ; cbn in *.
      all: now rewrite IH.

  Qed.

End Interpolation.