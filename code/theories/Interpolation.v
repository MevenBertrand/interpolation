From Stdlib Require Import Relations Arith Lia Bool List RelationClasses.
From Interpolation Require Import Utils Syntax Languages Notations Reduction Typing Bidir.

(** ** Primitives for context splitting *)

Section Splitting.
  Context `{Lang}.

  Inductive side : Set := | source | target.

  Definition flip_side s := match s with | source => target | target => source end.

  Inductive split : context -> context -> context -> Set :=
    | split_emp : split ε ε ε
    | split_s {Γ Γs Γt A} : split Γ Γs Γt -> split (Γ,,A) (Γs,,A) Γt
    | split_t {Γ Γs Γt A} : split Γ Γs Γt -> split (Γ,,A) Γs (Γt,,A).

  Fixpoint flip_split {Γ Γs Γt} (s : split Γ Γs Γt) : split Γ Γt Γs :=
    match s with
    | split_emp => split_emp
    | split_s s => split_t (flip_split s)
    | split_t s => split_s (flip_split s)
    end.

  Fixpoint sren_s {Γ Γs Γt} (s : split Γ Γs Γt) : ren :=
    match s with
    | split_emp => id
    | split_s s' => ⇑ (sren_s s')
    | split_t s' => (sren_s s') >> ↑
    end.

  Fixpoint sren_t {Γ Γs Γt} (s : split Γ Γs Γt) : ren :=
    match s with
    | split_emp => id
    | split_t s' => ⇑ (sren_t s')
    | split_s s' => (sren_t s') >> ↑
    end.

  Lemma flip_split_inv {Γ Γs Γt} (s : split Γ Γs Γt) :
    flip_split (flip_split s) = s.
  Proof.
    induction s ; cbn.
    1: easy.
    all: now rewrite IHs.
  Qed.

  Lemma sren_s_flip {Γ Γs Γt} (s : split Γ Γs Γt) :
    sren_s (flip_split s) = sren_t s.
  Proof.
    induction s ; cbn.
    1: easy.
    all: now rewrite IHs.
  Qed.

  Lemma sren_t_split {Γ Γs Γt} (s : split Γ Γs Γt) :
    sren_t (flip_split s) = sren_s s.
  Proof.
    rewrite <- (flip_split_inv s) at 2.
    rewrite sren_s_flip.
    reflexivity.
  Qed.

  Lemma sren_s_ty {Γ Γs Γt} (s : split Γ Γs Γt) :
    Γ ⊢ (sren_s s) :: Γs.
  Proof.
    induction s ; cbn.
    all: eauto with typing.
  Qed.

  Lemma sren_t_ty {Γ Γs Γt} (s : split Γ Γs Γt) :
    Γ ⊢ (sren_t s) :: Γt.
  Proof.
    eapply ren_typing_ext.
    2: eapply sren_s_ty.
    rewrite sren_s_flip.
    reflexivity.
  Qed.

  Hint Resolve sren_s_ty sren_t_ty : typing.

  Fixpoint find_side {Γ Γs Γt} (s : split Γ Γs Γt) (n : nat) : option side :=
    match s, n with
    | split_emp, _ => None
    | split_s _, 0 => Some source
    | split_t _, 0 => Some target
    | split_s s', S n' | split_t s', S n' => find_side s' n'
    end.

  Lemma find_flip {Γ Γs Γt} (s : split Γ Γs Γt) (n : nat) :
    find_side (flip_split s) n = option_map flip_side (find_side s n).
  Proof.
    induction s in n |- * ; cbn ; try easy.
    all: now destruct n ; cbn.
  Qed.

  Lemma in_context_find_none {Γ Γs Γt} (n : nat) (s : split Γ Γs Γt) T :
    in_context n Γ T ->
    find_side s n = None ->
    False.
  Proof.
    induction s in n |- * ; [|destruct n | destruct n] ; cbn.
    - eauto with typing.
    - congruence.
    - intros Hin ?%IHs.
      1: easy.
      exact Hin.
    - congruence.
    - intros Hin ?%IHs.
      1: easy.
      exact Hin.
  Qed.

  Lemma find_side_some_l {Γ Γs Γt} (n : nat) (s : split Γ Γs Γt) :
    find_side s n = Some source ->
    {n' & {T & in_context n' Γs T /\ n = sren_s s n'}}.
  Proof.
    intros Hside.
    induction s in n, Hside |- * ; [|destruct n | destruct n] ; cbn in *.
    - congruence.
    - eexists 0, _ ; split ; reflexivity.
    - edestruct IHs as (n'&e&[]) ; tea.
      subst.
      eexists (S n'),_ ; split ; cbn ; tea ; reflexivity.
    - congruence.
    - edestruct IHs as (n'&e&[]) ; tea.
      subst.
      eexists n',_ ; split ; cbn ; tea ; reflexivity.
  Qed.

  Lemma find_side_some_r {Γ Γs Γt} (n : nat) (s : split Γ Γs Γt) :
    find_side s n = Some target ->
    {n' & {T & in_context n' Γt T /\ n = sren_t s n'}}.
  Proof.
    intros e.
    rewrite <- sren_s_flip.
    apply find_side_some_l.
    rewrite find_flip, e.
    reflexivity.
  Qed.

End Splitting.

Section Interpolation.
  Context `{Lang}.

  (** With the splitting of the context given by Γs and Γt and the type A,
    I is a valid interpolating type. *)
  Definition interpolate_ty Γs Γt A M (c : const_split): Prop :=
    forall p, atoms_ty p M ⊆ 
      (atoms_ctx p Γs ∪ atoms_const p c.(pconst_l)) ∩
      (atoms_ctx (negp p) Γt ∪ (atoms_const (negp p) c.(pconst_r)) ∪ atoms_ty p A).

  Definition interpolate_tm {Γ Γs Γt} (s : split Γ Γs Γt) (c : const_split) M A t l r :=
    (Γs ⊢ l :: M) /\ (atoms_tm l ⊆ c.(pconst_l)) /\
    (Γt ,, M ⊢ r :: A) /\ (atoms_tm r ⊆ c.(pconst_r)) /\
    r⟨⇑ (sren_t s)⟩[l⟨sren_s s⟩..] ⤳* t.

  Let Pcheck Γ T t := forall Γs Γt (s : split Γ Γs Γt) (c : const_split),
    exists M l r,
      interpolate_ty Γs Γt T M c /\ interpolate_tm s c M T t l r.

  Let Pinf Γ T t := forall Γs Γt (s : split Γ Γs Γt) (c : const_split),
    (
      (forall p, atoms_ty p T ⊆ atoms_ctx p Γt ∪ atoms_const p c.(pconst_r)) /\
      (exists M l r, 
        (forall p, atoms_ty p M ⊆ (atoms_ctx p Γs ∪ atoms_const p c.(pconst_l))
                                  ∩ (atoms_ctx (negp p) Γt ∪ atoms_const (negp p) c.(pconst_r)))
        /\ interpolate_tm s c M T t l r)
    ) \/ (
      (forall p, atoms_ty p T ⊆ atoms_ctx p Γs ∪ atoms_const p c.(pconst_l)) /\
      (exists M l r, 
        (forall p, atoms_ty p M ⊆ (atoms_ctx (negp p) Γs ∪ atoms_const (negp p) c.(pconst_l))
                                  ∩ (atoms_ctx p Γt ∪ atoms_const p c.(pconst_r)))
        /\ interpolate_tm (flip_split s) (flip_csplit c) M T t l r)
    ).

  Ltac pre_crush_incl :=
    unfold interpolate_ty in * ;
    intros ;
    repeat match goal with
      | b : polarity |- _ => destruct b
      | H : forall b : polarity, _ |- _ => pose proof (H pos) ; pose proof (H neg) ; cbn in * ; clear H
    end.

  Ltac crush_incl := pre_crush_incl ; set_solver.

  Theorem interpolation_ind : bidir_concl Pcheck Pinf.
  Proof.
    apply bidir_ind ; subst Pcheck Pinf.

    - (* case tStar *)
      intros Γ Γs Γt s.
      exists TUnit, tStar, tStar.
      split.
      1: solve [crush_incl].
      red.
      prod_splitter.
      1,3: now auto with typing.
      1,2: solve [crush_incl].
      reflexivity.

    - (* case tLam *)
      intros Γ A B t _ IH Γs Γt s c.
      destruct (IH Γs (Γt,,A) (split_t s) c) as (M&l&r&HM&Ht).
      exists M, l, (tLam (r⟨swap_var⟩)).
      split.
      1: clear -HM ; solve [crush_incl].
      
      unfold interpolate_tm in * ; cbn in *.
      destruct Ht as (?&?&?&?&e).
      prod_splitter.
      1,3: now eauto with typing.
      1: solve [crush_incl].
      1: rewrite atoms_ren ; solve [crush_incl].

      refold.
      now rewrite swap_up2, swap_up1, renRen_term, e.
    
    - (* case tPair *)
      intros Γ A B t t' _ IHA _ IHB Γs Γt s c.
      destruct (IHA Γs Γt s c) as (M & l & r & HM & (?&?&?&?&et)).
      destruct (IHB Γs Γt s c) as (M' & l' & r' & HM' & (?&?&?&?&et')).
      exists (TProd M M'), (tPair l l'),
        (tPair (r[tip tFst]) (r'[tip tSnd])).
      split.
      1: clear -HM HM' ; solve [crush_incl].
      
      unfold interpolate_tm in * ; cbn in *.
      prod_splitter.
      1,3: now eauto 20 with typing.
      1: solve [crush_incl].
      + erewrite union_mono.
        2-3: rewrite atoms_tm_subst, atoms_subst_tip ; cbn ; reflexivity.
        set_solver.
      
      + now rewrite !tip_up_ren, !tip_subst, ST_Fst, ST_Snd, et, et'.
    
      - (* case tLeft *)
      intros * _ IH ?? s c.
      destruct (IH _ _ s c) as (M & l & r & HM & Ht).
      exists M, l, (tLeft r).
      split.
      1: clear -HM ; solve [crush_incl].
      
      unfold interpolate_tm in * ; cbn in *.
      destruct Ht as (?&?&?&?&e).
      prod_splitter.
      1,3: eauto with typing.
      1-2: solve [crush_incl].
      now rewrite e.
    
    - (* case tRight *)
      intros * _ IH ?? s c.
      destruct (IH _ _ s c) as (M & l & r & HM & Ht).
      exists M, l, (tRight r).
      split.
      1: clear -HM ; solve [crush_incl].

      unfold interpolate_tm in * ; cbn in *.
      destruct Ht as (?&?&?&?&e).
      prod_splitter.
      1,3: eauto with typing.
      1-2: solve [crush_incl].
      now rewrite e.
    
      - (* case tAbort *)
      intros * _ IH ?? s c.
      destruct (IH _ _ s c) as [[_ (M&l&r&[HM (?&?&?&?&e)])]|[_ (M&l&r&[HM (?&?&?&?&e)])]] ; tea.

      + exists M, l, (tAbort r).
        split.
        1: clear -HM ; solve [crush_incl].

        unfold interpolate_tm in * ; cbn in *.
        prod_splitter.
        1,3: eauto with typing.
        1-2: solve [crush_incl].
        now rewrite e.

      + exists (TFun M TEmp), (tLam r), (tAbort (tApp (tVar 0) l⟨↑⟩)).
        split.
        1: clear -HM ; solve [crush_incl].

        unfold interpolate_tm in *.
        prod_splitter.
        1,3: eauto 20 with typing.
        1: cbn in * ; solve [crush_incl].
        1: cbn in * ; rewrite atoms_ren ; solve [crush_incl].

        cbn ; refold.
        rewrite ST_Beta_Fun.
        rewrite sren_s_flip, sren_t_split in e.
        apply R_Abort_cong.
        etransitivity ; [|eassumption].
        apply ereflexivity.
        substify.
        now asimpl.

    - (* case tIf *)
      intros Γ A B T s bl br ? IHs ? IHl ? IHr ?? sp c.
      destruct (IHs _ _ sp c) as [[HMsum (M&l&r&[HMs (?&?&?&?&es)])]|[HMsum (M&l&r&[HMs (?&?&?&?&es)])]] ; tea.

      + destruct (IHl _ _ (split_t sp) c) as (Ml & ll & rl & HMl & (?&?&?&?&etl)).
        destruct (IHr _ _ (split_t sp) c) as (Mr & lr & rr & HMr & (?&?&?&?&etr)).
        exists (TProd M (TProd Ml Mr)), (tPair l (tPair ll lr)),
          ((tIf r[tip tFst]
            rl[(tip (fun x => (tFst (tSnd x))))]⟨swap_var⟩
            rr[(tip (fun x => tSnd (tSnd x)))]⟨swap_var⟩)).
        split.
        1: clear -HMsum HMs HMl HMr ; solve [crush_incl].

        unfold interpolate_tm in *.
        prod_splitter.
        1,3: eauto 20 with typing.
        1: solve [crush_incl].
        * cbn.
          etransitivity.
          1: repeat apply union_mono ; rewrite ?atoms_ren, atoms_tm_subst, atoms_subst_tip ; cbn ; reflexivity.
          set_solver.

        * cbn ; refold.
          rewrite !swap_up2, !swap_up1, !tip_up_ren, !tip_subst ; cbn ; try easy.
          now rewrite !ST_Snd, !ST_Fst, renRen_term, renRen_term, etl, etr, es.

      + rewrite sren_s_flip, sren_t_split in es.
        destruct (IHl _ _ (split_s sp) c) as (Ml & ll & rl & HMl & (?&?&?&?&etl)).
        destruct (IHr _ _ (split_s sp) c) as (Mr & lr & rr & HMr & (?&?&?&?&etr)).
        exists (TFun M (TSum Ml Mr)),
          (tLam (tIf r (tLeft ll⟨↑⟩⟨swap_var⟩) (tRight lr⟨↑⟩⟨swap_var⟩))),
          (tIf (tApp (tVar 0) l⟨↑⟩) rl⟨↑⟩⟨swap_var⟩ rr⟨↑⟩⟨swap_var⟩).
        split.
        1: clear -HMsum HMs HMl HMr ; solve [crush_incl].

      unfold interpolate_tm in *.
      prod_splitter.
      1,3: now eauto 20 with typing.
      * cbn.
        etransitivity.
        1: repeat apply union_mono ; rewrite ?atoms_ren ; reflexivity.
        set_solver.
      * cbn.
        etransitivity.
        1: repeat apply union_mono ; rewrite ?atoms_ren ; reflexivity.
        set_solver.
      
      * cbn ; refold.
        clear -es etl etr.
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

    - (* case demote *)
      intros * _ IH -> ?? s c.
      destruct (IH _ _ s c) as [[? (M&l&r&[HM ?])]|[Hat (M&l&r&[HM (?&?&?&?&erl)])]] ; tea.

      + exists M, l, r ; split.
        1: clear -HM ; solve [crush_incl].
        easy.
      + exists (TFun M A), (tLam r), (tApp (tVar 0) l⟨↑⟩).
        split.
        1: clear -HM Hat ; solve [crush_incl].

        unfold interpolate_tm in *.
        prod_splitter.
        1,3: now eauto 20 with typing.
        1: solve [crush_incl].
        1: cbn ; rewrite atoms_ren ; set_solver.
        cbn.
        rewrite ST_Beta_Fun, <- erl.
        apply ereflexivity.
        rewrite sren_s_flip, sren_t_split.
        substify.
        now asimpl.

    - (* case tVar *)
      intros ? n T Hin ?? s c.
      destruct (find_side s n) as [[]|] eqn:e.
      3: exfalso ; now eauto using in_context_find_none.

      + right.
        apply find_side_some_l in e as (n'&A&[? ->]).
        eapply in_context_inj in Hin.
        2:now eapply sren_s_ty.
        subst.
        split.
        1: intros ; rewrite atoms_in ; tea ; set_solver.

        exists TUnit, tStar, (tVar (S n')).
        split.
        1: intros ; cbn ; set_solver.
        unfold interpolate_tm.
        prod_splitter.
        1,3: eauto with typing.
        1-2: solve [crush_incl].
        cbn.
        now rewrite sren_t_split.

      + left.
        apply find_side_some_r in e as (n'&A&[? ->]).
        eapply in_context_inj in Hin.
        2:now eapply sren_t_ty.
        subst.
        split.
        1: intros ; rewrite atoms_in ; tea ; set_solver.

        exists TUnit, tStar, (tVar (S n')).
        split.
        1: solve [crush_incl].

        unfold interpolate_tm.
        prod_splitter.
        1,3: eauto with typing.
        1-2: solve [crush_incl].
        reflexivity. 

    - (* case tConst *)
      intros Γ c ?? ? csplit.
      destruct (const_cover csplit c).
      
      + right.
        split.
        1: now right ; eexists.

        exists TUnit, tStar, (tConst c).
        split.
        1: solve [crush_incl].
        red ; prod_splitter.
        1,3: now eauto with typing.
        1-2: crush_incl.

        reflexivity.
      
      + left.
        split.
        1: now right ; eexists.

        exists TUnit, tStar, (tConst c).
        split.
        1: solve [crush_incl].
        red ; prod_splitter.
        1,3: now eauto with typing.
        1-2: crush_incl.

        reflexivity.

    - (* case tApp *)
      intros Γ A B n u _ Hn _ IHu Γs Γt s c.
      destruct (Hn _ _ s c) as
        [[IHpol (Mt&lt&rt&(IHt&?&?&?&?&et))]|[IHpol (Mt&lt&rt&(IHt&?&?&?&?&et))]].

      + left.
        cbn in *.
        specialize (IHu _ _ s c) as (Mu&lu&ru&(IHMu&?&?&?&?&eu)).
        split.
        1: clear -IHpol IHt IHMu ; solve [crush_incl].
        exists (TProd Mt Mu), (tPair lt lu),
          (tApp (rt[tip tFst]) (ru[(tip tSnd)])).
        cbn.
        split.
        1: clear -IHpol IHt IHMu ; solve [crush_incl].

        unfold interpolate_tm in *.
        prod_splitter.
        1,3: now eauto 20 with typing.
        1: solve [crush_incl].
        1:{
          cbn.
          erewrite union_mono.
          2,3: rewrite atoms_tm_subst, atoms_subst_tip ; cbn ; reflexivity.
          set_solver.
        }
        cbn.
        now rewrite !tip_up_ren, !tip_subst, ST_Fst, ST_Snd, eu, et.

      + right.
        cbn in *.
        specialize (IHu _ _ (flip_split s) (flip_csplit c)) as (Mu&lu&ru&(IHMu&?&?&?&?&eu)).
        split.
        1: clear -IHpol IHt IHMu ; solve [crush_incl].
        exists (TProd Mt Mu), (tPair lt lu),
          (tApp (rt[tip tFst]) (ru[tip tSnd])).
        cbn.
        split.
        1: clear -IHpol IHt IHMu; solve [crush_incl].
        
        unfold interpolate_tm in *.
        prod_splitter.
        1,3: now eauto 20 with typing.
        1: solve [crush_incl].
        1:{
          cbn.
          erewrite union_mono.
          2,3: rewrite atoms_tm_subst, atoms_subst_tip ; cbn ; reflexivity.
          set_solver.
        }
        cbn.
        now rewrite !tip_up_ren, !tip_subst, ST_Fst, ST_Snd, eu, et.

    - (* case tProj *)
      intros * _ IH Γs Γt s c.
      destruct (IH _ _ s c) as [[IHb (M&l&r&(HM&?&?&?&?&etm))]|[IHb (M&l&r&(HM&?&?&?&?&etm))]].
      + left.
        split.
        1: destruct b ; clear -HM IHb ; solve [crush_incl].
        exists M, l, (tProj b r).
        split.
        1: solve [crush_incl].

        unfold interpolate_tm in * ; prod_splitter.
        3: destruct b.
        1,3,4: now eauto with typing.
        1-2: easy.
        cbn.
        now rewrite etm.
      
      + right.
        split.
        1: destruct b ; clear -HM IHb ; solve [crush_incl].

        exists M, l, (tProj b r).
        split ; [easy|].
        unfold interpolate_tm in * ; prod_splitter.
        3: destruct b ; cbn.
        1,3,4: now eauto with typing.
        1-2: easy.
        cbn.
        now rewrite etm.
  Qed.

End Interpolation.