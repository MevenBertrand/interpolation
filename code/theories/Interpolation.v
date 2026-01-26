From Interpolation Require Import Utils Syntax Notations Reduction Typing Bidir.
From Stdlib Require Import Relations Arith Lia Bool List RelationClasses.

(** ** Primitives for context splitting *)

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

Fixpoint split_ren_s {Γ Γs Γt} (s : split Γ Γs Γt) : ren :=
  match s with
  | split_emp => id
  | split_s s' => ⇑ (split_ren_s s')
  | split_t s' => (split_ren_s s') >> ↑
  end.

Fixpoint split_ren_t {Γ Γs Γt} (s : split Γ Γs Γt) : ren :=
  match s with
  | split_emp => id
  | split_t s' => ⇑ (split_ren_t s')
  | split_s s' => (split_ren_t s') >> ↑
  end.

Lemma flip_split_inv {Γ Γs Γt} (s : split Γ Γs Γt) :
  flip_split (flip_split s) = s.
Proof.
  induction s ; cbn.
  1: easy.
  all: now rewrite IHs.
Qed.

Lemma split_ren_s_flip {Γ Γs Γt} (s : split Γ Γs Γt) :
  split_ren_s (flip_split s) = split_ren_t s.
Proof.
  induction s ; cbn.
  1: easy.
  all: now rewrite IHs.
Qed.

Lemma split_ren_t_split {Γ Γs Γt} (s : split Γ Γs Γt) :
  split_ren_t (flip_split s) = split_ren_s s.
Proof.
  rewrite <- (flip_split_inv s) at 2.
  rewrite split_ren_s_flip.
  reflexivity.
Qed.

Lemma split_ren_s_ty {Γ Γs Γt} (s : split Γ Γs Γt) :
  Γ |- (split_ren_s s) :: Γs.
Proof.
  induction s ; cbn.
  all: eauto with typing.
Qed.

Lemma split_ren_t_ty {Γ Γs Γt} (s : split Γ Γs Γt) :
  Γ |- (split_ren_t s) :: Γt.
Proof.
  eapply ren_has_type_ext.
  2: eapply split_ren_s_ty.
  rewrite split_ren_s_flip.
  reflexivity.
Qed.

Hint Resolve split_ren_s_ty split_ren_t_ty : typing.

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
  {n' & {T & in_context n' Γs T /\ n = split_ren_s s n'}}.
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
  {n' & {T & in_context n' Γt T /\ n = split_ren_t s n'}}.
Proof.
  intros e.
  rewrite <- split_ren_s_flip.
  apply find_side_some_l.
  rewrite find_flip, e.
  reflexivity.
Qed.

(** ** Atoms of a type/context *)

Fixpoint atoms_ty (p : polarity) (A : type) {struct A} : base -> Prop :=
  match A with
  | TBase b => if p then (sing b) else ∅
  | TUnit | TEmp => ∅
  | TFun A B => atoms_ty (negp p) A ∪ atoms_ty p B
  | TProd A B | TSum A B => atoms_ty p A ∪ atoms_ty p B
  end.

Fixpoint atoms_ctx (p : polarity) (Γ : context) : base -> Prop :=
  match Γ with
  | nil => ∅
  | cons A Γ => atoms_ctx p Γ ∪ (atoms_ty p A)
  end.

Lemma atoms_in n Γ T :
  in_context n Γ T ->
  (forall p, atoms_ty p T ⊆ atoms_ctx p Γ).
Proof.
  intros H.
  unfold in_context in *.
  induction n in Γ, H |- * ; cbn.
  - destruct Γ ; cbn in * ; [congruence|].
    intros ? ? ?.
    right.
    now congruence.
  - destruct Γ ; cbn in * ; [congruence|].
    intros ? ? ?.
    left.
    now apply IHn.
Qed.

Section Interpolation.

(** With the splitting of the context given by Γs and Γt and the type A,
  I is a valid interpolating type. *)
Definition interpolate_ty Γs Γt A M :=
  forall p, atoms_ty p M ⊆ (atoms_ctx p Γs) ∩ (atoms_ctx (negp p) Γt ∪ atoms_ty p A).

Definition interpolate_tm {Γ Γs Γt} (s : split Γ Γs Γt) M A t l r :=
  (Γs |- l :: M) /\ (Γt ,, M |- r :: A) /\
  r⟨⇑ (split_ren_t s)⟩[l⟨split_ren_s s⟩..] ⤳* t.

Let Pcheck Γ T t := forall Γs Γt (s : split Γ Γs Γt),
  exists M l r,
    interpolate_ty Γs Γt T M /\ interpolate_tm s M T t l r.

Let Pinf Γ T t := forall Γs Γt (s : split Γ Γs Γt),
  (
    (forall p, atoms_ty p T ⊆ atoms_ctx p Γt) /\
    (exists M l r, 
      (forall p, atoms_ty p M ⊆ (atoms_ctx p Γs) ∩ (atoms_ctx (negp p) Γt)) /\
      interpolate_tm s M T t l r)
  ) \/ (
    (forall p, atoms_ty p T ⊆ atoms_ctx p Γs) /\
    (exists M l r, 
      (forall p, atoms_ty p M ⊆ (atoms_ctx (negp p) Γs) ∩ (atoms_ctx p Γt)) /\
      interpolate_tm (flip_split s) M T t l r)
  ).

Theorem interpolation : bidir_concl Pcheck Pinf.
Proof.
  apply bidir_ind.
  - (* case tStar *)
    intros Γ Γs Γt s.
    exists TUnit, tStar, tStar.
    split.
    + unfold interpolate_ty.
      intros ; cbn.
      intros ? [].
    + red.
      prod_splitter.
      1-2: now auto with typing.
      reflexivity.
  - (* case tLam *)
    intros Γ A B t _ IH Γs Γt s.
    destruct (IH Γs (Γt,,A) (split_t s)) as (M&l&r&HM&Ht).
    exists M, l, (tLam (r⟨swap_var⟩)).
    split.
    + intros p b Hb.
      specialize (HM p b Hb).
      now cbn in *.
    + unfold interpolate_tm in * ; cbn in *.
      destruct Ht as (?&?&e).
      prod_splitter.
      1-2: now eauto with typing.
      refold.
      rewrite swap_shift2, swap_shift1, <- e.
      apply ereflexivity.
      now asimpl.
  - (* case tPair *)
    intros Γ A B t t' _ IHA _ IHB Γs Γt s.
    destruct (IHA Γs Γt s) as (M & l & r & HM & (?&?&et)).
    destruct (IHB Γs Γt s) as (M' & l' & r' & HM' & (?&?&et')).
    exists (TProd M M'), (tPair l l'),
      (tPair (r[tip tFst]) (r'[tip tSnd])).
    split.
    + intros p b [Hb|Hb'].
      1: specialize (HM p b Hb).
      2: specialize (HM' p b Hb').
      all: now cbn in *.
    + unfold interpolate_tm in * ; cbn in *.
      prod_splitter.
      1-2: now eauto 20 with typing.
      now rewrite !tip_shift, !tip_subst, ST_Fst, ST_Snd, et, et'.
  - (* case tLeft *)
    intros * _ IH ?? s.
    destruct (IH _ _ s) as (M & l & r & HM & Ht).
    exists M, l, (tLeft r).
    split.
    + intros ?? Hb.
      specialize (HM _ _ Hb).
      now cbn in *.
    + unfold interpolate_tm in * ; cbn in *.
      destruct Ht as (?&?&e).
      prod_splitter.
      1-2: eauto with typing.
      now rewrite e.
  - (* case tRight *)
    intros * _ IH ?? s.
    destruct (IH _ _ s) as (M & l & r & HM & Ht).
    exists M, l, (tRight r).
    split.
    + intros ?? Hb.
      specialize (HM _ _ Hb).
      now cbn in *.
    + unfold interpolate_tm in * ; cbn in *.
      destruct Ht as (?&?&e).
      prod_splitter.
      1-2: eauto with typing.
      now rewrite e.
  - (* case tAbort *)
    intros * _ IH ?? s.
    destruct (IH _ _ s) as (M & l & r & HM & Ht).
    exists M, l, (tAbort r).
    split.
    + intros ?? Hb.
      specialize (HM _ _ Hb).
      now cbn in *.
    + unfold interpolate_tm in * ; cbn in *.
      destruct Ht as (?&?&e).
      prod_splitter.
      1-2: eauto with typing.
      now rewrite e.
  - (* case tIf *)
    intros Γ A B T s bl br ? IHs ? IHl ? IHr ?? sp.
    destruct (IHs _ _ sp) as [[HMsum (M&l&r&[HMs (?&?&es)])]|[HMsum (M&l&r&[HMs (?&?&es)])]] ; tea.
    + destruct (IHl _ _ (split_t sp)) as (Ml & ll & rl & HMl & (?&?&etl)).
      destruct (IHr _ _ (split_t sp)) as (Mr & lr & rr & HMr & (?&?&etr)).
      unfold interpolate_tm in *.
      exists (TProd M (TProd Ml Mr)), (tPair l (tPair ll lr)),
        ((tIf r[tip tFst]
          rl[(tip (fun x => (tFst (tSnd x))))]⟨swap_var⟩
          rr[(tip (fun x => tSnd (tSnd x)))]⟨swap_var⟩)).
      split.
      * intros p x Hp.
        specialize (HMsum (negp p) x).
        specialize (HMs p x).
        specialize (HMl p x).
        specialize (HMr p x).
        now cbn in *.
      * prod_splitter.
        1-2: now eauto 20 with typing.
        cbn ; refold.
        rewrite !swap_shift2, !swap_shift1, !tip_shift, !tip_subst ; cbn ; try easy.
        now rewrite !ST_Snd, !ST_Fst, !renRen_term, etl, etr, es.
    + rewrite split_ren_s_flip, split_ren_t_split in es.
      destruct (IHl _ _ (split_s sp)) as (Ml & ll & rl & HMl & (?&?&etl)).
      destruct (IHr _ _ (split_s sp)) as (Mr & lr & rr & HMr & (?&?&etr)).
      unfold interpolate_tm in *.
      exists (TFun M (TSum Ml Mr)),
        (tLam (tIf r (tLeft ll⟨↑⟩⟨swap_var⟩) (tRight lr⟨↑⟩⟨swap_var⟩))),
        (tIf (tApp (tVar 0) l⟨↑⟩) rl⟨↑⟩⟨swap_var⟩ rr⟨↑⟩⟨swap_var⟩).
      split.
      * intros p x Hp.
        clear -HMsum HMs HMl HMr Hp.
        unfold interpolate_ty in *.
        cbn in *.
        specialize (HMsum p x).
        specialize (HMs (negp p) x).
        rewrite negp_inv in HMs.
        specialize (HMl p x).
        specialize (HMr p x).
        now cbn in *.
      * prod_splitter.
        1-2: now eauto 20 with typing.
        cbn ; refold.
        clear -es etl etr.
        rewrite !swap_shift2, !swap_shift1, !ST_Beta_Fun.
        cbn.
        epose proof (ST_If_Comm _ _ _ (eIf _ _)) as He.
        cbn in He.
        rewrite He ; clear He.
        rewrite !ST_Left, !ST_Right, !swap_shift2, !swap_shift1 ; refold.
        apply R_If_cong.
        all: etransitivity ; [|eassumption].
        all: apply ereflexivity.
        ++ now substify ; asimpl.
        ++ cbn.
          rewrite !renRen_term ; refold.
          apply subst_term_morphism.
          ** intros [|] ; cbn ; [|easy].
              now substify ; asimpl. 
          ** now substify ; asimpl.
        ++ cbn.
          rewrite !renRen_term ; refold.
          apply subst_term_morphism.
          ** intros [|] ; cbn ; [|easy].
              now substify ; asimpl. 
          ** now substify ; asimpl.
  - (* case demote *)
    intros * _ IH -> ?? s.
    destruct (IH _ _ s) as [[? (M&l&r&[HM ?])]|[Hat (M&l&r&[HM (?&?&erl)])]] ; tea.
    + exists M, l, r ; split.
      2: easy.
      intros p b [?%HM Hb]%dup ; cbn in * ; easy.
    + exists (TFun M A), (tLam r), (tApp (tVar 0) l⟨↑⟩).
      split.
      * intros p b [[HΓ%HM Hb]%dup| HA] ; cbn in *.
        1: rewrite negp_inv in HΓ ; easy.
        split ; [|easy].
        now apply Hat.
      * unfold interpolate_tm in *.
        prod_splitter.
        1-2: now eauto 20 with typing.
        cbn.
        rewrite ST_Beta_Fun, <- erl.
        apply ereflexivity.
        rewrite split_ren_s_flip, split_ren_t_split.
        substify.
        now asimpl.
  - (* case tVar *)
    intros ? n T Hin ?? s.
    destruct (find_side s n) as [[]|] eqn:e.
    3: exfalso ; now eauto using in_context_find_none.
    + right.
      apply find_side_some_l in e as (n'&A&[? ->]).
      eapply in_context_inj in Hin.
      2:now eapply split_ren_s_ty.
      subst.
      split.
      1: now eapply atoms_in.
      exists TUnit, tStar, (tVar (S n')).
      split.
      1: intros ? ? ? ; now cbn in *.
      unfold interpolate_tm.
      prod_splitter.
      1-2: eauto with typing.
      cbn.
      now rewrite split_ren_t_split.
    + left.
      apply find_side_some_r in e as (n'&A&[? ->]).
      eapply in_context_inj in Hin.
      2:now eapply split_ren_t_ty.
      subst.
      split.
      1: now eapply atoms_in.
      exists TUnit, tStar, (tVar (S n')).
      split.
      1: intros ? ? ? ; now cbn in *.
      unfold interpolate_tm.
      prod_splitter.
      1-2: eauto with typing.
      reflexivity.
  - (* case tApp *)
    intros Γ A B n u _ Hn _ IHu Γs Γt s.
    destruct (Hn _ _ s) as
      [[IHpol (Mt&lt&rt&(IHt&?&?&et))]|[IHpol (Mt&lt&rt&(IHt&?&?&et))]].
    + left.
      cbn in *.
      specialize (IHu _ _ s) as (Mu&lu&ru&(IHMu&?&?&eu)).
      split.
      1: now intros ?? Hb ; eapply IHpol ; cbn.
      exists (TProd Mt Mu), (tPair lt lu),
        (tApp (rt[tip tFst]) (ru[(tip tSnd)])).
      cbn.
      split.
      * intros ? b ? ; cbn in *.
        specialize (IHt p b).
        specialize (IHMu p b).
        specialize (IHpol (negp p) b).
        rewrite negp_inv in IHpol.
        cbn in *.
        easy.
      * unfold interpolate_tm in *.
        prod_splitter.
        1-2: now eauto 20 with typing.
        cbn.
        now rewrite !tip_shift, !tip_subst, ST_Fst, ST_Snd, eu, et.
    + right.
      cbn in *.
      specialize (IHu _ _ (flip_split s)) as (Mu&lu&ru&(IHMu&?&?&eu)).
      split.
      1: now intros ?? Hb ; eapply IHpol ; cbn.
      exists (TProd Mt Mu), (tPair lt lu),
        (tApp (rt[tip tFst]) (ru[tip tSnd])).
      cbn.
      split.
      * intros ? b ? ; cbn in *.
        specialize (IHt p b).
        specialize (IHMu p b).
        specialize (IHpol (negp p) b).
        rewrite negp_inv in IHpol.
        cbn in *.
        easy.
      * unfold interpolate_tm in *.
        prod_splitter.
        1-2: now eauto 20 with typing.
        cbn.
        now rewrite !tip_shift, !tip_subst, ST_Fst, ST_Snd, eu, et.
  - (* case tProj *)
    intros * _ IH Γs Γt s.
    destruct (IH _ _ s) as [[IHb (M&l&r&(?&?&?&etm))]|[IHb (M&l&r&(?&?&?&etm))]].
    + left.
      split.
      * intros p.
        destruct b.
        all: intros b Hb ; apply IHb.
        all: now cbn.
      * exists M, l, (tProj b r).
        split ; [easy|].
        unfold interpolate_tm in * ; prod_splitter.
        2: destruct b.
        1-3: now eauto with typing.
        cbn.
        now rewrite etm.
    + right.
      split.
      * intros p.
        destruct b.
        all: intros b Hb ; apply IHb.
        all: now cbn.
      * exists M, l, (tProj b r).
        split ; [easy|].
        unfold interpolate_tm in * ; prod_splitter.
        2: destruct b ; cbn.
        1-3: now eauto with typing.
        cbn.
        now rewrite etm.
Qed.

End Interpolation.