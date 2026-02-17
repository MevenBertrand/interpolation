(** * Interpolation.MetaTheory: meta-theoretic properties of typing, including normalisation*)
From Interpolation Require Import Utils Syntax Notations Reduction ReductionConfluence Typing Bidir.

(** ** Typing and reduction *)

Section TypingRed.
  Context `{Lang}.

  (** *** Preservation of typing under reduction *)
  (** Note that a stronger variant is proven in [Equations] *)
  Lemma preservation_one (Γ : context) (T : type) (t u : term) : (Γ ⊢ t :: T) -> t ⤳ u -> (Γ ⊢ u :: T).
  Proof.
    intros Hty Hred.
    induction Hred in Γ, T, Hty |- *.
    all: try (match goal with | e : elim |- _ => destruct e ; cbn in * end ; try solve [congruence]).
    all: try (match goal with | e : _ = _ |- _ => inversion e ; subst end).
    all: repeat match goal with | H : (_ ⊢ _ _ :: _) |- _ => inversion H ; subst ; clear H ; refold end.
    all: eauto 20 with typing.
  Qed.

  Lemma preservation (Γ : context) (T : type) (t u : term) : (Γ ⊢ t :: T) -> t ⤳* u -> (Γ ⊢ u :: T).
  Proof.
    induction 2 ; eauto using preservation_one.
  Qed.

  (** *** Progress *)
  (** A well-typed term is either a normal form, or can do a reduction step*)

  Lemma progress (Γ : context) (T : type) (t : term) :
    (Γ ⊢ t :: T) -> (Γ ⊢ t ◃ T) \/ (exists u, t ⤳ u).
  Proof.
    intros Hty.
    induction Hty ; refold.
    all: repeat match goal with
      | IH : _ \/ _ |- _ => destruct IH as [?|[]] ; [|right ; eexists ; now econstructor] end.
    all: try solve [left ; eauto with typing].
    all: match goal with
        | IH : _ ⊢ _ ◃ (_ _) |- _ => (inversion IH ; subst ; clear IH)
        | IH : _ ⊢ _ ◃ TEmp |- _ => inversion IH ; subst ; clear IH
      end ;
      try solve [right ; eexists ; now constructor].
    all: left ; eauto with typing.
  Qed.

  (** *** Bidirectional typing characterises well-typed normal forms *)

  Lemma bidir_normal_ind : bidir_concl
    (fun Γ T t => forall u, t ⤳ u -> False)
    (fun Γ T t => forall u, t ⤳ u -> False).
  Proof.
    apply bidir_ind ; intros ; eauto.
    all: match goal with H : _ ⤳ _ |- _ => inversion H ; subst ; refold ; clear H end ; eauto.
    all: match goal with H : _ ⊢ _ ▹ _ |- _ => inversion H end.
  Qed.

  Lemma normal_bidir Γ T t :
    (Γ ⊢ t ◃ T) <-> ((Γ ⊢ t :: T) /\ ~(exists u, t ⤳ u)).
  Proof.
    split.
    - intros Hty.
      split.
      + now apply bidir_typing in Hty.
      + intros [? Hu].
        now eapply bidir_normal_ind in Hty.
    - intros [Hty ].
      now apply progress in Hty as [|].
  Qed.

  Lemma nf_red_eq Γ T t t' :
    (Γ ⊢ t ◃ T) ->
    t ⤳* t' ->
    t = t'.
  Proof.
    intros Hnf Hred.
    revert Hnf.
    pattern t.
    revert t Hred.
    apply clos_refl_trans_ind_right.
    1: easy.
    intros.
    exfalso.
    eapply normal_bidir ; tea.
    now eexists.
  Qed.

End TypingRed.


(** ** Normalisation *)

Section Normalisation.
  Context `{Lang}.

  (** *** Covering *)
  (** A term is covered by a predicate if it is a case tree, with nodes eliminations of
    neutrals of sum and empty types, and leaves terms that satisfy the predicate. *)
  Inductive covered (F : context -> term -> Prop) (Γ : context) : term -> Prop :=
  | cover_abort t : (Γ ⊢ t ▹ TEmp) -> covered F Γ (tAbort t)
  | cover_if A B s bl br :
      (Γ ⊢ s ▹ TSum A B) ->
      covered F (Γ,,A) bl -> covered F (Γ,,B) br ->
      covered F Γ (tIf s bl br)
  | cover_ret t : F Γ t -> covered F Γ t.

  (** This forms a monad *)
  Definition map_cover F G Γ t : (forall Δ t, F Δ t -> G Δ t) -> covered F Γ t -> covered G Γ t.
  Proof.
    intros f.
    induction 1 ; now econstructor.
  Qed.

  Definition join_cover F Γ t : covered (covered F) Γ t -> covered F Γ t.
  Proof.
    induction 1.
    3: assumption.
    all: now econstructor.
  Qed.

  (** And can be run on normal forms to yield a normal form *)
  Definition covered_nf Γ T t : covered (fun Δ t => Δ ⊢ t ◃ T) Γ t -> Γ ⊢ t ◃ T.
  Proof.
    induction 1 ; eauto with typing.
  Qed.

  (** *** Reducibility *)

  (** A term is reducible if it reduces to a value *)
  Definition _reducible (c : context -> type -> term -> Prop) (Γ : context) (T : type) (t : term) :=
    exists t', t ⤳* t' /\ c Γ T t'.

  (**
    A value at positive type is a cover of "proper values", which are either neutrals or constructors.
    A value at negative type is a normal form that, when observed, yields reducible terms. *)

  Fixpoint value (Γ : context) (T : type) (t : term) : Prop :=
    match T with
    | TBase _ | TEmp => covered (fun Δ u => Δ ⊢ u ▹ T) Γ t
    | TUnit => (Γ ⊢ t ◃ T)
    | TSum A B => covered
      (fun Δ u => (Δ ⊢ u ▹ T) \/
        (exists a, u = tLeft a /\ value Δ A a) \/ (exists b, u = tRight b /\ value Δ B b))
      Γ t
    | TProd A B => (Γ ⊢ t ◃ T) /\ (forall (b : bool), _reducible value Γ (if b then A else B) (tProj b t))
    | TFun A B => (Γ ⊢ t ◃ T) /\
        (forall Δ u ρ, (Δ ⊢ ρ :: Γ) -> value Δ A u ->
          _reducible value Δ B (tApp t⟨ρ⟩ u))
    end.

  Notation reducible := (_reducible value).

  (** *** Semantic typing *)

  (** A reducible environment is one where all values are reducible *)
  Definition reducible_env (Δ Γ : context) (γ : subst) : Prop :=
    forall i T, in_context i Γ T -> value Δ T (γ i).

  Instance sem_has_type_env : HasSemTyping context context subst := reducible_env.

  (** A term is semantically well-typed if it yields reducible values in any reducible environment *)
  Definition sem_has_type (Γ : context) (T : type) (t : term) : Prop :=
    forall (Δ : context) (γ : subst), (Δ ⊩ γ :: Γ) -> reducible Δ T t[γ].

  Instance sem_has_type_term : HasSemTyping context type term := sem_has_type.

  Ltac fold_sem_has_type :=
    change sem_has_type with
      (sem_typing (Ctx := context) (Ty := type) (Obj := term)) in * ;
    change reducible_env with
      (sem_typing (Ctx := context) (Ty := context) (Obj := subst)) in *.

  Smpl Add fold_sem_has_type : refold.

  (** *** Easy lemmas on reducibility *)
  Lemma value_red Γ T t : value Γ T t -> reducible Γ T t.
  Proof.
    intros.
    eexists ; split ; eauto ; reflexivity.
  Qed. 

  Lemma red_antired {Γ T t} t' : reducible Γ T t' -> t ⤳* t' -> reducible Γ T t.
  Proof.
    intros [v] ?.
    exists v.
    split ; [|easy].
    now etransitivity.
  Qed.

  (** *** Reify/reflect *)
  (** Neutrals are always values, and values are always normal forms. *)

  Hint Extern 0 => (progress subst) : typing.

  Lemma reify (T : type) (Γ : context) (t : term) : value Γ T t -> Γ ⊢ t ◃ T.
  Proof.
    induction T in Γ, t |- * ; cbn ; refold ; try easy.
    all: intros ; eapply covered_nf, map_cover ; tea.
    all: cbn ; eauto with typing.
    intros * [|[[]|[]]].
    all: cbn ; intuition eauto with typing.
  Qed.

  Lemma reflect (T : type) :
    (forall Γ t, (Γ ⊢ t ▹ T) -> value Γ T t).
  Proof.
    induction T ; cbn ; refold.
    all: try solve [now econstructor].
    - intros * Hne.
      split ; [eauto with typing|].
      intros b.
      apply value_red.
      assert (Γ ⊢ tProj b t ▹ (if b then T1 else T2)) by now econstructor.
      destruct b ; solve [now apply IHT1|now apply IHT2].
    - intros.
      split.
      1: now eauto with typing.
      intros.
      eapply value_red, IHT2.
      econstructor.
      1: now eauto with typing.
      now apply reify.
  Qed.

  (** *** Reducibility is stable under weakening *)

  Lemma ren_covered (F : context -> term -> Prop) (Δ Γ : context) (t : term) (r : ren) :
    (forall Δ Γ ρ t, F Γ t -> (Δ ⊢ ρ :: Γ) -> F Δ t⟨ρ⟩) ->
    (Δ ⊢ r :: Γ) ->
    covered F Γ t ->
    covered F Δ t⟨r⟩.
  Proof.
    intros HF Hren Hcov.
    induction Hcov in Δ, r, Hren |- * ; cbn ; econstructor ; now eauto with typing.
  Qed.

  Lemma ren_value (Δ Γ : context) (T : type) (t : term) (r : ren) :
    value Γ T t ->
    (Δ ⊢ r :: Γ) ->
    value Δ T t⟨r⟩.
  Proof.
    intros Hval Hren.
    induction T in Γ, Δ, t, r, Hren, Hval |- * ; cbn in *;
      try solve [intuition eauto using ren_covered with typing].
    - split ; [intuition eauto with typing|].
      intros b.
      destruct Hval as [_ Hval].
      specialize (Hval b) as [u Hu].
      exists (u⟨r⟩).
      split ; [|now destruct b ; intuition eauto with typing].
      change (tProj b t⟨r⟩) with ((tProj b t)⟨r⟩).
      now apply R_ren.
    - split ; [intuition eauto with typing|].
      intros Ξ **.
      edestruct Hval as [_ [v ]].
      1: eapply ren_comp_typing ; cycle -1 ; eassumption.
      1: eassumption.
      exists v.
      now asimpl ; refold.
    - eapply ren_covered ; tea.
      intros ?? r' ? Hval' **.
      destruct Hval' as [|[[a [->]]|[b [->]]]].
      + left ; eauto with typing.
      + right ; left.
        now exists (a⟨r'⟩).
      + right ; right.
        now exists b⟨r'⟩.
  Qed.

  Lemma sem_ren_subst (Ξ Δ Γ : context) (γ : subst) (r : ren) :
    (Δ ⊩ γ :: Γ) ->
    (Ξ ⊢ r :: Δ) ->
    Ξ ⊩ γ >> ren_term r :: Γ.
  Proof.
    intros Hγ ? i **.
    cbn.
    now eapply ren_value.
  Qed.

  (** *** Semantic typing of various substitutions *)

  Lemma sem_Up {Δ Γ : context} {A : type} {γ : subst} : (Δ ⊩ γ :: Γ) -> (Δ,,A) ⊩ ⇑ γ :: (Γ ,, A).
  Proof.
    intros Hγ [|] T ? ; cbn in * ; refold.
    - apply reflect ; eauto with typing.
    - eapply ren_value ; eauto with typing.
  Qed.

  Lemma sem_cons (Δ Γ : context) (A : type) (γ : subst) (t : term) :
    (Δ ⊩ γ :: Γ) ->
    value Δ A t ->
    Δ ⊩ t .: γ :: (Γ ,, A).
  Proof.
    intros Hγ Ht [|] ? Hin ; cbn.
    - now inversion Hin ; subst.
    - now apply Hγ.
  Qed.

  (** *** We can push eliminators to the leaves of a cover *)

  Lemma proj_cover F Γ t b :
    covered F Γ t ->
    exists v, (tProj b t) ⤳* v /\ covered (fun Δ u => exists u', u = tProj b u' /\ F Δ u') Γ v.
  Proof.
    induction 1 as [? t | ??? s * ? ? (bl'&el&?) ? (br'&er&?) |] ; cbn.
    - exists (tAbort t).
      split.
      1: now rewrite ST_Proj_Abort.
      now constructor.
    - exists (tIf s bl' br').
      split.
      1: now rewrite ST_Proj_If, el, er.
      now econstructor.
    - exists (tProj b t).
      split ; [easy|].
      constructor.
      now eexists.
  Qed.

  Lemma app_cover F Γ f t :
    covered F Γ f ->
    exists v, (tApp f t) ⤳* v /\
      covered (fun Δ u => exists u' ρ, (Δ ⊢ ρ :: Γ) /\ u = tApp u' t⟨ρ⟩ /\ F Δ u') Γ v.
  Proof.
    intros Hcov.
    induction Hcov as [? e | ??? s * |? f] in t |- * ; cbn.
    - exists (tAbort e).
      split.
      1: now rewrite ST_App_Abort.
      now constructor.
    - specialize (IHHcov1 t⟨↑⟩) as (bl'&el&?).
      specialize (IHHcov2 t⟨↑⟩) as (br'&er&?).
      eexists (tIf s bl' br').
      split.
      1: now rewrite ST_App_If, el, er.
      econstructor ; tea.
      all: eapply map_cover ; tea.
      all: cbn ; intros ?? (u'&ρ&?&[->]).
      all: exists u', (↑ >> ρ).
      all: intuition eauto with typing.
      all: now asimpl.
    - exists (tApp f t).
      split ; [easy|].
      constructor.
      eexists _, id.
      intuition eauto with typing.
      now asimpl.
  Qed.

  Lemma abort_cover F Γ t :
    covered F Γ t ->
    exists v, (tAbort t) ⤳* v /\ covered (fun Δ u => exists u', u = tAbort u' /\ F Δ u') Γ v.
  Proof.
    induction 1 as [? t | ??? s * ? ? (bl'&el&?) ? (br'&er&?) |] ; cbn.
    - exists (tAbort t).
      split.
      1: now rewrite ST_Abort_Abort.
      now constructor.
    - exists (tIf s bl' br').
      split.
      1: now rewrite ST_Abort_If, el, er.
      now econstructor.
    - eexists.
      split ; [easy|].
      apply cover_ret.
      now eexists.
  Qed.

  Lemma if_cover F Γ s bl br :
    covered F Γ s ->
    exists v, (tIf s bl br) ⤳* v /\
      covered (fun Δ u => exists u' ρ, (Δ ⊢ ρ :: Γ) /\ u = tIf u' bl⟨⇑ ρ⟩ br⟨⇑ ρ⟩ /\ F Δ u') Γ v.
  Proof.
    intros Hcov.
    induction Hcov as [? e | ??? s * |? s] in bl, br |- * ; cbn.
    - exists (tAbort e).
      split.
      1: now rewrite ST_If_Abort.
      now constructor.
    - specialize (IHHcov1 bl⟨⇑ ↑⟩ br⟨⇑ ↑⟩) as (bl'&el&?).
      specialize (IHHcov2 bl⟨⇑ ↑⟩ br⟨⇑ ↑⟩) as (br'&er&?).
      eexists (tIf s bl' br').
      split.
      1: now rewrite ST_If_If, el, er.
      econstructor ; tea.
      all: eapply map_cover ; tea.
      all: cbn ; intros ?? (u'&ρ&?&[->]).
      all: exists u', (↑ >> ρ).
      all: intuition eauto with typing.
      all: now rewrite !up_up_ren.
    - exists (tIf s bl br).
      split ; [easy|].
      constructor.
      eexists _, id.
      intuition eauto with typing.
      now rewrite !up_id.
  Qed.

  (** *** Covering and reducibility *)

  (** A term covered by reducible term reduces to a term covered by values, by
    reducing all leaves *)
  Lemma covered_red Γ T t :
    covered (fun Δ u => reducible Δ T u) Γ t ->
    exists t', t ⤳* t' /\ covered (fun Δ u => value Δ T u) Γ t'.
  Proof.
    induction 1 as [? t | ??? s * ? ? (bl'&?&?) ? (br'&?&?)|? ? [t']].
    - exists (tAbort t).
      split ; [easy|].
      now constructor.
    - exists (tIf s bl' br').
      split ; [now rewrite R_If_cong|].
      now econstructor.
    - exists t' ; split ; [easy|].
      now constructor.
  Qed.

  (** A term covered by values is reducible
    Proven by induction on the type, if it is positive we are essentially done,
    otherwise we push observations to the leaves thanks to the above lemmas. *)
  Lemma cover_value Γ T t :
    covered (fun Δ u => value Δ T u) Γ t ->
    reducible Γ T t.
  Proof.
    intros Hcov.
    induction T in Γ, T , t , Hcov |- *.
    all: try solve [now exists t ; cbn ; eauto using join_cover].
    - apply value_red ; cbn.
      apply covered_nf.
      eapply map_cover ; tea.
      now cbn.
    - apply value_red ; cbn.
      split.
      + eapply covered_nf, map_cover ; tea.
        cbn ; easy.
      + intros b.
        eapply proj_cover in Hcov as [t' []] ; cbn in *.
        eapply red_antired ; tea.
        edestruct (covered_red Γ (if b then T1 else T2) t') as (t''&?&?).
        1:{ 
          eapply map_cover ; [..|eassumption].
          cbn.
          now intros ?? (?&->&[_ Hred]).
        }
        destruct b ; now eapply red_antired.
    - apply value_red ; cbn.
      split.
      + eapply covered_nf, map_cover ; tea.
        cbn ; easy.
      + intros Δ u ρ Hρ Hred.
        eapply ren_covered in Hcov ; tea.
        2: now eauto using ren_value.
        apply (app_cover _ _ _ u) in Hcov as [t' []] ; cbn in *.
        eapply red_antired ; tea.
        edestruct (covered_red Δ T2 t') as (t''&?&?).
        1:{ 
          eapply map_cover ; [..|eassumption].
          cbn.
          intros ?? (f&?&?&->&[_ Hred']).
          replace f with f⟨id⟩ by now asimpl.
          apply Hred' ; eauto with typing.
          now eapply ren_value.
        }
        now eapply red_antired.
  Qed.

  (** Any term covered by reducible terms is reducible *)
  Lemma cover_reducible Γ T t :
    covered (fun Δ u => reducible Δ T u) Γ t ->
    reducible Γ T t.
  Proof.
    intros (?&?&?)%covered_red.
    eauto using red_antired, cover_value.
  Qed.

  (** *** Semantic typing lemmas *)

  Lemma sem_Const Γ c :
    Γ ⊩ tConst c :: const_type c.
  Proof.
    intros Δ γ Hγ.
    cbn.
    apply value_red, reflect.
    now constructor.
  Qed.

  Lemma sem_Var n Γ T :
    in_context n Γ T ->
    Γ ⊩ tVar n :: T.
  Proof.
    intros Hin Δ γ Hγ.
    specialize (Hγ _ _ Hin).
    now apply value_red.
  Qed.

  Lemma sem_Star Γ :
    Γ ⊩ tStar :: TUnit.
  Proof.
    intros ? ** ; cbn.
    apply value_red ; cbn.
    now econstructor.
  Qed.

  Lemma sem_App Γ A B f u :
    (Γ ⊩ f :: TFun A B) ->
    (Γ ⊩ u :: A) ->
    Γ ⊩ tApp f u :: B.
  Proof.
    intros Hf Hu Δ γ Hγ.
    cbn.
    destruct (Hf _ γ Hγ) as [f' (Hredf&?&Hf')].
    destruct (Hu _ γ Hγ) as [u' [Hredu]].
    cbn in *.
    apply (red_antired (tApp f' u')).
    - replace f' with (f'⟨ids⟩) by (now asimpl).
      apply Hf'.
      all: now eauto with typing.
    - now rewrite Hredf, Hredu.
  Qed.

  Lemma sem_Pair Γ A B a b :
    (Γ ⊩ a :: A) ->
    (Γ ⊩ b :: B) ->
    (Γ ⊩ tPair a b :: TProd A B).
  Proof.
    intros Ha Hb Δ γ Hγ.
    destruct (Ha _ γ Hγ) as [a' [Hreda]].
    destruct (Hb _ γ Hγ) as [b' [Hredb]].
    exists (tPair a' b').
    split ; [|split] ; cbn.
    - now rewrite Hreda, Hredb.
    - auto using reify with typing.
    - intros [].
      all: eapply red_antired ; [now apply value_red|].
      all: now rewrite ?ST_Fst, ?ST_Snd.
  Qed.

  Lemma sem_Fst Γ A B t :
    (Γ ⊩ t :: TProd A B) ->
    (Γ ⊩ tFst t :: A).
  Proof.
    intros Ht Δ γ Hγ.
    specialize (Ht _ _ Hγ) as [t' [Hred [? IH]]] ; cbn in *.
    apply (red_antired (tFst t')).
    2: now rewrite Hred.
    now specialize (IH true).
  Qed.

  Lemma sem_Snd Γ A B t :
    (Γ ⊩ t :: TProd A B) ->
    (Γ ⊩ tSnd t :: B).
  Proof.
    intros Ht Δ γ Hγ.
    specialize (Ht _ _ Hγ) as [t' [Hred [? IH]]] ; cbn in *.
    apply (red_antired (tSnd t')).
    2: now rewrite Hred.
    now specialize (IH false).
  Qed.

  Lemma sem_Lam Γ A B t :
    (Γ ,, A ⊩ t :: B) ->
    Γ ⊩ tLam t :: TFun A B.
  Proof.
    intros Ht Δ γ Hγ.
    cbn ; refold.
    edestruct (Ht (Δ,,A) (⇑ γ)) as [t' [Hred]].
    1: now eapply sem_Up.
    exists (tLam t').
    split ; [now rewrite Hred|].
    cbn.
    split.
    1: now eauto using reify with typing.
    intros Ξ v ** ; refold.
    eapply red_antired.
    2: now rewrite ST_Beta_Fun.
    edestruct (Ht Ξ) as [v' [Hred']].
    1:{
      apply sem_cons ; [|eassumption].
      now eapply sem_ren_subst.
    }
    exists v' ; split ; [|easy].
    replace (t[_]) with (t[⇑ γ]⟨⇑ ρ⟩[v..]) in Hred'
      by (substify ; now asimpl).
    assert (t[⇑ γ]⟨⇑ ρ⟩[v..] ⤳* t'⟨⇑ ρ⟩ [v..]) as Hred''
      by now rewrite Hred.
    eapply confluence in Hred'' as (v''&?&?).
    2: exact Hred'.
    enough (v' = v'') as -> by easy.
    eapply nf_red_eq ; tea.
    now apply reify.
  Qed.

  Lemma sem_Abort Γ A t :
    (Γ ⊩ t :: TEmp) ->
    (Γ ⊩ tAbort t :: A).
  Proof.
    intros Ht Δ γ Hγ.
    specialize (Ht _ _ Hγ) as [t' [Hred Hne]] ; cbn in *.
    eapply abort_cover in Hne as (t''&Hred'&?).
    eapply red_antired.
    2: now rewrite Hred, Hred'.
    eapply cover_reducible, map_cover ; tea.
    intros ?? (?&->&?).
    eapply cover_reducible.
    now constructor.
  Qed.

  Lemma sem_Left Γ A B t :
    (Γ ⊩ t :: A) ->
    (Γ ⊩ tLeft t :: TSum A B).
  Proof.
    intros Ht Δ γ Hγ.
    specialize (Ht _ _ Hγ) as [t' [Hred Hval]] ; cbn in *.
    exists (tLeft t').
    split ; [now rewrite Hred|].
    constructor.
    right ; left.
    now eexists.
  Qed.

  Lemma sem_Right Γ A B t :
    (Γ ⊩ t :: B) ->
    (Γ ⊩ tRight t :: TSum A B).
  Proof.
    intros Ht Δ γ Hγ.
    specialize (Ht _ _ Hγ) as [t' [Hred Hval]] ; cbn in *.
    exists (tRight t').
    split ; [now rewrite Hred|].
    constructor.
    right ; right.
    now eexists.
  Qed.

  Lemma sem_If Γ A B T s bl br :
    (Γ ⊩ s :: TSum A B) ->
    (Γ,,A ⊩ bl :: T) ->
    (Γ,,B ⊩ br :: T) ->
    (Γ ⊩ tIf s bl br :: T).
  Proof.
    intros Hs Hl Hr Δ γ Hγ.
    specialize (Hs _ _ Hγ) as [s' [Hred Hne]] ; cbn in *.
    eapply if_cover in Hne as (t''&Hred'&?).
    eapply red_antired.
    2: now rewrite Hred, Hred'.
    eapply cover_reducible, map_cover ; tea.
    intros Δ' ? (?&ρ&?&->&Hval).
    eapply cover_reducible.
    constructor.
    destruct Hval as [| [(a&->&?)|(b&->&?)]].
    - eapply cover_reducible.
      rewrite !up_up_subst_ren.
      econstructor ; tea.
      all: constructor.
      + now eapply Hl, sem_Up, sem_ren_subst.
      + now eapply Hr, sem_Up, sem_ren_subst.
    - eapply red_antired.
      2: now rewrite ST_Left.
      replace (_[_..]) with (bl[a .: (γ >> ren_term ρ)]).
      2:{ substify ; asimpl ; refold.
          apply subst_term_morphism ; [|easy].
          intros [|] ; cbn ; [easy|].
          apply subst_term_morphism ; [|easy].
          now intros [|].
      }
      eapply Hl, sem_cons.
      2: assumption.
      now eapply sem_ren_subst.
    - eapply red_antired.
      2: now rewrite ST_Right.
      replace (_[_..]) with (br[b .: (γ >> ren_term ρ)]).
      2:{ substify ; asimpl ; refold.
          apply subst_term_morphism ; [|easy].
          intros [|] ; cbn ; [easy|].
          apply subst_term_morphism ; [|easy].
          now intros [|].
      }
      eapply Hr, sem_cons.
      2: assumption.
      now eapply sem_ren_subst.
  Qed.

  (** *** The fundamental lemma: typing implies semantic typing *)

  Theorem fundamental Γ T (t : term) :
    (Γ ⊢ t :: T) ->
    (Γ ⊩ t :: T).
  Proof.
    intros Hty.
    induction Hty.
    - now apply sem_Const.
    - now apply sem_Var.
    - now apply sem_Star.
    - now apply sem_Lam.
    - now eapply sem_App.
    - now eapply sem_Pair.
    - now eapply sem_Fst.
    - now eapply sem_Snd.
    - now eapply sem_Abort.
    - now eapply sem_Left.
    - now eapply sem_Right.
    - now eapply sem_If.
  Qed.

  (** We conclude by using the above with the identity substitution *)
  Lemma sem_id (Γ : context) : (Γ ⊩ ids :: Γ).
  Proof.
    intros i ** ; cbn.
    apply reflect.
    eauto with typing.
  Qed.

  Corollary sem_red (Γ : context) (A : type) (t : term) : (Γ ⊩ t :: A) -> reducible Γ A t.
  Proof.
    intros Ht.
    specialize (Ht Γ ids (sem_id _)).
    enough (t[ids] = t) as [] by easy.
    now asimpl.
  Qed.

  Corollary normalisation Γ T (t : term) :
    (Γ ⊢ t :: T) ->
    exists u, (t ⤳* u) /\ (Γ ⊢ u ◃ T).
  Proof.
    intros []%fundamental%sem_red.
    eexists ; split ; intuition eauto using reify.
  Qed.

End Normalisation.