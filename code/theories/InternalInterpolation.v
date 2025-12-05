Definition interpolate_Pi
  (V : Type)
  (VA : V -> Type)
  (VB : V -> Type)
  (A : forall {x : V}, VA x -> Type)
  (B : forall {x : V}, VB x -> Type)
  (t : forall {x : V} {xA : VA x} {xB : VB x}, A xA -> B xB) :
  { I : V -> Type &
  { u : forall (x : V) (xA : VA x), A xA -> I x &
  { v : forall (x : V) (xB : VB x), I x -> B xB &
    forall (x : V) (xA : VA x) (xB : VB x) (a : A xA), t a = v x xB (u x xA a)}}}.
Proof.
  exists (fun x => (forall (xB : VB x), B x xB)).
  exists (fun x xA a (xB : VB x) => t x xA xB a).
  exists (fun x xB f => f xB).
  reflexivity.
Defined.

Definition interpolate_Sig
  (V : Type)
  (VA : V -> Type)
  (VB : V -> Type)
  (A : forall {x : V}, VA x -> Type)
  (B : forall {x : V}, VB x -> Type)
  (t : forall {x : V} {xA : VA x} {xB : VB x}, A xA -> B xB) :
  { I : V -> Type &
  { u : forall (x : V) (xA : VA x), A xA -> I x &
  { v : forall (x : V) (xB : VB x), I x -> B xB &
    forall (x : V) (xA : VA x) (xB : VB x) (a : A xA), t a = v x xB (u x xA a)}}}.
Proof.
  exists (fun x => ({xA : VA x & A x xA})).
  exists (fun x xA a => existT _ xA a).
  exists (fun x xB (s : {xA : VA x & A x xA}) => let (xA,a) := s in t x xA xB a).
  reflexivity.
Defined.