base : Type
bool : Type
type : Type
term(tVar) : Type
elim : Type

TBase : base -> type

TUnit : type
tStar : term

TProd : type -> type -> type
tPair : term -> term -> term
tProj : bool -> term -> term

TFun : type -> type -> type
tLam : (bind term in term) -> term
tApp : term -> term -> term

TEmp : type
tAbort : term -> term

TSum : type -> type -> type
tIn : bool -> term -> term
tIf : term -> (bind term in term) -> (bind term in term) -> term

eProj : bool -> elim
eApp : term -> elim
eAbort : elim
eIf : (bind term in term) -> (bind term in term) -> elim