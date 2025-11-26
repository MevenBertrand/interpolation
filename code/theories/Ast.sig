base : Type
bool : Type
type : Type
term(tVar) : Type

TBase : base -> type

TUnit : type
tStar : term

TProd : type -> type -> type
tPair : term -> term -> term
tProj : bool -> term -> term

TFun : type -> type -> type
tLam : (bind term in term) -> term
tApp : term -> term -> term