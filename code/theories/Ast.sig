bool : Type
const : Type
term(tVar) : Type
elim : Type

tConst : const -> term

tStar : term

tPair : term -> term -> term
tProj : bool -> term -> term

tLam : (bind term in term) -> term
tApp : term -> term -> term

tAbort : term -> term

tIn : bool -> term -> term
tIf : term -> (bind term in term) -> (bind term in term) -> term

eProj : bool -> elim
eApp : term -> elim
eAbort : elim
eIf : (bind term in term) -> (bind term in term) -> elim