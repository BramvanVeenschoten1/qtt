


data Expr
  = Var Int
  | Pi Span Name Mult Expr Expr
  | Lam Span Name Mult Expr Expr

type Constructor = (Name,Span,Expr)
type Inductive = (Name,Expr,Int,[Constructor])
type Clause = (Span,[Pattern],Expr)
type Function = (Name,Span,Expr,[Clause])

data ASTDecl
  = ASTInductive [Inductive]
  | ASTFixpoint  [Function]
  | ASTConstant  [(Name,Span,Expr,Expr)]
  | ASTPostulate [(Name,Span,Expr)]

type ASTModule = [ASTDecl]