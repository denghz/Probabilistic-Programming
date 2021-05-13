module Transformer where


import Syntax
import Environment
import Helpers

type Env = (Environment [Expr -> Expr], Expr)

pdfDist ::  Dist -> Env -> [Expr -> Expr]
pdfDist (Return e) env  = pdfExp e env
pdfDist (Score e dist) (l,w) = pdfDist dist (l, Apply (Variable "*") [e,w])
pdfDist (Let (Rand x d1) d2) (l,w) = pdfDist d2 (define l x (pdfDist d1 (l,Number 1.0)), w)
pdfDist (PrimD _ id es) _ = [\x -> Number 0] --prim distribution pdf definition 

pdfExp :: Expr -> Env -> [Expr -> Expr]
pdfExp (Variable x) (l,w) = 
    do
      g <- find l x
      return (\z -> Apply (Variable "*") [substitute (define empty_env x z) w, g z])
pdfExp (Apply (Variable "+") [Number n, e]) (l,w)=
  do
    g <- pdfExp e (l,w)
    return (\z -> g (Apply (Variable "-") [z, Number n]))

pdfExp (Apply (Variable "+") [e, Number n]) (l,w) = pdfExp (Apply (Variable "+") [Number n, e]) (l,w)

pdfExp (Apply (Variable "*") [e, Number n]) (l,w) =
  do 
    g <- pdfExp e (l,w)
    return (\z -> Apply (Variable "*") [Apply (Variable "Inv") [if n < 0 then Number (-n) else Number n], 
            g (Apply (Variable "*") [z,Apply (Variable "Inv") [Number n]])])

pdfExp (Apply (Variable "*") [Number n , e]) (l,w) = pdfExp (Apply (Variable "*") [e, Number n]) (l,w) 