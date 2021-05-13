module Transformer where


import Syntax
import Environment
import Helpers

type Env = (Environment [Expr -> Expr], Expr)

pdfDist ::  Dist -> Env -> IO [Expr -> Expr]
pdfDist (Return e) env  = pdfExp e env
pdfDist (Score e dist) (l,w) = pdfDist dist (l, Apply (Variable "*") [e,w])
pdfDist (Let (Rand x d1) d2) (l,w) = do {f <- pdfDist d1 (l,Number 1.0); pdfDist d2 (define l x f, w)}
pdfDist (PrimD _ id es) _ = return [\x -> Number 0] --prim distribution pdf to be defined 

pdfExp :: Expr -> Env -> IO [Expr -> Expr]
pdfExp (Variable x) (l,w) = 
    return $ do
      g <- find l x
      return (\z -> Apply (Variable "*") [substitute (define empty_env x z) w, g z])
pdfExp (Apply (Variable "+") [Number n, e]) (l,w)=
    do
      gs <- pdfExp e (l,w)
      return $ do
        g <- gs
        return (\z -> g (Apply (Variable "-") [z, Number n]))

pdfExp (Apply (Variable "+") [e, Number n]) (l,w) = pdfExp (Apply (Variable "+") [Number n, e]) (l,w)

pdfExp (Apply (Variable "*") [e, Number n]) (l,w) =
  do 
    gs <- pdfExp e (l,w)
    return $ do 
      g <- gs
      return (\z -> Apply (Variable "*") [Apply (Variable "Inv") [if n < 0 then Number (-n) else Number n], 
            g (Apply (Variable "*") [z,Apply (Variable "Inv") [Number n]])])

pdfExp (Apply (Variable "*") [Number n , e]) (l,w) = pdfExp (Apply (Variable "*") [e, Number n]) (l,w) 

pdfExp (Apply f [e]) (l,w) =
  if not $ diffFunction e then error "e must be differentiable"
  else
    do
      res <- checks f
      if res then
        do
          gs <- pdfExp e (l,w)
          return $ do
            g <- gs
            return (\z -> Apply (Variable "*") [Apply (Diff (Inverse f)) [z], g(Apply (Inverse f) [z])])
      else error "e is not diff and monotone and invertible"
  where
    checks f = return True