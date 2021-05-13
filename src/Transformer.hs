{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Transformer where


import Syntax
import Environment
import Helpers

type Env = (Environment [Expr -> Expr], Expr)
unrollMul :: Expr -> [Expr]
unrollMul (Apply (Variable "*") [e1,e2]) =
  unrollMul e1 ++ unrollMul e2
unrollMul e = [e]

toMul :: [Expr] -> Expr
toMul [e] = e
toMul (e:es) = Apply (Variable "*") [e, toMul es]

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
    checks f = return True --call Mathematica
pdfExp (Pair (x,y)) (l,w) =
    let freeX = freeVars x in let freeY = freeVars y in
    if not (any (`elem` freeX) freeY) then
      let exprs = unrollMul w in
        let xw = filter ((not . null) . filter (`elem` freeX) . freeVars) exprs in
        let yw = filter ((not . null) . filter (`elem` freeY) . freeVars) exprs in
      do
        fs <- pdfExp x (l, toMul xw)
        gs <- pdfExp y (l, toMul yw)
        return [\(Pair (a,b)) -> Apply (Variable "*") [f a, g a] | f <- fs, g <- gs]
    else error "x and y are not independent"

pdfExp (Pair (Apply f [Variable x], e2)) (l,w) =
  do
    t <- check f
    if x `elem` freeVars e2 || not t then error "e1 and e2 are not independent"
    else do
       gs1 <- pdfExp(Apply f [Variable x]) (l,Number 1)
       gs2 <- pdfExp
              (substitute (define empty_env x (Variable "zzz")) e2)
              (l,substitute (define empty_env x (Variable "zzz")) w)
       return $
          do
            g1 <- gs1
            g2 <- gs2
            return (\(Pair (a,b)) -> Apply (Variable "*") [g1 a, substitute (define empty_env "zzz" a) (g2 a)])

    where check f = return True -- check invertible

-- pdfExp e env = 
--     do
--       gs <- mapM (\x -> pdfExp (Pair (Variable x,e)) env) (freeVars e)
--       let gs' = concat gs
--       return $ do
--         g <- gs'
--         return (\t -> Apply (Integrate g) [t])
