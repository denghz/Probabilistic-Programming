{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Transformer where


import Syntax
import Environment
import Helpers

type Env = (Environment [Expr], Expr)
unrollMul :: Expr -> [Expr]
unrollMul (Apply (Variable "*") [e1,e2]) =
  unrollMul e1 ++ unrollMul e2
unrollMul e = [e]

toMul :: [Expr] -> Expr
toMul [e] = e
toMul (e:es) = Apply (Variable "*") [e, toMul es]

pdfDist ::  Dist -> Env -> IO [Expr]
pdfDist (Return e) env  = pdfExp e env
pdfDist (Score e dist) (l,w) = pdfDist dist (l, Apply (Variable "*") [e,w])
pdfDist (Let (Rand x d1) d2) (l,w) = do {f <- pdfDist d1 (l,Number 1.0); pdfDist d2 (define l x f, w)}
pdfDist (PrimD _ "Normal" es) _ =
  let mu = head es in let sigma = last es in
    return [Func [Variable "x"] (Apply (Variable "*") [
      Apply (Variable "inv")
        [Apply (Variable "*")
          [sigma, Apply (Variable "power")
                              [Apply (Variable "*") [Number 2, Variable "pi"], Number 0.5]]],
      Apply (Variable "exp")
        [Apply (Variable "~")
          [Apply (Variable "*")
            [Apply (Variable "inv") [Number 2], Apply (Variable "power") [
              Apply (Variable "*")
                [Apply (Variable "inv") [sigma], Apply (Variable "-") [Variable "x", mu]],
              Number 2
            ]]
          ]]])]
pdfDist (PrimD _ "Uniform" es) _ =
  let a = head es in let b = last es in
    return [Func [Variable "x"]
      (If (Apply (Variable "<") [Variable "x", a]) (Number 0)
        (If (Apply (Variable ">") [Variable "x", b]) (Number 0)
          (Apply (Variable "inv") [Apply (Variable "-") [a,b]])))]

pdfDist d _ = error $ show d <> " doesn't have a pdf"

pdfExp :: Expr -> Env -> IO [Expr]
pdfExp (Variable x) (l,w) =
    return $ do
      g <- find l x
      if null (freeVars g) && (null (freeVars w) || freeVars w == [x]) then
        return (Func [Variable "z"] (Apply (Variable "*") [substitute (define empty_env x (Variable "z")) w, Apply g [Variable "z"]]))
      else error "precondition doesn't match"

pdfExp (Apply (Variable "+") [Number n, e]) (l,w)=
    do
      gs <- pdfExp e (l,w)
      return $ do
        g <- gs
        return (Func [Variable "z"] (Apply g [Apply (Variable "-") [Variable "z", Number n]]))

pdfExp (Apply (Variable "+") [e, Number n]) (l,w) = pdfExp (Apply (Variable "+") [Number n, e]) (l,w)

pdfExp (Apply (Variable "*") [e, Number n]) (l,w) =
  if n == 0 then error "precondition doesn't match" else
  do
    gs <- pdfExp e (l,w)
    return $ do
      g <- gs
      return (Func [Variable "z"]
                (Apply (Variable "*")
                  [Apply (Variable "Inv") [if n < 0 then Number (-n) else Number n],
                    Apply g [Apply (Variable "*") [Variable "z",Apply (Variable "Inv") [Number n]]]]))

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
            return (Func [Variable "z"]
                    (Apply (Variable "*")
                        [Apply (Diff (Inverse f)) [Variable "z"], Apply g [Apply (Inverse f) [Variable "z"]]]))
      else error "e is not diff and monotone and invertible"
  where
    checks f = return True --check invertible and diff and monotone (reduce[diff > 0 or diff < 0] == True)

pdfExp (Pair (x,y)) (l,w) =
    let freeX = freeVars x in let freeY = freeVars y in
    if not (any (`elem` freeX) freeY) then
      let exprs = unrollMul w in
        let xw = filter ((not . null) . filter (`elem` freeX) . freeVars) exprs in
        let yw = filter ((not . null) . filter (`elem` freeY) . freeVars) exprs in
      do
        fs <- pdfExp x (l, toMul xw)
        gs <- pdfExp y (l, toMul yw)
        return
          [Func [Variable "z"]
            (Apply (Variable "*")
              [Apply f [Apply (Variable "fst") [Variable "z"]], Apply g [Apply (Variable "snd") [Variable "z"]]]) | f <- fs, g <- gs]
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

            return (Func [Variable "z"] (
              let a = Apply (Variable "fst") [Variable "z"] in
              let b  = Apply (Variable "snd") [Variable "z"] in
              Apply (Variable "*") [Apply g1 [a], substitute (define empty_env "zzz" a) (Apply g2 [b])]))

    where check f = return True -- check invertible

pdfExp e (l,w) =
    do
      let xs = freeVars e
      gs <- mapM (\x -> pdfExp (Pair (Variable x,e)) (l,w)) (freeVars e ++ concatMap freeVars (concatMap (find l) xs))
      let gs' = concat gs
      return $ do
        g <- gs'
        return (Func [Variable "t"] (Apply (Integrate g) [Variable "t"]))
