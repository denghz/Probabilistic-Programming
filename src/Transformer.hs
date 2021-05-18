{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Transformer where


import Syntax
import Environment
import Helpers
import System.Process.Typed ( readProcessStderr_, shell, runProcess )
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Lazy.Char8 as L8
import Control.Exception (throwIO)
import qualified Data.List as List

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
    return [Func (Variable "x") (Apply (Variable "*") [
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
    return [Func (Variable "x")
      (If (Apply (Variable "<") [Variable "x", a]) (Number 0)
        (If (Apply (Variable ">") [Variable "x", b]) (Number 0)
          (Apply (Variable "inv") [Apply (Variable "-") [a,b]])))]

pdfDist d _ = error $ show d <> " doesn't have a pdf"

pdfExp :: Expr -> Env -> IO [Expr]
pdfExp (Variable x) (l,w) =
    return $ do
      g <- find l x
      if null (freeVars g) && (null (freeVars w) || freeVars w == [x]) then
        return (Func (Variable "z") (Apply (Variable "*") [substitute (define empty_env x (Variable "z")) w, Apply g [Variable "z"]]))
      else error "precondition doesn't match"

pdfExp (Apply (Variable "+") [Number n, e]) (l,w)=
    do
      gs <- pdfExp e (l,w)
      return $ do
        g <- gs
        return (Func (Variable "z") (Apply g [Apply (Variable "-") [Variable "z", Number n]]))

pdfExp (Apply (Variable "+") [e, Number n]) (l,w) = pdfExp (Apply (Variable "+") [Number n, e]) (l,w)

pdfExp (Apply (Variable "*") [e, Number n]) (l,w) =
  if n == 0 then error "precondition doesn't match" else
  do
    gs <- pdfExp e (l,w)
    return $ do
      g <- gs
      return (Func (Variable "z")
                (Apply (Variable "*")
                  [Apply (Variable "Inv") [if n < 0 then Number (-n) else Number n],
                    Apply g [Apply (Variable "*") [Variable "z",Apply (Variable "Inv") [Number n]]]]))

pdfExp (Apply (Variable "*") [Number n , e]) (l,w) = pdfExp (Apply (Variable "*") [e, Number n]) (l,w)

pdfExp (Apply f [e@(Variable n)]) (l,w) =
  if not $ diffFunction e then error "e must be differentiable"
  else
    do
      res <- checks f
      if res then
        do
          gs <- pdfExp e (l,w)
          return $ do
            g <- gs
            return (Func (Variable "z")
                    (Apply (Variable "*")
                        [Diff (Apply (Inverse f e) [Variable "z"]) (Variable "z"), Apply g [Apply (Inverse f e) [Variable "z"]]]))
      else error "e is not diff and monotone and invertible"
  where
    checks f = 
      do
        b1 <- checkDiff f
        b2 <- checkInverse f
        b3 <- checkMonotone f
        return $ b1 && b2 && b3--check invertible and diff and monotone (reduce[diff > 0 or diff < 0] == True)

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
          [Func (Variable "z")
            (Apply (Variable "*")
              [Apply f [Apply (Variable "fst") [Variable "z"]], Apply g [Apply (Variable "snd") [Variable "z"]]]) | f <- fs, g <- gs]
    else error "x and y are not independent"

pdfExp (Pair (Apply f [Variable x], e2)) (l,w) =
  do
    t <- check f
    if x `elem` freeVars e2 || not t then error "e1 and e2 are not independent"
    else do
       gs1 <- pdfExp(Apply f [Variable x]) (l,Number 1)
       gs2' <- pdfExp
                (substitute (define empty_env x (Apply (Inverse f (Variable x)) [Variable "a"])) e2)
                (l,substitute (define empty_env x (Apply (Inverse f (Variable x)) [Variable "a"])) w)
       let gs2 = map (Func (Variable "a")) gs2'
       return $
          do
            g1 <- gs1
            g2 <- gs2

            return (Func (Variable "z") (
              let a = Apply (Variable "fst") [Variable "z"] in
              let b  = Apply (Variable "snd") [Variable "z"] in
              Apply (Variable "*") [Apply g1 [a],  Apply (Apply g2 [a]) [b]]))

    where check f = checkDiff f -- check invertible

pdfExp e (l,w) =
    do
      let xs = freeVars e
      let xs' = xs ++ concatMap freeVars (concatMap (find l) xs)
      let vs = map Variable xs'
      gs <- mapM (\x -> pdfExp (Pair (Variable x,e)) (l,w)) xs'
      let gs' = concat gs
      return $ do
        (g,v) <- zip gs' vs
        return (Func (Variable "t") (Apply (Integrate g v) [Variable "t"]))

pdfExp (If e1 e2 e3) (l,w) =
  do
    gs1 <- pdfBranch e1 e2 (l,w)
    gs2 <- pdfBranch (Apply (Variable "~") [e1]) e2 (l,w)
    return $ [Func (Variable "t") (Apply (Variable "+") [Apply g1 [Variable "t"], Apply g2 [Variable "t"]]) | g1 <- gs1, g2 <- gs2]

pdfBranch :: Expr -> Expr -> Env -> IO [Expr]
pdfBranch e1 e2 (l,w) =
  let fvE1 = freeVars e1 in
    let fvE2 = freeVars e2 in
  if not (any (`elem` fvE1) fvE2) then
    do
      e1s' <- pTrue e1 (l,w)
      gs <- pdfExp e2 (l,w)
      return $ [
        Func (Variable "t") (Apply (Variable "*") [e1', Apply g [Variable "t"]] ) | e1' <- e1s', g <- gs]
  else do
    gs <- pdfExp e2 (l,w)
    return $
      [Func (Variable "t")
          (If
            (substitute (define empty_env "x" (Variable "t")) e1)
            (Apply g [Variable "t"])
            (Number 0)) | g <- gs]

pTrue :: Expr -> Env -> IO [Expr]
pTrue (Apply (Variable "<") es) env =
  let x = head es in let y = last es in
    do
      ps <- pdfExp (Apply (Variable "-") [x, y]) env
      return $ map (\e -> IntegrateBound e (Variable "z") Nothing (Just (Number 0))) ps

pTrue (Apply (Variable ">") es) env =
  do
    es' <- pTrue (Apply (Variable "<") es) env
    return $ [Apply (Variable "-") [Number 1, e'] | e' <- es']

pTrue (Apply (Variable ">=") es) env = pTrue (Apply (Variable ">") es) env

pTrue (Apply (Variable "<=") es) env = pTrue (Apply (Variable "<") es) env


checkDiff :: Expr -> IO Bool
checkDiff e = 
  let expList = transformExpToPN (Diff (Apply e [Variable "z"]) (Variable "z")) in
  let args = unwords expList in
    do
      res <- readProcessStderr_ (shell ("python3 " <> "/home/dhz/probprog/src/checkDiff.py " <> args))
      return (read (L8.unpack res))


checkInverse :: Expr -> IO Bool
checkInverse e = 
  let expList = transformExpToPN e in
  let args = unwords expList in
    do
      res <- readProcessStderr_ (shell ("python3 " <> "/home/dhz/probprog/src/checkRealInverse.py " <> args))
      return (read (L8.unpack res))

checkMonotone :: Expr -> IO Bool
checkMonotone e = 
  let expList = transformExpToPN (Diff (Apply e [Variable "z"]) (Variable "z")) in
  let args = unwords expList in
    do
      res <- readProcessStderr_ (shell ("python3 " <> "/home/dhz/probprog/src/checkMonotone.py " <> args))
      return (read (L8.unpack res))



-- call calcaulatePdf.py to calculate the pdf by Mathematica

pdf :: Expr -> IO ()
pdf e = 
  do
    pdf <- pdfExp e (empty_env, Number 1)
    let argss = map transformExpToPN pdf
    mapM_ (\args -> runProcess (shell ("python3 " <> "/home/dhz/probprog/src/checkMonotone.py " <> unwords args))) argss
