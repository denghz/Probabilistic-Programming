module Simplify where
import Syntax
import Continuation
import Helpers
import qualified Data.ByteString.Lazy.Char8 as L8
import System.Process.Typed ( readProcessStderr_, shell )

fullSimplify :: Expr -> M Expr
fullSimplify (If e1 e2 e3) = If <$> fullSimplify e1 <*> fullSimplify e2 <*> fullSimplify e3
fullSimplify (Number n) = return $ Number n
fullSimplify (Variable n) = return $ Variable n
fullSimplify (Loop bs1 e1 e2 bs2) =
  let (vs1, es1) = unzip bs1 in let (vs2, es2) = unzip bs2 in
    do
      es1' <- mapM fullSimplify es1
      es2' <- mapM fullSimplify es2
      e1' <- fullSimplify e1
      e2' <- fullSimplify e2
      return $ Loop (zip vs1 es1') e1 e2 (zip vs2 es2')
fullSimplify (Pair (e1,e2)) =
  do
    e1' <- fullSimplify e1
    e2' <- fullSimplify e2
    return $ Pair (e1', e2')
fullSimplify e@(Apply e1 es) =
    if diffFunction e then Mk (\k ->
      do
        e <- mathSimplify e
        k e)
    else Apply e1 <$> mapM fullSimplify es
  where
    mathSimplify e =
      do
        let args = unwords $ transformExpToPN e
        res <- readProcessStderr_ (shell ("python3 " <> "/home/dhz/probprog/src/simplify.py " <> args))
        let wordList = words (L8.unpack res)
        return $ readInfixExpr wordList


