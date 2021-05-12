import Syntax
fullSimplify :: Expr -> Expr
fullSimplify (If e1 e2 e3) = If (fullSimplify e1) (fullSimplify e2) (fullSimplify e3)
fullSimplify (Number n) = Number n
fullSimplify (Variable n) = Variable n
fullSimplify (Loop bs1 e1 e2 bs2) = let (vs1, es1) = unzip bs1 in let (vs2, es2) = unzip bs2 in
  Loop (zip vs1 (map fullSimplify es1)) (fullSimplify e1) (fullSimplify e2) (zip vs2 (map fullSimplify es2))
fullSimplify (Pair (e1,e2)) = Pair (fullSimplify e1, fullSimplify e2)
fullSimplify e@(Apply e1 es) =  
    if diffFunction e then mathSimplify
    else Apply e1 (map fullSimplify es)


diffFunction :: Expr -> Bool
diffFunction (Number _) = True
diffFunction (Variable _) = True
diffFunction (Apply (Variable id) es)
  | id `elem` ["+", "-", "*", "~", "inv", "sin", "cos", "tan", "exp", "log"] =
    all diffFunction es
  | otherwise = False
diffFunction _ = False

