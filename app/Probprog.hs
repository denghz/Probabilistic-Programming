module Probprog(main,eval,init_env) where
import Parsing(dialog, print_defn, print_value)
import Syntax
import Parser
import Environment
import Control.Monad(liftM, ap)
import Data.Maybe(isJust)

type Ans = (String, Env)
newtype M a = Mk ((a -> Ans) -> Ans)

applyK (Mk mx) = mx 

instance Monad M where
  return x = Mk (\k -> k x)
  xm >>= f = Mk (\k -> applyK xm (\x -> applyK (f x) k)) 

instance Functor M where fmap = liftM
instance Applicative M where pure = return; (<*>) = ap
data Value =
    Real Double       
  | BoolVal Bool      -- Booleans
  | Function Ident ([Value] -> M Value)         -- Functions
  | PDF Dist  -- Since we cannot evaluate it now, we add it as a value
  | NotDetermined Ident -- value cannot be determined yet
  | PairVal (Value, Value)

-- An environment is a map from identifiers to values
type Env = Environment Value

notDeterVars :: Env -> Expr -> [Ident]
notDeterVars env (Variable x) = 
  case find env x of
    NotDetermined _ -> [x]
    _ -> []
notDeterVars env (If e1 e2 e3) = notDeterVars env e1 ++ notDeterVars env e2 ++ notDeterVars env e3
notDeterVars env (Apply f es) = concatMap (notDeterVars env) es
notDeterVars env (Pair (x, y)) = notDeterVars env x ++ notDeterVars env y
notDeterVars env (Loop bs1 e1 e2 bs2) =
  concatMap (notDeterVars env) es1 ++ notDeterVars env' e1 ++ notDeterVars env' e2 ++ concatMap (notDeterVars env) es2
  where 
    (xs1, es1) = unzip bs1
    (xs2, es2) = unzip bs2
    env' = foldr (\(x,v) env -> define env x v) env (zip xs1 $ replicate (length xs1) (Real 0))
notDeterVars _ _ = []


eval :: Env -> Expr -> M Value

eval _ (Number n)  = return (Real n)

eval env (Variable x)  = return (find env x)

eval env (If e1 e2 e3)  =
  do 
    b <- eval env e1 
    case b of
      BoolVal True -> eval env e2 
      BoolVal False -> eval env e3 
      _ -> error "boolean required in conditional"

eval env (Apply f es) =
  do
    fv <- eval env f 
    args <- mapM (eval env) es
    apply fv args

eval env (Pair (x, y))  = 
  do
    xv <- eval env x 
    yv <- eval env y 
    return (PairVal (xv, yv))

eval env (Loop bs1 e1 e2 bs2)  = 
  do 
    env' <- elabBinds env bs1 
    u env'
  where
    elabBinds env bs  = 
      do 
        vs <- mapM (eval env) es
        return (foldr (\(x,v) env -> define env x v) env $ zip xs vs)
      where 
        (xs, es) = unzip bs
        
    u env =
      do 
        b <- eval env e1 
        case b of
          BoolVal False -> do env' <- elabBinds env bs2; u env'
          BoolVal True -> eval env e2 
          _ -> error "boolean required in while loop"

eval e _ =
  error ("can't evaluate " ++ show e)

simplify :: Env -> Dist -> M Dist
simplify e d = simplify' e (standardise d)

simplify' :: Env -> Dist -> M Dist
simplify' env (Return e) = Return <$> partialEval env e
simplify' env (PrimD t x es) = PrimD t x <$> mapM (partialEval env) es
simplify' env (Score e d) =
  do
    e' <- partialEval env e
    Score e' <$> simplify' env d
simplify' env (Let (Rand x d1) d2) = 
  do
    d1' <- simplify' env d1
    d2' <- simplify' (define env x $ NotDetermined x) d2
    return $ Let (Rand x d1') d2'

simplify' _ _ = error "Determinstinc bind should be eliminated before simplification"

partialEval :: Env -> Expr -> M Expr
partialEval env e = 
  if null (notDeterVars env e) then 
    do v <- eval env e 
       case v of
         Function _ _ -> return e -- e is a variable of built in function
         _ -> return (valToTree v)
  else partialEval' env e


valToTree :: Value -> Expr
valToTree (Real n) = Number n
valToTree (BoolVal True) = Variable "true"
valToTree (BoolVal False) = Variable "false"
valToTree (PairVal (v1, v2)) =  Pair (valToTree v1, valToTree v2)
valToTree v = error ("\ncannot convert the value back to Syntax Tree, " ++ show v)


partialEval' :: Env -> Expr -> M Expr 
partialEval' env (If e1 e2 e3) = 
  if null (notDeterVars env e1) then
    do
      b <- eval env e1 
      case b of
        BoolVal True -> partialEval env e2
        BoolVal False -> partialEval env e3
        _ -> error "boolean required in conditional"
  else
    do 
      t1 <- partialEval env e1
      t2 <- partialEval env e2
      t3 <- partialEval env e3
      return (If t1 t2 t3)
partialEval' env (Apply f es) =
  do
    fv <- eval env f 
    args <- mapM (partialEval env) es
    return (Apply f args)

partialEval' env (Pair (x, y)) = 
  do
    x' <- partialEval env x
    y' <- partialEval env y
    return $ Pair (x', y')

partialEval' env (Loop bs1 e1 e2 bs2) = 
  do
    ts1 <- mapM (partialEval env) es1
    t1 <- partialEval env' e1
    t2 <- partialEval env' e2
    ts2 <- mapM (partialEval env') es2
    return (Loop (zip xs1 ts1) t1 t2 (zip xs2 ts2))
  where
    (xs1, es1) = unzip bs1
    (xs2, es2) = unzip bs2
    env' = foldr (\(x,v) env -> define env x v) env (zip xs1 $ map NotDetermined xs1)

partialEval' _ e = return e

apply :: Value -> [Value] -> M Value
apply (Function _ f) args = f args
apply _ _ = error "applying a non-function"


elabDist :: Defn -> Env -> M Env
elabDist (Prob x d) env = 
  do d' <- simplify env d 
     return $ define env x (PDF d')

standardise :: Dist -> Dist
standardise = standardise' empty_env

standardise' :: Environment Expr -> Dist -> Dist
standardise' env (Let (Val x e) d)  = 
  standardise' (define env x (substitute env e)) d 
     
standardise' env (Let (Rand x d1) d2)  = 
  Let (Rand x d1') d2'
    where 
      d1' = standardise' env d1
      d2' = standardise' (define env x Empty) d2

    
standardise' env (Score e d)  = 
  let d' = standardise' env d in
     Score (substitute env e) d'

standardise' env (Return e)  = 
  Return (substitute env e)

standardise' env (PrimD t x es) =
  Let (Rand z $ PrimD t x (map (substitute env) es)) (Return $ Variable z)
  where z = newIdent env

substitute :: Environment Expr -> Expr -> Expr
substitute env (If e1 e2 e3) = If (substitute env e1) (substitute env e2) (substitute env e3)
substitute env (Apply e1 es) = Apply (substitute env e1) (map (substitute env) es)
substitute env (Pair (e1,e2)) = Pair (substitute env e1, substitute env e2)
substitute env (Loop bs1 e1 e2 bs2) =
  Loop (zip xs1 es1') e1' e2' (zip xs2 es2')
  where 
    (xs1, es1) = unzip bs1
    (xs2, es2) = unzip bs2
    es1' = map (substitute env) es1
    env' = foldr (\x e -> define e x Empty) env xs1
    e1' = substitute env' e1
    e2' = substitute env' e2
    es2' = map (substitute env') es2

substitute env (Variable v) =
  -- x = Empty means x is a random variable or x is a loop variable
  case maybe_find env v of
    Nothing -> Variable v
    Just Empty -> Variable v
    Just e -> e

substitute env e = e

newIdent :: Environment a -> Ident
newIdent env = head $ filter (\x -> x `notElem` names env) allStrings
  where
    allStrings = [c:s | s <- "":allStrings, c <- ['a'..'z'] ++ ['0'..'9']] 



data Type = Count | Uncount | PairT Type Type


nn :: Environment Type -> Expr -> Maybe Type
nn env (Variable x) = Just $ find env x 
nn env (If e1 e2 e3) = 
nn _ _ = Just Count

ac :: Dist -> Bool
ac d = isJust $ ac' empty_env d

ac' :: Environment Type -> Dist -> Maybe Type
ac' env (PrimD t _ _) = Just $ if t == DZ then Count else Uncount
ac' env (Return e) = nn env e
ac' env (Score e d) = ac' env d
ac' env (Let (Rand x d1) d2) = 
  do 
    t <- ac' env d1
    ac' (define env x t) d2

init_env :: Env
init_env = 
  make_env [constant "true" (BoolVal True), 
            constant "false" (BoolVal False),
    pureprim "+" (\ [Real a, Real b] -> Real (a + b)),
    pureprim "-" (\ [Real a, Real b] -> Real (a - b)),
    pureprim "*" (\ [Real a, Real b] -> Real (a * b)),
    pureprim "~" (\ [Real a] -> Real (- a)),
    pureprim "/" (\ [Real a, Real b] -> Real (a / b)),
    pureprim "<" (\ [Real a, Real b] -> BoolVal (a < b)),
    pureprim "<=" (\ [Real a, Real b] -> BoolVal (a <= b)),
    pureprim ">" (\ [Real a, Real b] -> BoolVal (a > b)),
    pureprim ">=" (\ [Real a, Real b] -> BoolVal (a >= b)),
    pureprim "=" (\ [a, b] -> BoolVal (a == b)),
    pureprim "<>" (\ [a, b] -> BoolVal (a /= b)),
    pureprim "fst" (\[PairVal p] -> fst p),
    pureprim "snd" (\[PairVal p] -> snd p),
    pureprim "sin" (\[Real a] -> Real $ sin a),
    pureprim "cos" (\[Real a] -> Real $ cos a),
    pureprim "tan" (\[Real a] -> Real $ tan a),
    pureprim "exp" (\[Real a] -> Real $ exp a),
    pureprim "log" (\[Real a] -> Real $ log a)]
  where constant x v = (x, v)
        primitive x f = (x, Function x f)
        pureprim x f = primitive x (return . f)

instance Eq Value where
  Real a == Real b = a == b
  BoolVal a == BoolVal b = a == b
  Function n1 _ == Function n2 _ = n1 == n2 -- only builtin function, so comparable
  _ == _ = False

instance Show Value where
  show (Real n) = show n
  show (BoolVal b) = if b then "true" else "false"
  show (Function n _) = n
  show (PDF d) = show d
  show (PairVal (x,y)) = show (x,y)

obey :: Phrase -> Env -> (String, Env)

obey (Calculate dist) env =
  applyK (simplify env dist) (\v -> (print_value v, env))

obey (Evaluate exp) env = 
  applyK (eval env exp) (\v -> (print_value v, env))

obey (Define def) env =
  let x = def_lhs def in
  applyK (elabDist def env) (\env -> (print_defn env x, env))


main = dialog parser obey init_env