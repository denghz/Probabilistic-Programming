module Probprog(main,eval,init_env) where
import Parsing(dialog, primwrap, print_defn, print_value)
import Syntax
import Parser
import Environment
import Control.Monad(liftM, ap)

type Ans = (String, Env)
newtype M a = Mk ((a -> Ans) -> Ans)

applyK (Mk mx) = mx 

instance Monad M where
  return x = Mk (\k ->k x)
  xm >>= f = Mk (\k -> applyK xm (\x -> applyK (f x) k)) 

instance Functor M where fmap = liftM
instance Applicative M where pure = return; (<*>) = ap
data Value =
    Real Double       
  | BoolVal Bool      -- Booleans
  | Function ([Value] -> M Value)         -- Functions
  | Nil               -- Empty list
  | Cons Value Value  -- Non-empty lists
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
notDeterVars env (Apply f es) = notDeterVars env f ++ concatMap (notDeterVars env) es
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

eval env (Lambda xs e1)  = return (abstract xs e1 env)

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

partialEval :: Env -> Expr -> M Expr
partialEval env e = 
  if null (notDeterVars env e) then 
    do v <- eval env e 
       case v of
         Function _ -> return e -- e is a built in function
         _ -> return (valToTree v)
  else partialEval' env e


valToTree :: Value -> Expr
valToTree (Real n) = Number n
valToTree (BoolVal True) = Apply (Variable "=") [Number 0, Number 0]
valToTree (BoolVal False) = Apply (Variable "=") [Number 0, Number 1]
valToTree Nil = Variable "nil"
valToTree (Cons v1 v2) = Apply (Variable ":") [valToTree v1, valToTree v2]
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
apply (Function f) args = f args
apply _ _ = error "applying a non-function"

abstract :: [Ident] -> Expr -> Env -> Value
abstract xs e env = 
  Function (flip eval e . defargs env xs)

elab :: Bind -> Env -> M Env
elab (Val x e) env = 
  do 
    v <- eval env e 
    return (define env x v)
elab (Rand x d) env = return (define env x (NotDetermined x))

elabDist :: Defn -> Env -> M Env
elabDist (Prob x d) env = 
  do d' <- standardise env d 
     return $ define env x (PDF d')

standardise :: Env -> Dist -> M Dist
standardise env (Let b d)  = 
  do env' <- elab b env; 
     d' <- standardise env' d 
     return $ if isDBind b then d' else Let b d'
  where isDBind (Val _ _) = True
        isDBind (Rand _ _ ) = False
    
standardise env (Score e d)  = 
  do d' <- standardise env d 
     t <- partialEval env e
     return (Score t d')

standardise env (Return e)  = 
  do t <- partialEval env e; return (Return t)

standardise env (PrimD x es) =
  do ts <- mapM (partialEval env) es; 
     return $ Let (Rand z $ PrimD x ts) (Return $ Variable z)
  where z = newIdent env

newIdent :: Env -> Ident
newIdent env = head $ filter (\x -> x `notElem` names env) allStrings
  where
    allStrings = [c:s | s <- "":allStrings, c <- ['a'..'z'] ++ ['0'..'9']] 


init_env :: Env
init_env = 
  make_env [constant "nil" Nil, 
            constant "true" (BoolVal True), 
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
    pureprim "head" (\ [Cons h _] -> h),
    pureprim "tail" (\ [Cons _ t] -> t),
    pureprim ":" (\ [a, b] -> Cons a b),
    pureprim "fst" (\[PairVal p] -> fst p),
    pureprim "snd" (\[PairVal p] -> snd p)]
  where constant x v = (x, v)
        primitive x f = (x, Function (primwrap x f))
        pureprim x f = primitive x (return . f)

instance Eq Value where
  Real a == Real b = a == b
  BoolVal a == BoolVal b = a == b
  Nil == Nil = True
  Cons h1 t1 == Cons h2 t2 = (h1 == h2) && (t1 == t2)
  Function _ == Function _ = error "can't compare functions"
  _ == _ = False

instance Show Value where
  show (Real n) = show n
  show (BoolVal b) = if b then "true" else "false"
  show Nil = "[]"
  show (Cons h t) = "[" ++ show h ++ shtail t ++ "]"
    where 
      shtail Nil = ""
      shtail (Cons h t) = ", " ++ show h ++ shtail t
      shtail x = " . " ++ show x
  show (Function _) = "<function>"
  show (PDF d) = show d
  show (PairVal (x,y)) = show (x,y)

obey :: Phrase -> Env -> (String, Env)

obey (Calculate dist) env =
  applyK (standardise env dist) (\v -> (print_value v, env))

obey (Evaluate exp) env = 
  applyK (eval env exp) (\v -> (print_value v, env))

obey (Define def) env =
  let x = def_lhs def in
  applyK (elabDist def env) (\env -> (print_defn env x, env))


main = dialog parser obey init_env