module Probprog(main,eval,init_env) where
import Parsing ( dialog, primwrap, print_defn, print_value )
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
  | PDF (Double -> Double)
  | PairVal (Value, Value)

-- An environment is a map from identifiers to values
type Env = Environment Value

eval :: Expr -> Env -> M Value

eval (Number n) _ = return (Real n)

eval (Variable x) env = return (find env x)

eval (If e1 e2 e3) env =
  do 
    b <- eval e1 env
    case b of
      BoolVal True -> eval e2 env
      BoolVal False -> eval e3 env
      _ -> error "boolean required in conditional"

eval (Apply f es) env =
  do
    fv <- eval f env
    args <- evalargs es env
    apply fv args

eval (Lambda xs e1) env = return (abstract xs e1 env)

eval (Pair (x, y)) env = 
  do
    xv <- eval x env
    yv <- eval y env
    return (PairVal (xv, yv))

eval (Loop bs1 e1 e2 bs2) env = 
  do 
    env' <- elabBinds bs1 env
    u env'
  where
    elabBinds bs env = 
      do 
        vs <- evalargs es env
        return (foldr (\(x,v) env -> define env x v) env $ zip xs vs)
      where 
        (xs, es) = unzip bs
        
    u env =
      do 
        b <- eval e1 env
        case b of
          BoolVal False -> do env' <- elabBinds bs2 env; u env'
          BoolVal True -> eval e2 env
          _ -> error "boolean required in while loop"



eval e _ =
  error ("can't evaluate " ++ show e)

apply :: Value -> [Value] -> M Value
apply (Function f) args = f args
apply _ _ = error "applying a non-function"

evalargs :: [Expr] -> Env -> M [Value]
evalargs [] _ = return []
evalargs (e:es) env =
  do
    v <- eval e env
    vs <- evalargs es env
    return (v:vs)

abstract :: [Ident] -> Expr -> Env -> Value
abstract xs e env = 
  Function (eval e . defargs env xs)

elab :: Bind -> Env -> M Env
elab (Val x e) env = 
  do 
    v <- eval e env
    return (define env x v)
elab (Samp x d) env = return (define env x (PDF (\_ -> 0)))

elabDist :: Defn -> Env -> M Env
elabDist (Prob x d) env = return (define env x (PDF (\_ -> 0)))

init_env :: Env
init_env = 
  make_env [constant "nil" Nil, 
            constant "true" (BoolVal True), 
            constant "false" (BoolVal False),
    pureprim "+" (\ [Real a, Real b] -> Real (a + b)),
    pureprim "-" (\ [Real a, Real b] -> Real (a - b)),
    pureprim "*" (\ [Real a, Real b] -> Real (a * b)),
    pureprim "~" (\ [Real a] -> Real (- a)),
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

obey :: Phrase -> Env -> (String, Env)

obey (Calculate dist) env =
  (print_value ("dist"), env)

obey (Evaluate exp) env = 
  applyK (eval exp env) (\v -> (print_value v, env))

obey (Define def) env =
  let x = def_lhs def in
  applyK (elabDist def env) (\env' -> (print_defn env' x, env'))


main = dialog parser obey init_env