module Probprog(main,eval,init_env) where
import Parsing ( dialog, primwrap, print_defn, print_value )
import Syntax
import Parser
import Environment

data Value =
    Real Double       
  | BoolVal Bool      -- Booleans
  | Function ([Value] -> Value)         -- Functions
  | Nil               -- Empty list
  | Cons Value Value  -- Non-empty lists
  | PDF (Double -> Double)
  | PairVal (Value, Value)

-- An environment is a map from identifiers to values
type Env = Environment Value

eval :: Expr -> Env -> Value

eval (Number n) _ = Real n

eval (Variable x) env = find env x

eval (If e1 e2 e3) env =
  case eval e1 env of
    BoolVal True -> eval e2 env
    BoolVal False -> eval e3 env
    _ -> error "boolean required in conditional"

eval (Apply f es) env =
  apply (eval f env) (map ev es)
    where ev e1 = eval e1 env

eval (Lambda xs e1) env = abstract xs e1 env

eval e _ =
  error ("can't evaluate " ++ show e)

apply :: Value -> [Value] -> Value
apply (Function f) args = f args
apply _ _ = error "applying a non-function"

abstract :: [Ident] -> Expr -> Env -> Value
abstract xs e env = 
  Function (\args -> eval e (defargs env xs args))

elab :: Bind -> Env -> Env
elab (Val x e) env = define env x (eval e env)
elab (Samp x d) env = define env x (PDF (\_ -> 0))

elabDist :: Defn -> Env -> Env
elabDist (Prob x d) env = define env x (PDF (\_ -> 0))

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
        pureprim x f = (x, Function (primwrap x f))

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

obey (Define def) env =
  let x = def_lhs def in
  let env' = elabDist def env in
  (print_defn env' x, env')


main = dialog parser obey init_env