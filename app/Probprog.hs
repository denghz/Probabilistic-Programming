module Probprog(main,eval,init_env) where
import Parsing ( dialog, primwrap, print_defn, print_value )
import Syntax
import Parser
import Environment

data Value =
    IntVal Integer    -- Integers
  | BoolVal Bool      -- Booleans
  | Function ([Value] -> Value)         -- Functions
  | Nil               -- Empty list
  | Cons Value Value  -- Non-empty lists

-- An environment is a map from identifiers to values
type Env = Environment Value

eval :: Expr -> Env -> Value

eval (Number n) _ = IntVal n

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

eval (Let d e1) env = eval e1 (elab d env)

eval e _ =
  error ("can't evaluate " ++ pretty e)

apply :: Value -> [Value] -> Value
apply (Function f) args = f args
apply _ _ = error "applying a non-function"

abstract :: [Ident] -> Expr -> Env -> Value
abstract xs e env = 
  Function (\args -> eval e (defargs env xs args))

elab :: Defn -> Env -> Env
elab (Val x e) env = define env x (eval e env)

elab (Rec x (Lambda xs e1)) env =
  env' where env' = define env x (abstract xs e1 env')
elab (Rec _ _) _ =
  error "RHS of letrec must be a lambda"

init_env :: Env
init_env = 
  make_env [constant "nil" Nil, 
            constant "true" (BoolVal True), 
            constant "false" (BoolVal False),
    pureprim "+" (\ [IntVal a, IntVal b] -> IntVal (a + b)),
    pureprim "-" (\ [IntVal a, IntVal b] -> IntVal (a - b)),
    pureprim "*" (\ [IntVal a, IntVal b] -> IntVal (a * b)),
    pureprim "div" (\ [IntVal a, IntVal b] -> 
      if b == 0 then error "Dividing by zero" else IntVal (a `div` b)),
    pureprim "mod" (\ [IntVal a, IntVal b] ->
      if b == 0 then error "Dividing by zero" else IntVal (a `mod` b)),
    pureprim "~" (\ [IntVal a] -> IntVal (- a)),
    pureprim "<" (\ [IntVal a, IntVal b] -> BoolVal (a < b)),
    pureprim "<=" (\ [IntVal a, IntVal b] -> BoolVal (a <= b)),
    pureprim ">" (\ [IntVal a, IntVal b] -> BoolVal (a > b)),
    pureprim ">=" (\ [IntVal a, IntVal b] -> BoolVal (a >= b)),
    pureprim "=" (\ [a, b] -> BoolVal (a == b)),
    pureprim "<>" (\ [a, b] -> BoolVal (a /= b)),
    pureprim "integer" (\ [a] ->
      case a of IntVal _ -> BoolVal True; _ -> BoolVal False),
    pureprim "head" (\ [Cons h _] -> h),
    pureprim "tail" (\ [Cons _ t] -> t),
    pureprim ":" (\ [a, b] -> Cons a b)]
  where constant x v = (x, v)
        pureprim x f = (x, Function (primwrap x f))

instance Eq Value where
  IntVal a == IntVal b = a == b
  BoolVal a == BoolVal b = a == b
  Nil == Nil = True
  Cons h1 t1 == Cons h2 t2 = (h1 == h2) && (t1 == t2)
  Function _ == Function _ = error "can't compare functions"
  _ == _ = False

instance Show Value where
  show (IntVal n) = show n
  show (BoolVal b) = if b then "true" else "false"
  show Nil = "[]"
  show (Cons h t) = "[" ++ show h ++ shtail t ++ "]"
    where 
      shtail Nil = ""
      shtail (Cons h t) = ", " ++ show h ++ shtail t
      shtail x = " . " ++ show x
  show (Function _) = "<function>"

obey :: Phrase -> Env -> (String, Env)

obey (Calculate exp) env =
  (print_value (eval exp env), env)

obey (Define def) env =
  let x = def_lhs def in
  let env' = elab def env in
  (print_defn env' x, env')

main = dialog parser obey init_env