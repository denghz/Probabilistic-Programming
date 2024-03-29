module Environment(Environment, empty_env, find, maybe_find,
           define, defargs, make_env, names, within) where

import qualified Data.Map as Map
import Data.Maybe(fromMaybe)
type Ident = String

newtype Environment v = Env (Map.Map Ident v) deriving (Show,Eq)

empty_env :: Environment v
empty_env = Env Map.empty

find :: Environment v -> Ident -> v
find (Env m) x = fromMaybe (error $ show x ++ " is not defined") (Map.lookup x m)

maybe_find :: Environment v -> Ident -> Maybe v
maybe_find (Env m) x = Map.lookup x m

define :: Environment v -> Ident -> v -> Environment v
define (Env m) x v = Env (Map.insert x v m)

defargs :: Environment v -> [Ident] -> [v] -> Environment v
defargs env fps args =
  if length args == length fps then
    foldl (\ env' (x, v) -> define env' x v) env (zip fps args)
  else
    error "wrong number of args"

make_env :: [(Ident, v)] -> Environment v
make_env defs = Env (Map.fromList defs)

names :: Environment v -> [Ident]
names (Env m) = Map.keys m

within :: Environment v -> Environment v -> Environment v
within (Env m1) (Env m2) = Env (Map.union m2 m1)