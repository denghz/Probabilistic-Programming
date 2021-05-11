
module Continuation where
import Environment
import Syntax

import Control.Monad(liftM, ap)
type Env = Environment Value
type Ans = IO Env
newtype M a = Mk ((a -> Ans) -> Ans)

applyK :: M a -> (a -> Ans) -> Ans
applyK (Mk mx) = mx

instance Monad M where
  return x = Mk (\k -> k x)
  xm >>= f = Mk (\k -> applyK xm (\x -> applyK (f x) k))

instance Functor M where fmap = liftM
instance Applicative M where pure = return; (<*>) = ap

data Value =
    Real Double
  | BoolVal Bool  -- Booleans
  | Function Ident ([Value] -> M Value)  -- Functions
  | PDF Dist  -- Since we cannot evaluate it now, we add it as a value
  | NotDetermined Ident -- value cannot be determined yet
  | PairVal (Value, Value)

-- An environment is a map from identifiers to values