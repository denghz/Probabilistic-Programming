
module Syntax where
import Data.IntervalSet(IntervalSet(..))
import Environment
data Type = T Range | P Type Type
  deriving (Eq, Show)
data Range =
  C (IntervalSet Double) | UC (IntervalSet Double) | B (IntervalSet Double) (IntervalSet Double)
  deriving (Eq, Show)
data Phrase =
    Calculate (Dist, Type)
  | Evaluate Expr
  | Define Defn
  deriving (Show,Eq)

data Dist =
    Return Expr
  | PrimD DistType Ident [Expr]
  | Let Bind Dist
  | Score Expr Dist
  | Const Type
  deriving (Show,Eq)

data DistType = DZ | DR
  deriving (Show,Eq)

data Expr =
    Number Double
  | If Expr Expr Expr
  | Variable Ident
  | Apply Expr [Expr]
  | Loop [(Ident, Expr)] Expr Expr [(Ident, Expr)]
  | Pair (Expr, Expr)
  | Inverse Expr Expr
  | Diff Expr Expr
  | Integrate Expr Expr
  | IntegrateBound Expr Expr (Maybe Expr) (Maybe Expr)
  | Func Expr Expr
  | Empty
  deriving (Show,Eq)

data Defn =
   Prob Ident Dist
  deriving (Show,Eq)

data Bind =
    Val Ident Expr
  | Rand Ident Dist
  deriving (Show,Eq)

type Ident = String

def_lhs :: Defn -> Ident
def_lhs (Prob x _) = x
