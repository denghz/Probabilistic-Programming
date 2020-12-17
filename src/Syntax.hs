module Syntax where

data Phrase =                 
    Calculate Dist
  | Evaluate Expr            
  | Define Defn               
  deriving Show

data Dist = 
    Return Expr
  | PrimD Ident [Expr]
  | Let Bind Dist
  | Score Expr Dist
  deriving Show

data Expr =                  
    Number Double            
  | If Expr Expr Expr         
  | Variable Ident            
  | Apply Expr [Expr]         
  | Lambda [Ident] Expr   
  | Loop [(Ident, Expr)] Expr Expr [(Ident, Expr)]
  | Pair (Expr, Expr)
  | Empty                     
  deriving Show

data Defn =                   
   Prob Ident Dist
  deriving Show

data Bind =
    Val Ident Expr
  | Rand Ident Dist
  deriving Show

type Ident = String

def_lhs :: Defn -> Ident
def_lhs (Prob x _) = x
