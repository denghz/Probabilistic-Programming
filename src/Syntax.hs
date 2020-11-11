module Syntax where

data Phrase =                 
    Calculate Dist            
  | Define Defn               
  deriving Show

data Dist = 
    Return Expr
  | DZ DZ
  | DR DR
  | Let Bind Dist
  | Score Expr Dist
  deriving Show

data DZ = 
  Roll Expr | WRoll [(Expr, Expr)]
  deriving Show

data DR = 
  Uniform (Expr,Expr) | Normal (Expr, Expr)
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
  | Samp Ident Dist
  deriving Show

type Ident = String

def_lhs :: Defn -> Ident
def_lhs (Prob x _) = x
