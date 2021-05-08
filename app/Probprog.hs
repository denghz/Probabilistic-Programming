{-# LANGUAGE OverloadedStrings #-}

module Probprog(main,eval,init_env) where
import Parsing(dialogm, print_defn, print_value)
import Syntax
import Parser
import qualified Data.IntervalSet as Intervals(null, member, whole, span)
import Data.IntervalSet hiding(null, member)
import qualified Data.IntegerInterval as IntInterval
import Data.Interval hiding(null, singleton, intersections, member, isSubsetOf)
import qualified Data.Interval as Interval(member, whole)
import Environment
import Control.Monad(liftM, ap)
import Data.Maybe(isJust)
import Data.Char

import qualified CPython as Py
import qualified CPython.Protocols.Object as Py
import qualified CPython.System as Py
import qualified CPython.Types as Py
import qualified CPython.Types.Dictionary as PyDict
import qualified CPython.Types.Exception as Py
import qualified CPython.Types.Module as Py
import CPython.Simple

import qualified Control.Exception as E
import           Data.Semigroup ((<>))
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           System.Directory (getCurrentDirectory)
import           System.FilePath ((</>))
import           System.IO (stdout, stderr, hPutStrLn)

type Ans = IO Env
newtype M a = Mk ((a -> Ans) -> Ans)

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
type Env = Environment Value

notDeterVars :: Env -> Expr -> [Ident]
notDeterVars env e =
  let vs = freeVars e in
    filter f vs
    where
      f v =
        case find env v of
          NotDetermined _ -> True
          _ -> False

freeVars :: Expr -> [Ident]
freeVars (Variable x) =
  [x | x /= "true" || x /= " false"]
freeVars (If e1 e2 e3) = freeVars e1 ++ freeVars e2 ++ freeVars e3
freeVars (Apply f es) = concatMap freeVars es
freeVars (Pair (x, y)) = freeVars x ++ freeVars y
freeVars (Loop bs1 e1 e2 bs2) =
  concatMap freeVars es1 ++ filerLocal (freeVars e1 ++ freeVars e2 ++ concatMap freeVars es2)
  where
    (xs1, es1) = unzip bs1
    (xs2, es2) = unzip bs2
    filerLocal = filter (`notElem` xs1)
freeVars _ = []


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

--Returns if x is an int to n decimal places
isInt :: (Integral a, RealFrac b) => a -> b -> Bool
isInt n x = round (10^fromIntegral n*(x-fromIntegral (round x)))==0

makeInterval :: (Ord a) => Extended a -> Boundary -> Extended a -> Boundary -> Interval a
makeInterval lb lbt ub ubt =
  case (lbt, ubt) of
    (Closed, Closed) -> lb <=..<= ub
    (Closed, Open) -> lb <=..< ub
    (Open, Open) -> lb <..< ub
    (Open, Closed) -> lb <..<= ub

-- Extended Real is a ring not a field

-- All builtin function should be considered
imageFunc :: Ident -> [[IntervalSet Double]] -> M [IntervalSet Double]
imageFunc "+" rs =
  if length rs /= 2 then error "only 2 arguement allowed for +"
  else return [fromList [plus x y | x <- xs, y <- ys]]
  where
    xs = if length (head rs) == 1 then toList (head (head rs)) else error "tuple arguement not allowed for +"
    ys = if length (last rs) == 1 then toList (last (head rs)) else error "tuple arguement not allowed for +"
    plus x y =
      makeInterval lb lbt ub ubt
      where
        (lbx, lbxt) = lowerBound' x
        (lby, lbyt) = lowerBound' y
        (ubx, ubxt) = upperBound' x
        (uby, ubyt) = upperBound' y
        lb = lbx + lby
        ub = ubx + uby
        lbt = if Open `elem` [lbxt, lbyt] then Open else Closed
        ubt = if Open `elem` [ubxt, ubyt] then Open else Closed
imageFunc "-" rs =
  if length rs /= 2 then error "only 2 arguement allowed for -"
  else return [fromList [minus x y | x <- xs, y <- ys]]
  where
    xs = if length (head rs) == 1 then toList (head (head rs)) else error "tuple arguement not allowed for -"
    ys = if length (last rs) == 1 then toList (last (head rs)) else error "tuple arguement not allowed for -"
    minus x y =
      makeInterval lb lbt ub ubt
      where
        (lbx, lbxt) = lowerBound' x
        (lby, lbyt) = lowerBound' y
        (ubx, ubxt) = upperBound' x
        (uby, ubyt) = upperBound' y
        ub = ubx - lby
        lb = lbx - uby
        ubt = if Open `elem` [ubxt, lbyt] then Open else Closed
        lbt = if Open `elem` [lbxt, ubyt] then Open else Closed
imageFunc "*" rs =
  if length rs /= 2 then error "only 2 arguement allowed for -"
  else return [fromList [mul x y | x <- xs, y <- ys]]
  where
    xs = if length (head rs) == 1 then toList (head (head rs)) else error "tuple arguement not allowed for *"
    ys = if length (last rs) == 1 then toList (last (head rs)) else error "tuple arguement not allowed for *"
    mul x y =
      makeInterval lb lbt ub ubt
      where
        lbx = lowerBound' x
        lby = lowerBound' y
        ubx = upperBound' x
        uby = upperBound' y
        bds = [(x*y, xt, yt) | (x, xt) <- [lbx, ubx], (y, yt) <- [lby, uby]]
        (ub, ubt1, ubt2) = maximum bds
        (lb, lbt1, lbt2) = minimum bds
        ubt = if Open `elem` [ubt1, ubt2] then Open else Closed
        lbt = if Open `elem` [lbt1, lbt2] then Open else Closed
imageFunc "<" rs =
  if length rs /= 2 then error "only 2 arguement allowed for <"
  else return [unions [less x y | x <- xs, y <- ys]]
  where
    xs = if length (head rs) == 1 then toList (head (head rs)) else error "tuple arguement not allowed for <"
    ys = if length (last rs) == 1 then toList (last (head rs)) else error "tuple arguement not allowed for <"
    less x y
      | x >=! y = singleton (Finite 0 <=..<= Finite 0)
      | x <! y = singleton (Finite 1 <=..<= Finite 1)
      | otherwise = fromList [Finite 0 <=..<= Finite 0, Finite 1 <=..<= Finite 1]
imageFunc "<=" rs =
  if length rs /= 2 then error "only 2 arguement allowed for <="
  else return [unions [lessEq x y | x <- xs, y <- ys]]
  where
    xs = if length (head rs) == 1 then toList (head (head rs)) else error "tuple arguement not allowed for <="
    ys = if length (last rs) == 1 then toList (last (head rs)) else error "tuple arguement not allowed for <="
    lessEq x y
      | x >! y = singleton (Finite 0 <=..<= Finite 0)
      | x <=! y = singleton (Finite 1 <=..<= Finite 1)
      | otherwise = fromList [Finite 0 <=..<= Finite 0, Finite 1 <=..<= Finite 1]
imageFunc ">" rs =
  if length rs /= 2 then error "only 2 arguement allowed for >"
  else return [unions [gt x y | x <- xs, y <- ys]]
  where
    xs = if length (head rs) == 1 then toList (head (head rs)) else error "tuple arguement not allowed for >"
    ys = if length (last rs) == 1 then toList (last (head rs)) else error "tuple arguement not allowed for >"
    gt x y
      | x <=! y = singleton (Finite 0 <=..<= Finite 0)
      | x >! y = singleton (Finite 1 <=..<= Finite 1)
      | otherwise = fromList [Finite 0 <=..<= Finite 0, Finite 1 <=..<= Finite 1]
imageFunc ">=" rs =
  if length rs /= 2 then error "only 2 arguement allowed for >="
  else return [unions [gtEq x y | x <- xs, y <- ys]]
  where
    xs = if length (head rs) == 1 then toList (head (head rs)) else error "tuple arguement not allowed for >="
    ys = if length (last rs) == 1 then toList (last (head rs)) else error "tuple arguement not allowed for >="
    gtEq x y
      | x <! y = singleton (Finite 0 <=..<= Finite 0)
      | x >=! y = singleton (Finite 1 <=..<= Finite 1)
      | otherwise = fromList [Finite 0 <=..<= Finite 0, Finite 1 <=..<= Finite 1]
imageFunc "=" rs =
  if length rs /= 2 then error "only 2 arguement allowed for ="
  else return [unions [eq x y | x <- xs, y <- ys]]
  where
    xs = if length (head rs) == 1 then toList (head (head rs)) else error "tuple arguement not allowed for ="
    ys = if length (last rs) == 1 then toList (last (head rs)) else error "tuple arguement not allowed for ="
    eq x y
      | x /=! y = singleton (Finite 0 <=..<= Finite 0)
      | x ==! y = singleton (Finite 1 <=..<= Finite 1)
      | otherwise = fromList [Finite 0 <=..<= Finite 0, Finite 1 <=..<= Finite 1]
imageFunc "<>" rs =
  if length rs /= 2 then error "only 2 arguement allowed for <>"
  else return [unions [notEq x y | x <- xs, y <- ys]]
  where
    xs = if length (head rs) == 1 then toList (head (head rs)) else error "tuple arguement not allowed for <>"
    ys = if length (last rs) == 1 then toList (last (head rs)) else error "tuple arguement not allowed for <>"
    notEq x y
      | x ==! y = singleton (Finite 0 <=..<= Finite 0)
      | x /=! y = singleton (Finite 1 <=..<= Finite 1)
      | otherwise = fromList [Finite 0 <=..<= Finite 0, Finite 1 <=..<= Finite 1]
imageFunc "~" rs =
  if length rs /= 1 then error "only 1 arguement allowed for ~"
  else return [fromList $ map neg xs]
  where
    xs = if length (head rs) == 1 then toList (head (head rs)) else error "tuple arguement not allowed for ~"
    neg x = makeInterval (-ub) ubt (-lb) lbt
      where
        (lb, lbt) = lowerBound' x
        (ub, ubt) = upperBound' x
imageFunc "inv" rs =
  if length rs /= 1 then error "only 1 arguement allowed for inv"
  else return [fromList $ map neg xs]
  where
    xs = if length (head rs) == 1 then toList (head (head rs)) else error "tuple arguement not allowed for inv"
    neg x = if 0 `Interval.member` x then Interval.whole
            else makeInterval (if ub /= 0 then 1/ub else NegInf) ubt (if lb /= 0 then 1/lb else PosInf) lbt
          where
            (lb, lbt) = lowerBound' x
            (ub, ubt) = upperBound' x
imageFunc "fst" rs
  | length rs /= 1 = error "only 1 arguement allowed for fst"
  | length (head rs) == 2 = return [head (head rs)]
  | otherwise = error "fst only accepts pair argument"
imageFunc "snd" rs
  | length rs /= 1 = error "only 1 arguement allowed for snd"
  | length (head rs) == 2 = return [last (head rs)]
  | otherwise = error "snd only accepts pair argument"
imageFunc "floor" rs
  | length rs /= 1 = error "only 1 arguement allowed for floor"
  | length (head rs) == 1 = return [unions intRanges]
  | otherwise = error "floor only accepts one argument"
  where
      intRanges
        = map (toIntervalSet . IntInterval.fromIntervalUnder)
            $ toList (head (head rs))
      toIntervalSet x
        = if lb /= NegInf && ub /= PosInf then
              fromList
                $ map
                    (IntInterval.toInterval . IntInterval.singleton)
                    [(fromFinite lb) .. (fromFinite ub)]
          else
              singleton $ IntInterval.toInterval x
        where
            lb = IntInterval.lowerBound x
            ub = IntInterval.upperBound x
            fromFinite (Finite n) = n
imageFunc "exp" rs
  | length rs /= 1 = error "only 1 arguement allowed for exp"
  | length (head rs) == 1 = return [fromList $ map expRange (toList (head (head rs)))]
  | otherwise = error "exp only accepts one argument"
  where
      expRange x
        = makeInterval (expER lb) lbt (expER ub) ubt
        where
            (lb, lbt) = lowerBound' x
            (ub, ubt) = upperBound' x
            expER (Finite n) = Finite (exp n)
            expER PosInf = PosInf
            expER NegInf = Finite 0
imageFunc "log" rs
  | length rs /= 1 = error "only 1 arguement allowed for log"
  | length (head rs) == 1 = return [fromList $ map logRange (toList (head (head rs)))]
  | otherwise = error "log only accepts one argument"
  where
      logRange x
        = if (lb < Finite 0) || (lb == Finite 0 && lbt == Closed) then
              error "log x is undefined when x <= 0"
          else
              makeInterval (logER lb) lbt (logER ub) ubt
        where
            (lb, lbt) = lowerBound' x
            (ub, ubt) = upperBound' x
            logER (Finite 0) = NegInf
            logER PosInf = PosInf
            logER (Finite n) = Finite (log n)
imageFunc id rs
  | id `elem` ["sin", "cos", "tan"] =
    if length rs /= 1 then error ("only 1 arguement allowed for " ++ id)
    else if length (head rs) == 1 then Mk(\k ->
      (do
        rs' <- mapM (triRange id) (toList (head (head rs)))
        k [fromList rs']))
    else error (id ++ " only accepts one argument")
    where 
      triRange id x = 
        do
          cwd <- getCurrentDirectory
          Py.initialize
          pythonpath <- Py.getPath
          T.putStrLn ("Python path at startup is: " <> pythonpath <> "\n")
          -- Appending so that the user's PYTHONPATH variable (ready by python) can go first.
          let updatedPytonpath = pythonpath <> ":/home/dhz/.local/lib/python3.6/site-packages:/usr/local/lib/python3.6/dist-packages:/usr/lib/python3/dist-packages:./test"
          T.putStrLn ("Setting Python path to: " <> updatedPytonpath <> "\n")
          Py.setPath updatedPytonpath 
          let calRanges = call "functionRange" "calRange"
          res <- calRanges 
                  [arg (T.pack $ toUpper (head id) : tail id),  
                  arg (mapER lb),
                  arg (T.pack $ show lbt),
                  arg (mapER ub),
                  arg (T.pack $ show ubt) ] []
          Py.finalize 
          let (lb, lbt) = getLb (fst res)
          let (ub, ubt) = getUb (snd res)
          return $ makeInterval lb lbt ub ubt
        where
          (lb, lbt) = lowerBound' x
          (ub, ubt) = upperBound' x
          mapER (Finite n) = Just n
          mapER _ = Nothing
          getLb Nothing = (NegInf, Open)
          getLb (Just (lb, lbt)) = (Finite lb, read $ T.unpack lbt)
          getUb Nothing = (PosInf, Open)
          getUb (Just (ub, ubt)) = (Finite ub, read $ T.unpack ubt)



imageDist :: Environment Dist -> Dist -> M [IntervalSet Double]
imageDist env (Return e) = range env e
imageDist env (Let (Rand x d1) d2) = imageDist (define env x d1) d2
imageDist env (Score e d) = imageDist env d -- unable to calculate, for safety, return the upperbound
imageDist env (PrimD _ id es) = 
    do 
      rs <- mapM (range env) es
      x' <- imagePrim id (map f rs)
      return [x']
    where
    f rs = if length rs == 1 then head rs else error $ show es ++ ", arguement of distribution cannot be tuple"

rangeToInt :: (Integral b,  RealFrac a) => Interval a -> b
rangeToInt r =
      let n = do
                n <- Data.Interval.extractSingleton r
                if isInt 10 n then return $ round n else Nothing
      in
        case n of
          Just n -> n
          Nothing -> error "Roll/WRoll distribution only accept Integer parameter"

imagePrim :: Ident -> [IntervalSet Double] -> M (IntervalSet Double)
imagePrim "Normal" rs =
  if length rs /= 2 then error "Normal distribution can only have two parameters."
  else
    let variance = last rs in let mean = head rs in
      if variance `isSubsetOf` singleton (Finite 0 <=..<= Finite 0)
        then return mean else return Intervals.whole
imagePrim "Uniform" rs =
  if length rs /= 2 then error "Unifrom distribution can only have two parameters."
  else
    return $ singleton (Intervals.span (unions rs)) --convex hull
imagePrim "Roll" rs =
  if length rs /= 1 then error "Roll distribution can only have on parameter"
  else let max = maximum $ map rangeToInt (toList $ head rs)   in
    return $ fromList (map (IntInterval.toInterval.IntInterval.singleton) [1..max])
imagePrim "WRoll" rs = let res = unions rs in let _ = map rangeToInt (toList res) in return res


range :: Environment Dist -> Expr -> M [IntervalSet Double]
range env (Pair p) =
  do
    x <- range env (fst p)
    y <- range env (snd p)
    return (x ++ y)
range _ (Number n) = return [singleton $ Finite n <=..<= Finite n]
range env (If _ e1 e2) =
  do
    rs1 <- range env e1
    rs2 <- range env e2
    if length rs1 == length rs2 then return $ zipWith union rs1 rs2
    else error $ show e1 ++ ", " ++ show e2 ++ ", don't have same dimension"
  -- this is a upperbound estimate, can be calculate more accurate by using the lattices library.
range env (Apply (Variable n) es) = 
  do
    rs <- mapM (range env) es
    imageFunc n rs

range env (Variable x) = let d = find env x in imageDist env d
range env Loop {} = return [Intervals.whole] --unable to calculate, for safety, return the upperbound

typePrim :: Environment Dist -> Dist -> M Type
typePrim env (PrimD t id es)
  | t == DZ = return Count
  | id == "Normal" =
    do
      rs' <- mapM (range env) es
      let rs = map (f id) rs'
      if Intervals.member 0 (last rs) then return Count else return Uncount

  | id == "Uniform" =
      do
        rs' <- mapM (range env) es
        let rs = map (f id) rs'
        if Intervals.null (intersections rs)
        then return Uncount else return Count
  where
    f dist rs =
      case dist of
        "WRoll" -> if length rs == 2 then head rs else error $ show es ++ ", arguement of WRoll distribution can only be pair"
        _ -> if length rs == 1 then head rs else error $ show es ++ ", arguement of" ++ dist ++ " distribution cannot be tuple"
typePrim _ d = error $ show d ++ " is not a prim dist"


data Type = Count | Uncount
  deriving Eq


nn :: Environment Dist -> Expr -> M (Maybe Type)
nn env (Variable x) = fmap Just (typePrim env (find env x))
nn env (Number  _) = return $ Just Count
nn env (If e1 e2 e3) =
  do t1 <- nn env e2
     t2 <- nn env e3
     return (if t1 == t2 then t1
              else error $ show (If e1 e2 e3) ++ ", doesn't have the same type in both branches")
nn env (Apply (Variable "+") xs)
  | null $ freeVars (head xs) = nn env (last xs)
  | null $ freeVars (last xs) = nn env (head xs)
  | otherwise = nn env (Pair (head xs, last xs))
nn _ _ = return $ Just Count

ac :: Dist -> M Bool
ac d = 
  do
    x <- ac' empty_env d
    return (isJust x)

ac' :: Environment Dist -> Dist -> M (Maybe Type)
ac' env d@(PrimD t _ _) = fmap Just (typePrim env d)
ac' env (Return e) = nn env e
ac' env (Score e d) = ac' env d
ac' env (Let (Rand x d1) d2) =
  do
    t <- ac' env d1
    ac' (define env x d1) d2

init_env :: Env
init_env =
  make_env [constant "true" (BoolVal True),
            constant "false" (BoolVal False),
    pureprim "+" (\ [Real a, Real b] -> Real (a + b)),
    pureprim "-" (\ [Real a, Real b] -> Real (a - b)),
    pureprim "*" (\ [Real a, Real b] -> Real (a * b)),
    pureprim "~" (\ [Real a] -> Real (- a)),
    pureprim "inv" (\ [Real a] -> if a /= 0 then Real (1 / a) else error "1/0 is undefined"),
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
    pureprim "log" (\[Real a] -> Real $ log a),
    pureprim "floor" (\[Real a] -> Real $ fromIntegral (floor a))]
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

obey :: Phrase -> Env -> IO Env

obey (Calculate dist) env =
  applyK (simplify env dist) (\v -> do putStrLn $ print_value v;return env)

obey (Evaluate exp) env =
  applyK (eval env exp) (\v -> do putStrLn $ print_value v;return env)

obey (Define def) env =
  let x = def_lhs def in
  applyK (elabDist def env) (\env -> (do putStrLn $ print_defn env x;return env))


main = dialogm parser obey init_env