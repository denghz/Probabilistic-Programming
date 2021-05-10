{-# LANGUAGE OverloadedStrings #-}

module Probprog(main,eval,init_env) where
import Parsing(dialog, print_defn, print_value)
import Syntax
import Parser
import qualified Data.IntervalSet as Intervals(intersection, null, member, whole, span, union)
import Data.IntervalSet hiding(null, member)
import qualified Data.IntegerInterval as IntInterval
import Data.Interval hiding(null, singleton, intersections, member, isSubsetOf)
import qualified Data.Interval as Interval(member, whole)
import Environment
import Control.Monad(liftM, ap)
import Data.Maybe(isJust)
import Data.Char
import Data.Bifunctor
import Data.Bitraversable


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
import           System.IO (stdout, stderr, hPutStrLn, Newline (CRLF))

type Ans = IO Env
newtype M a = Mk ((a -> Ans) -> Ans)

data Range =
  C (IntervalSet Double) | UC (IntervalSet Double) | B (IntervalSet Double) (IntervalSet Double)
  deriving (Eq, Show)
  -- either count or uncount or both are possible
  -- Boundary of C set is in the set

getC :: Range -> Maybe (IntervalSet Double)
getC (C r) = Just r
getC (UC r) = Nothing
getC (B r1 r2) = Just r1


liftMId :: Monad m => (IntervalSet Double -> m (IntervalSet Double)) -> Range -> m Range
liftMId f (C r) = do {r' <- f r; return $ C r'}
liftMId f (UC r) = do {r' <- f r; return $ UC r'}
liftMId f (B r1 r2)  = do {r1' <- f r1; r2' <- f r2; return $ B r1' r2'}

liftId :: (IntervalSet Double -> IntervalSet Double) -> Range -> Range
liftId f (C r) = C (f r)
liftId f (UC r) = UC (f r)
liftId f (B r1 r2) = B (f r1) (f r2)

liftUCtoC :: (IntervalSet Double -> IntervalSet Double) -> Range -> Range
liftUCtoC f (C r) = C (f r)
liftUCtoC f (UC r) = C (f r)
liftUCtoC f (B r1 r2) = C (f r1 `union` f r2)

combineCUC :: Range -> Range -> Range
combineCUC (C r1) (UC r2) = B r1 r2
combineCUC (UC r1) (C r2) = B r2 r1

lift2BothtoC :: (IntervalSet Double -> IntervalSet Double -> IntervalSet Double) -> Range -> Range -> Range
lift2BothtoC op (C r1) (C r2) = C (r1 `op` r2)
lift2BothtoC op (C r1) (UC r2) = C (r1 `op` r2)
lift2BothtoC op (C r1) (B r2 r3) = C ((r1 `op` r2) `union` (r1 `op` r3))
lift2BothtoC op (UC r1) (C r2) = C (r1 `op` r2)
lift2BothtoC op (UC r1) (UC r2) = C (r1 `op` r2)
lift2BothtoC op (UC r1) (B r2 r3) = C ((r1 `op` r2) `union` (r1 `op` r3))
lift2BothtoC op (B r1 r2) (C r3) = C ((r1 `op` r3) `union` (r1 `op` r2))
lift2BothtoC op (B r1 r2) (UC r3) = C ((r1 `op` r3) `union` (r2 `op` r3))
lift2BothtoC op (B r1 r2) (B r3 r4) = C (unions [r1 `op` r3,r1 `op` r3, r1 `op` r4, r2 `op` r4])

lift2BothtoUC :: (IntervalSet Double -> IntervalSet Double -> IntervalSet Double) -> Range -> Range -> Range
lift2BothtoUC op c1 c2 = ctoUC $ lift2BothtoC op c1 c2
  where
    ctoUC (C r) = UC r

lift2CCtoC :: (IntervalSet Double -> IntervalSet Double -> IntervalSet Double) -> Range -> Range -> Range
lift2CCtoC op (C r1) (C r2) = C (r1 `op` r2)
lift2CCtoC op (C r1) (UC r2) = UC (r1 `op` r2)
lift2CCtoC op (C r1) (B r2 r3) = B (r1 `op` r2) (r1 `op` r3)
lift2CCtoC op (UC r1) (C r2) = UC (r1 `op` r2)
lift2CCtoC op (UC r1) (UC r2) = UC (r1 `op` r2)
lift2CCtoC op (UC r1) (B r2 r3) = UC ((r1 `op` r2) `union` (r1 `op` r3))
lift2CCtoC op (B r1 r2) (C r3) = B (r1 `op` r3) (r1 `op` r2)
lift2CCtoC op (B r1 r2) (UC r3) = UC ((r1 `op` r3) `union` (r2 `op` r3))
lift2CCtoC op (B r1 r2) (B r3 r4) = B (r1 `op` r3) (unions [r1 `op` r3, r1 `op` r4, r2 `op` r4])


data Type = T Range | P Type Type
  deriving (Eq, Show)

checkType :: Type -> Type -> Bool
checkType (P t1 t2) (P t3 t4) = checkType t1 t3 && checkType t2 t4
checkType (T r1) (T r2) = checkRange r1 r2
  where
    checkRange (C _) (C _) = True
    checkRange (UC _) (UC _) = True
    checkRange _ _ = False

unionType :: Type -> Type -> Type
unionType = lift2Type (lift2CCtoC Intervals.union)

lift2Type :: (Range -> Range -> Range) -> Type -> Type -> Type
lift2Type f (T r1) (T r2) = T (f r1 r2)
lift2Type f (P t1 t2) (P t3 t4) = P (lift2Type f t1 t3) (lift2Type f t2 t4)
lift2Type _ _ _= error "dimension doesn't match "

getRange :: Type -> Range
getRange (T r) = r

isPair :: Type -> Bool
isPair (P _ _) = True
isPair _ = False

fstType :: Type -> Type
fstType (P t1 t2) = t1

sndType :: Type -> Type
sndType (P t1 t2) = t2

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
freeVars (If e1 e2 e3) = freeVars e1 <> freeVars e2 <> freeVars e3
freeVars (Apply f es) = concatMap freeVars es
freeVars (Pair (x, y)) = freeVars x <> freeVars y
freeVars (Loop bs1 e1 e2 bs2) =
  concatMap freeVars es1 <> filerLocal (freeVars e1 <> freeVars e2 <> concatMap freeVars es2)
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
  error ("can't evaluate " <> show e)

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
valToTree v = error ("\ncannot convert the value back to Syntax Tree, " <> show v)


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
    allStrings = [c:s | s <- "":allStrings, c <- ['a'..'z'] <> ['0'..'9']]

--Returns if x is an int to n decimal places
isInt :: (Integral a, RealFrac b) => a -> b -> Bool
isInt n x = round (10^fromIntegral n*(x-fromIntegral (round x)))==0

-- Extended Real is a ring not a field
map1Ints :: (Interval Double -> Interval Double) -> IntervalSet Double -> IntervalSet Double
map1Ints f xs = fromList [f x | x <- toList xs]

map2Ints :: (Interval Double -> Interval Double -> Interval Double) -> IntervalSet Double -> IntervalSet Double -> IntervalSet Double
map2Ints f xs ys = fromList [f x y | x <- toList xs, y <- toList ys]
-- All builtin function should be considered
imageFunc :: Ident -> [Type] -> M Type
imageFunc id args
  | id `elem` ["+", "-", "*", "<", "<=", ">", ">=", "=", "<>"] =
      let x = head args in let y = last args in
      let rx = getRange x in let ry = getRange y in
      if length args /= 2 then  error $ "only 2 arguement allowed for " <> id
      else if id `elem` ["+", "-", "*"] then return (T (lift2CCtoC (binop id) rx ry))
      else return (T $ C (unions [comp id x y | x <- rangeToList rx, y <- rangeToList ry ])) -- id `elem` ["<", "<=", ">", ">=", "=", "<>"]
  | id `elem` ["~", "inv", "fst", "snd", "floor", "sin", "cos", "tan"] =
      let x = head args in
      if length args /= 1 then error $ "only 1 arguement allowed for " <> id
      else
        case id of
          "fst" ->  return $ fstType x
          "snd" -> return $ sndType x
          id -> let rx = getRange x in
            if id `elem` ["sin", "cos", "tan"] then
              Mk (\k ->
              (do
              r <- liftMId (mapM1 (triRange id)) rx
              k (T r)))
            else if id == "floor" then return $ T (liftUCtoC (minop id) rx)
            else return $ T ( liftId (minop id) rx)
  where
    mapM1 f xs =
      do
        xs' <- mapM f (toList xs)
        return (fromList xs')
    comp id =
      case id of 
        "<" -> less
        "<=" -> lessEq
        ">" -> gt
        ">=" -> gtEq
        "=" -> eq
        "<>" -> notEq
    minop id =
      case id of
        "~" -> map1Ints neg
        "inv" -> map1Ints inv
        "floor" -> floor
        "exp" -> map1Ints expRange
        "log" -> map1Ints logRange
    binop id =
      case id of
        "+" -> map2Ints plus
        "-" -> map2Ints minus
        "*" -> map2Ints mul
    plus x y = interval (lb,lbt) (ub,ubt)
      where
        (lbx, lbxt) = lowerBound' x
        (lby, lbyt) = lowerBound' y
        (ubx, ubxt) = upperBound' x
        (uby, ubyt) = upperBound' y
        lb = lbx + lby
        ub = ubx + uby
        lbt = if Open `elem` [lbxt, lbyt] then Open else Closed
        ubt = if Open `elem` [ubxt, ubyt] then Open else Closed
    minus x y = interval (lb, lbt) (ub, ubt)
      where
        (lbx, lbxt) = lowerBound' x
        (lby, lbyt) = lowerBound' y
        (ubx, ubxt) = upperBound' x
        (uby, ubyt) = upperBound' y
        ub = ubx - lby
        lb = lbx - uby
        ubt = if Open `elem` [ubxt, lbyt] then Open else Closed
        lbt = if Open `elem` [lbxt, ubyt] then Open else Closed
    mul x y =
      interval (lb, lbt) (ub, ubt)
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

    isLt (r1,b1) (r2,b2) =
       (b1 || all isSingleton rs1') && (b2 || all isSingleton rs2')
      where
        rs1 = toDescList r1
        rs2 = toDescList r2
        rs2' = filter (\l -> lowerBound l < upperBound (head rs1)) rs2
        rs1' = filter (\s -> upperBound s > lowerBound (last rs2)) rs1

    falseRange = singleton (Finite 0 <=..<= Finite 0)
    trueRange = singleton (Finite 1 <=..<= Finite 1)
    -- case not handled (negInf, 0) Intersection Z < ((negInf, 0) Intersection Z) union [1,2] should be true
    
    rangeToList (C r) = [(r, True)]
    rangeToList (UC r) = [(r, False)]
    rangeToList (B r1 r2) = [(r1, True), (r2, False)]

    less (r1, True) (r2, True) =lessCC r1 r2
    less r1 r2 = lessUCC r1 r2

    lessCC xs ys
      | xMin >=! yMax = falseRange
      | xMax <! yMin = trueRange
      | otherwise = unions [trueRange, falseRange]
        where
          xDescList = toDescList xs
          xMax = head xDescList
          xMin = last xDescList
          yDescList = toDescList ys
          yMax = head xDescList
          yMin = last xDescList

    lessUCC (xs, xb) (ys, yb)
      | (xs, xb) `isLt` (ys, yb) = trueRange
      | (ys, yb) `isLt` (xs, xb) = falseRange
      | otherwise = unions [trueRange, falseRange]

    lessEq (r1, True) (r2, True) = lessEqCC r1 r2
    lessEq r1 r2 = lessUCC r1 r2 
    lessEqCC xs ys
      | xMin >! yMax = singleton (Finite 0 <=..<= Finite 0)
      | xMax <=! yMin = singleton (Finite 1 <=..<= Finite 1)
      | otherwise = fromList [Finite 0 <=..<= Finite 0, Finite 1 <=..<= Finite 1]
        where
          xDescList = toDescList xs
          xMax = head xDescList
          xMin = last xDescList
          yDescList = toDescList ys
          yMax = head xDescList
          yMin = last xDescList

    gt r1 r2 = 
      let lsEq = lessEq r1 r2 in
      if lsEq == trueRange then falseRange
      else if lsEq == falseRange then trueRange
      else unions [trueRange, falseRange]
      
    gtEq r1 r2 =
      let ls = less r1 r2 in
      if ls == trueRange then falseRange
      else if ls == falseRange then trueRange
      else unions [trueRange, falseRange]

    eq r1 r2 =
      if gt r1 r2 == trueRange || less r1 r2 == trueRange then falseRange
      else case (r1, r2) of
        ((i1, True), (i2, True)) -> let i1s = toList i1 in let i2s = toList i2 in 
          if i1 == i2 && length i1s == 1 && isSingleton (head i1s) 
            then trueRange else unions [trueRange, falseRange]
        _ -> unions [trueRange, falseRange]
  
    notEq r1 r2 = 
      if eq r1 r2 == trueRange then falseRange else trueRange

    neg xs = interval (-ub,ubt) (-lb,lbt)
      where
        (lb, lbt) = lowerBound' xs
        (ub, ubt) = upperBound' xs
    inv x =
      if 0 `Interval.member` x then Interval.whole
      else interval (if ub/=0 then 1/ub else NegInf, ubt)
            (if lb/=0 then 1/lb else PosInf, lbt)
        where
          (lb, lbt) = lowerBound' x
          (ub, ubt) = upperBound' x
    floor xs = unions (map toIntervalSet (toList xs))
    toIntervalSet x =
      if lb /= NegInf && ub /= PosInf then
            fromList
              $ map
                  (IntInterval.toInterval . IntInterval.singleton)
                  [(fromFinite lb) .. (fromFinite ub)]
      else
            singleton $ IntInterval.toInterval x'
      where
        x' = IntInterval.fromIntervalUnder x
        lb = IntInterval.lowerBound x' +
            let (lb', lbt') = lowerBound' x in
              if checkInt lb' && lbt' == Closed then (-1) else 0
        ub = IntInterval.upperBound x'
        fromFinite (Finite n) = n
        checkInt (Finite n) = isInt 10 n
        checkInt _ = False
    expRange x
      = interval (expER lb, lbt) (expER ub ,ubt)
      where
          (lb, lbt) = lowerBound' x
          (ub, ubt) = upperBound' x
          expER (Finite n) = Finite (exp n)
          expER PosInf = PosInf
          expER NegInf = Finite 0
    logRange x
      = if (lb < Finite 0) || (lb == Finite 0 && lbt == Closed) then
            error "log x is undefined when x <= 0"
        else
            interval (logER lb, lbt) (logER ub, ubt)
      where
          (lb, lbt) = lowerBound' x
          (ub, ubt) = upperBound' x
          logER (Finite 0) = NegInf
          logER PosInf = PosInf
          logER (Finite n) = Finite (log n)
    triRange id x =
          do
            cwd <- getCurrentDirectory
            Py.initialize
            pythonpath <- Py.getPath
            T.putStrLn ("Python path at startup is: " <> pythonpath <> "\n")
            let updatedPytonpath = pythonpath <> ":/home/dhz/.local/lib/python3.6/site-packages:/usr/local/lib/python3.6/dist-packages:/usr/lib/python3/dist-packages:./src"
            T.putStrLn ("Setting Python path to: " <> updatedPytonpath <> "\n")
            Py.setPath updatedPytonpath
            let calRanges = call "functionRange" "calRange"
            res <- calRanges
                    [arg (T.pack $ toUpper (head id) : tail id),
                    arg (mapER lb),
                    arg (T.pack $ show lbt),
                    arg (mapER ub),
                    arg (T.pack $ show ubt) ] []
            let (lb, lbt) = getLb (fst res)
            let (ub, ubt) = getUb (snd res)
            Py.finalize
            return $ interval (lb, lbt) (ub, ubt)
          where
            (lb, lbt) = lowerBound' x
            (ub, ubt) = upperBound' x
            mapER (Finite n) = Just n
            mapER _ = Nothing
            getLb Nothing = (NegInf, Open)
            getLb (Just (lb, lbt)) = (Finite lb, read $ T.unpack lbt)
            getUb Nothing = (PosInf, Open)
            getUb (Just (ub, ubt)) = (Finite ub, read $ T.unpack ubt)

imageDist :: Environment Dist -> Dist -> M Type
imageDist env (Return e) = range env e
imageDist env (Let (Rand x d1) d2) = imageDist (define env x d1) d2
imageDist env (Score e d) = imageDist env d -- unable to calculate, for safety, return the upperbound
imageDist env (PrimD _ id es) =
    do
      rs <- mapM (range env) es
      imagePrim id rs


imagePrim :: Ident -> [Type] -> M Type
imagePrim "Normal" rs =
  if length rs /= 2 then error "Normal distribution can only have two parameters."
  else
    let variance = getRange $ last rs in let mean = head rs in
      if
        (do v <- getC variance; return $ v `isSubsetOf` singleton (Finite 0 <=..<= Finite 0)) == Just True
      then return mean else return (T (UC Intervals.whole))

imagePrim "Uniform" rs
  | length rs /= 2 = error "Unifrom distribution can only have two parameters."
  | ifIntersect x y = error "arguments of uniform distribution cannot overlap"
  | otherwise =
      let cr  = do
                rx <- getC x
                ry <- getC y
                let is = intersections [rx,ry]
                if not $ Intervals.null is then return (C is)
                else Nothing
      in let uc = lift2BothtoUC (\x y -> singleton (Intervals.span (x `union` y))) x y in
        case cr of
          Just c -> return $ T (combineCUC c uc)
          Nothing -> return $ T uc
  where
      ifIntersect r1 r2
        = not (checkSingOrNull $ lift2BothtoC Intervals.intersection r1 r2)
      checkSingOrNull (C r) = let rs = toList r in (length rs == 1 && isSingleton (head rs)) || Intervals.null r
      x = getRange $ head rs
      y = getRange $ last rs

imagePrim "Roll" rs =
  if length rs /= 1 then error "Roll distribution can only have one parameter"
  else
    case x of
      C r ->
        let ub = upperBound $ head (toDescList r)
        in case ub of
          PosInf -> return $ T (C Intervals.whole)
          Finite n ->
            if isInt 10 n then
              return $ T (C (fromList (map (IntInterval.toInterval.IntInterval.singleton) [1..floor n])))
            else intErr
      _ -> intErr
  where
    intErr = error "argument of Roll must be an integer"
    x = getRange $ head rs

imagePrim "WRoll" rs =
  let xs = map (getRange.fstType) rs in
  let unionRange = lift2CCtoC Intervals.union in
  let res = foldr1 unionRange xs in return (T res)

range :: Environment Dist -> Expr -> M Type
range env (Pair p) =
  do
    x <- range env (fst p)
    y <- range env (snd p)
    return (P x y)
range _ (Number n) = return $ T (C (singleton $ Finite n <=..<= Finite n))
range env (If _ e1 e2) =
  do
    t1 <- range env e1
    t2 <- range env e2
    return $ unionType t1 t2
  -- this is a upperbound estimate, can be calculate more accurate by using the lattices library.
range env (Apply (Variable n) es) =
  do
    rs <- mapM (range env) es
    imageFunc n rs

range env (Variable x) = let d = find env x in imageDist env d
range env Loop {} = return $ T (UC Intervals.whole) --unable to calculate, for safety, return the upperbound

-- Nothing means not NN, can result in the type of high demension, everything demensition can be only Count or only UnCount, or both Count and UCount
nn :: Environment Dist -> Expr -> M (Maybe Type)
nn env (Variable x) =
  do
    r <- imageDist env (find env x)
    return (Just r)

nn env (Number n) = return $ Just (T (C (singleton $ Finite n <=..<= Finite n)))

nn env (If e1 e2 e3) =
  do
    t <- range env e1
    if t == T (C $ singleton (Finite 0 <=..<= Finite 0)) then nn env e3
    else if t == T (C $ singleton (Finite 1 <=..<= Finite 1)) then nn env e2
    else do
      mt1 <- nn env e2
      mt2 <- nn env e3
      let res = do
           t1 <- mt1
           t2 <- mt2
           if checkType t1 t2 then return (unionType t1 t2) else Nothing
      return res

nn env (Apply (Variable "+") xs)
  | null $ freeVars (head xs) = nn env (last xs)
  | null $ freeVars (last xs) = nn env (head xs)
  | otherwise = nn env (Pair (head xs, last xs))

nn  _ _ = return Nothing

ac :: Dist -> Type -> M Bool
ac d t =
  do
    mt <- ac' empty_env d
    return (Just True == do
      t' <- mt
      return $ checkType t' t)

ac' :: Environment Dist -> Dist -> M (Maybe Type)
ac' env d@(PrimD t _ _)=
  do rs <- imageDist env d
     return (Just rs)
ac' env (Return e) =  nn env e
ac' env (Score e d) = ac' env d
ac' env (Let (Rand x d1) d2) =
  do
    _ <- ac' env d1
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


main = dialog parser obey init_env