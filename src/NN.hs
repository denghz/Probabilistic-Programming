{-# LANGUAGE OverloadedStrings #-}

module NN where
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
import qualified CPython.Types.Tuple as Py
import qualified CPython.Types.Integer as Py
import Data.Typeable
import CPython.Simple.Instances
import Data.Char(toUpper)
import qualified Data.IntervalSet as Intervals(intersection, null, member, whole, span, union)
import Data.IntervalSet
    ( fromList,
      intersections,
      isSubsetOf,
      singleton,
      toDescList,
      toList,
      union,
      unions,
      IntervalSet,
      Extended(..) )
import qualified Data.IntegerInterval as IntInterval
import Data.Interval hiding(null, singleton, intersections, member, isSubsetOf)
import qualified Data.Interval as Interval(member, whole)
import Environment
import Control.Monad(liftM, ap)
import Data.Maybe(isJust, fromJust, catMaybes)
import Syntax
import Continuation


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

functionNameMap :: [(String,Text)]
functionNameMap =  [("sin", "Sin"), ("cos", "Cos"), ("tan", "Tan"), ("exp", "Exp"), ("log", "Log"), ("+", "Plus"),
                ("-", "Subtract"), ("*", "Times"), ("~", "Minus"), ("inv", "Inv")]
--Returns if x is an int to n decimal places
isInt :: (Integral a, RealFrac b) => a -> b -> Bool
isInt n x = round (10^fromIntegral n*(x-fromIntegral (round x)))==0
instance (ToPy a, ToPy b) => ToPy (a,b) where
  toPy (a,b)=
    do
      a' <- toPy a
      b' <- toPy b
      t <- Py.toTuple [a',b']
      return $ Py.toObject t

instance (ToPy a, ToPy b, ToPy c) => ToPy (a,b,c) where
  toPy (a,b,c)=
    do
      a' <- toPy a
      b' <- toPy b
      c' <- toPy c
      t <- Py.toTuple [a',b', c']
      return $ Py.toObject t

instance (ToPy a, ToPy b, ToPy c, ToPy d) => ToPy (a,b,c,d) where
  toPy (a,b,c,d)=
    do
      a' <- toPy a
      b' <- toPy b
      c' <- toPy c
      d' <- toPy d
      t <- Py.toTuple [a',b', c', d']
      return $ Py.toObject t
instance FromPy Bool where
  fromPy b =
    do
      b' <- easyFromPy Py.fromInteger Proxy b
      if b' == 0 then return False
      else if b' == 1 then return True
      else error "return value from python is not an integer"

mapER :: Extended a -> Maybe a
mapER (Finite n) = Just n
mapER _ = Nothing


  -- either count or uncount or both are possible
  -- Boundary of C set is in the set
isUC :: Range -> Bool
isUC (UC _ ) = True
isUC _ = False

getUC :: Range -> IntervalSet Double
getUC (UC r) = r

rangeBtoUC :: Range -> Range
rangeBtoUC (B r1 r2) = UC r2
rangeBtoUC r = r

getC :: Range -> Maybe (IntervalSet Double)
getC (C r) = Just r
getC (UC r) = Nothing
getC (B r1 r2) = Just r1

rangeToList :: Range -> [(IntervalSet Double, Bool)]
rangeToList (C r) = [(r, True)]
rangeToList (UC r) = [(r, False)]
rangeToList (B r1 r2) = [(r1, True), (r2, False)]

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



checkType :: Type -> Type -> Bool
checkType (P t1 t2) (P t3 t4) = checkType t1 t3 && checkType t2 t4
checkType (T r1) (T r2) = checkRange r1 r2
  where
    checkRange (C _) (C _) = True
    checkRange (UC _) (UC _) = True
    checkRange _ _ = False

mapType :: (Range -> Range) -> Type -> Type
mapType f (T r) = T (f r)
mapType f (P r1 r2) = P (mapType f r1) (mapType f r2)

isCountType :: Type -> Bool
isCountType (T (C r)) = True
isCountType (P r1 r2) = isCountType r1 && isCountType r2
isCountType _ = False

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
-- Extended Real is a ring not a field
map1Ints :: (Interval Double -> Interval Double) -> IntervalSet Double -> IntervalSet Double
map1Ints f xs = fromList [f x | x <- toList xs]

map2Ints :: (Interval Double -> Interval Double -> Interval Double) -> IntervalSet Double -> IntervalSet Double -> IntervalSet Double
map2Ints f xs ys = fromList [f x y | x <- toList xs, y <- toList ys]


intervalToTuple :: Interval a -> (Maybe a, Text, Maybe a, Text)
intervalToTuple interval =
      (mapER lb, T.pack (show lbt), mapER ub, T.pack (show ubt))
      where
        (lb, lbt) = lowerBound' interval
        (ub, ubt) = upperBound' interval

justLookupFunctionName :: String -> Text
justLookupFunctionName id = fromJust $ lookup id functionNameMap

transfromExpPN :: Expr -> [Text]
transfromExpPN (Apply (Variable id) es) =
  justLookupFunctionName id:concatMap transfromExpPN es
transfromExpPN (Number n) = [T.pack $ show n]
transfromExpPN (Variable id) = [T.pack id]

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
      = if lb < Finite 0 || lb == Finite 0 && lbt == Closed then
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
      checkSingOrNull (C r) = let rs = toList r in length rs == 1 && isSingleton (head rs) || Intervals.null r
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


imageExpr :: Environment Dist -> Expr -> M Type
imageExpr env (Apply (Variable id) es) = 
  do
    ts <- mapM (imageExpr env) es
    imageFunc id ts
imageExpr env (Variable x) = imageDist env (find env x)
imageExpr env (Number n) = return (T (C (singleton $ Finite n <=..<= Finite n)))


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

diffFunction :: Expr -> Bool
diffFunction (Number _) = True
diffFunction (Variable _) = True
diffFunction (Apply (Variable id) es)
  | id `elem` ["+", "-", "*", "~", "inv", "sin", "cos", "tan", "exp", "log"] =
    all diffFunction es
  | otherwise = False
diffFunction _ = False

nnDiff :: Environment Dist -> Expr -> M (Maybe Type)
nnDiff env e =
  if not $ diffFunction e then return Nothing
  else do
    let vars = freeVars e
    xs <- mapM (fmap (getRange . fromJust) . nn env . Variable) vars
    if not (all isUC xs) then return Nothing
    else 
      let xs' = map (toList.getUC) xs in
      let vs = zip (map T.pack vars) $ map (map intervalToTuple) xs' in 
      do
        t <- imageExpr env e
        Mk (\k -> 
          do
            b <- diffCheck (transfromExpPN e) vs
            if b then k (Just t)
            else k Nothing
          )
  where
    diffCheck e vs = 
      do 
        Py.initialize
        pythonpath <- Py.getPath
        T.putStrLn ("Python path at startup is: " <> pythonpath <> "\n")
        -- Appending so that the user's PYTHONPATH variable (ready by python) can go first.
        let updatedPytonpath = pythonpath <> ":/usr/lib/python2.7/dist-packages:/home/dhz/.local/lib/python3.6/site-packages:/usr/local/lib/python3.6/dist-packages:/usr/lib/python3/dist-packages:./src"
        T.putStrLn ("Setting Python path to: " <> updatedPytonpath <> "\n")
        Py.setPath updatedPytonpath

        let nnDiff = call "nnDiff" "nnDiff"

        res <- nnDiff [arg e, arg vs] []
        Py.finalize
        return (res :: Bool)

nnFix :: Environment Dist -> Expr -> M (Maybe Type)
nnFix env p@(Pair (p1,p2)) = 
  let eList = map transfromExpPN $ flatPair p in
  let vars = freeVars p in 
  do
    xs <- mapM (fmap (getRange . fromJust) . nn env . Variable) vars
    if not (all isUC xs) then return Nothing
    else 
      let xs' = map (toList.getUC) xs in
      let vs = zip (map T.pack vars) $ map (map intervalToTuple) xs' in 
      do
        t <- imageExpr env p
        Mk (\k -> 
          do
            b <- fixCheck eList vs
            if b then k (Just t)
            else k Nothing
          )
  

  where
    flatPair (Pair (p1,p2)) = flatPair p1 <> flatPair p2
    flatPair e = [e]
    fixCheck e vs = 
      do 
        Py.initialize
        pythonpath <- Py.getPath
        T.putStrLn ("Python path at startup is: " <> pythonpath <> "\n")
        -- Appending so that the user's PYTHONPATH variable (ready by python) can go first.
        let updatedPytonpath = pythonpath <> ":/usr/lib/python2.7/dist-packages:/home/dhz/.local/lib/python3.6/site-packages:/usr/local/lib/python3.6/dist-packages:/usr/lib/python3/dist-packages:./src"
        T.putStrLn ("Setting Python path to: " <> updatedPytonpath <> "\n")
        Py.setPath updatedPytonpath

        let nnFix = call "nnFix" "nnFix"

        res <- nnFix [arg e, arg vs] []
        Py.finalize
        return (res :: Bool)
       
      
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

nn env e@(Apply (Variable "+") xs) =
  if length xs /= 2 then error "+ takes two arguments"
    else
  do
    t <- nnDiff env e
    if isJust t then return t
    else do
      ts <- nn env (Pair (head xs, last xs))
      let ts' = do
            t <- ts
            let t1 = fstType t
            let t2 = sndType t
            return [t1, t2]
      mapM (imageFunc "+") ts'

nn env e@(Apply (Variable "*") xs) =
  if length xs /= 2 then error "* takes two arguments"
    else
  do
    t <- nnDiff env e
    if isJust t then return t
    else do
      ts <- nn env (Pair (head xs, last xs))
      t1 <- nn env (head xs)
      t2 <- nn env (last xs)
      let ts' =
            if isJust ts then
              do
                t <- ts
                let t1 = fstType t
                let t2 = sndType t
                return [t1, t2]
            else
              do
                t1' <- t1
                t2' <- t2
                if not (memberType 0 t1' && memberType 0 t2')
                  then return [t1', t2']
                else Nothing
      mapM (imageFunc "*") ts'
  where
    memberType n t =
      let t' = getRange t in
       all (Intervals.member n . fst) (rangeToList t')

nn env e@(Apply (Variable id) xs)
  | id `elem` ["~", "inv", "log", "exp", "sin", "cos", "tan", "fst", "snd"] =
    if length xs /= 1 then error $ id <> " takes two arguments"
    else
      do
        t <- nnDiff env e
        if isJust t then return t
        else do
          t <- nn env (head xs)
          let t' = fmap (:[]) t
          mapM (imageFunc id) t'
  | otherwise = error $ id <> " not implemeneted"

nn env p@(Pair (x,y)) =
  do
    t <- nnFix env p
    if isJust t then return t
    else do
      xt <- nn env x
      yt <- nn env y
      xtUC <- nnUC env x
      ytUC <- nnUC env y
      let intersectVars = filter (`elem` freeVars x) (freeVars y)
      intersT <- mapM (nn env . Variable) intersectVars
      let t =
            do
              xt' <- xt
              yt' <- yt
              if (null intersectVars || all isCountType (catMaybes intersT)) && checkType xt' yt'
                then return $ P xt' yt'
              else if all isJust [xtUC, ytUC] then
                return $ P (fromJust xtUC) (fromJust ytUC)
              else Nothing
      return t

nn env Loop {} = return Nothing

nnUC :: Environment Dist -> Expr -> M (Maybe Type)
nnUC env (Variable x) =
  do
    r <- imageDist env (find env x)
    return $ Just (mapType rangeBtoUC r)
nnUC env (Number n) = nn env (Number n)
nnUC env (If e1 e2 e3) =
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
           let t1' = mapType rangeBtoUC t1
           let t2' = mapType rangeBtoUC t2
           if checkType t1' t2' then return (unionType t1' t2') else Nothing
      return res

nnUC env e@(Apply (Variable "+") xs) =
  if length xs /= 2 then error "+ takes two arguments"
    else
  do
    t <- nnDiff env e
    if isJust t then return t
    else do
      ts <- nnUC env (Pair (head xs, last xs))
      let ts' = do
            t <- ts
            let t1 = fstType t
            let t2 = sndType t
            return [t1, t2]
      mapM (imageFunc "+") ts'

nnUC env e@(Apply (Variable "*") xs) =
  if length xs /= 2 then error "* takes two arguments"
    else
  do
    t <- nnDiff env e
    if isJust t then return t
    else do
      t1 <- nnUC env (head xs)
      t2 <- nnUC env (last xs)
      let ts = catMaybes [t1, t2]
      t <- imageFunc "*" ts
      return (Just t)


nnUC env e@(Apply (Variable id) xs)
  | id `elem` ["~", "inv", "log", "exp", "sin", "cos", "tan", "fst", "snd"] =
    if length xs /= 1 then error $ id <> " takes two arguments"
    else
      do
        t <- nnDiff env e
        if isJust t then return t
        else do
          t <- nnUC env (head xs)
          let t' = fmap (:[]) t
          mapM (imageFunc id) t'
  | otherwise = error $ id <> " not implemeneted"

nnUC env (Pair (x,y)) = nn env (Pair (x,y))

nnUC env Loop {} = return Nothing