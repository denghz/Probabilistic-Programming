{-# LANGUAGE OverloadedStrings #-}

module NN where

import System.IO
    ( stdout, stderr, hPutStrLn, Newline(CRLF), hPutStr, hClose )
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
import Log
import System.Process.Typed ( readProcessStderr_, shell )
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Lazy.Char8 as L8
import Control.Exception (throwIO)
import qualified Data.List as List
import Helpers

import PrintBTree

-- All builtin function should be considered

imageFunc :: Ident -> [Type] -> M Type
imageFunc id args
  | id `elem` ["+", "-", "*", "<", "<=", ">", ">=", "=", "<>"] =
      let x = head args in let y = last args in
      let rx = getRange x in let ry = getRange y in
      if length args /= 2 then  error $ "only 2 arguement allowed for " <> id
      else if id `elem` ["+", "-", "*"] then return (T (lift2CCtoC (binop id) rx ry))
      else return (T $ C (unions [comp id x y | x <- rangeToList rx, y <- rangeToList ry ])) -- id `elem` ["<", "<=", ">", ">=", "=", "<>"]
  | id `elem` ["~", "inv", "fst", "snd", "floor", "sin", "cos", "tan", "exp", "log"] =
      let x = head args in
      if length args /= 1 then error $ "only 1 arguement allowed for " <> id
      else
        case id of
          "fst" ->  return $ fstType x
          "snd" -> return $ sndType x
          id -> let rx = getRange x in
            if id `elem` ["sin", "cos", "tan"] then
              let id' = fromJust $ lookup id functionNameMap in
              Mk (\k ->
                (do
                r <- liftMId (mapMIntervalSet (triRange id')) rx
                k (T r)))
            else if id == "floor" then return $ T (liftUCtoC (minop id) rx)
            else return $ T ( liftId (minop id) rx)
  where
    mapMIntervalSet f xs =
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
              if checkInt lb' && lbt' == Open then (-1) else 0
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
            let (lb, lbt, ub, ubt) = intervalToTuple $! x
            let args = unwords [id, boundTostr lb, show lbt, boundTostr ub, show ubt]
            res <- readProcessStderr_ (shell ("python3 " <> "/home/dhz/probprog/src/functionRange.py " <> args))
            let resWords = splitBy ',' $ L8.unpack res
            let lb' = maybe NegInf Finite $ read (head resWords)
            let lbt' = read (resWords !! 1)
            let ub' = maybe PosInf Finite $ read (resWords !! 2)
            let ubt' = read (resWords !! 3)
            return (interval (lb',lbt') (ub',ubt'))

imageDist :: Environment Dist -> Dist -> M Type
imageDist env (Return e) = range env e
imageDist env (Let (Rand x d1) d2) = imageDist (define env x d1) d2
imageDist env (Score e d) = imageDist env d -- unable to calculate, for safety, return the upperbound
imageDist env (PrimD _ id es) = imagePrim env id es
imageDist env (Const t) =
    return $ mapType (liftUCtoC id) t

imagePrim :: Environment Dist -> Ident -> [Expr] -> M Type
imagePrim env "Normal" es =
  if length es /= 2 then error "Normal distribution can only have two parameters."
  else
    do
      rs <- mapM (range env) es
      let variance = getRange $ last rs in let mean = head rs in
        if (do v <- getC variance; return $ v `isSubsetOf` singleton (Finite 0 <=..<= Finite 0)) == Just True
        then return mean
        else if (do v <- getC variance; return $ 0 `Intervals.member` v) == Just True then return $ unionType mean (T (UC Intervals.whole))
        else return (T (UC Intervals.whole))

imagePrim env "Uniform" es
  | length es /= 2 = error (show (length es) <> "Unifrom distribution can only have two parameters.")
  | otherwise =
      do
        rs <- mapM (range env) es
        diffr <- mapM (range env . Variable) diff
        let nodiff = all isSingleValue diffr
        let xr = head rs
        let yr = last rs
        let xRange = getRange xr
        let yRange = getRange yr
        if xr == yr && nodiff || x == y then
          return $ mapType (liftUCtoC id) xr
        else if ifIntersect xRange yRange then error "arguments of uniform distribution cannot overlap"
        else do
          let cr = (do
                      rx <- getC xRange
                      ry <- getC yRange
                      let is = intersections [rx,ry]
                      if not $ Intervals.null is && not (any (unCountConst env) es) then return (C is)
                      else Nothing)
          let uc = lift2BothtoUC (\x y -> singleton (Intervals.span (x `union` y))) xRange yRange
          case cr of
            Just c -> return $ T (combineCUC c uc)
            Nothing -> return $ T uc
  where
      ifIntersect r1 r2
        = not (checkSingOrNull $ lift2BothtoC Intervals.intersection r1 r2)
      checkSingOrNull (C r) = let rs = toList r in length rs == 1 && isSingleton (head rs) || Intervals.null r
      x = head es
      y = last es
      xvars = freeVars x
      yvars = freeVars y
      inter = xvars `intersect` yvars
      diff = filter (`notElem` inter) (xvars <> yvars)

imagePrim env "Roll" es =
  if length es /= 1 then error "Roll distribution can only have one parameter"
  else
    do
      x' <- range env e
      let x = getRange x'
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
    e = head es

imagePrim env "WRoll" es =
  do
    rs <- mapM (range env) es
    let xs = map (getRange.fstType) rs
    let unionRange = lift2CCtoC Intervals.union
    let res = foldr1 unionRange xs
    return (T res)

range :: Environment Dist -> Expr -> M Type
range env (Pair p) =
  do
    x <- range env (fst p)
    y <- range env (snd p)
    return (P x y)
range _ (Number n) = return $ T (C (singleton $ Finite n <=..<= Finite n))
range env (If e1 e2 e3) =
  do
    t <- range env e1
    if t == T (C $ singleton (Finite 0 <=..<= Finite 0)) then range env e3
    else if t == T (C $ singleton (Finite 1 <=..<= Finite 1)) then  range env e2
    else do
      t1 <- range env e1
      t2 <- range env e2
      return $ unionType t1 t2
  -- this is a upperbound estimate, can be calculate more accurate by using the lattices library.
range env (Apply (Variable n) es) =
  do
    ts <- mapM (range env) es
    imageFunc n ts

range env (Variable x) = let d = find env x in imageDist env d
range env Loop {} = return $ T (UC Intervals.whole) --unable to calculate, for safety, return the upperbound

nnDiff :: Environment Dist -> Expr -> M [Type]
nnDiff env e =
  if not $ diffFunction e then return []
  else do
    let vars = freeVars e
    xs <- mapM (range env . Variable) vars
    if any isPair xs || any isCountType xs then return []
    else
      let xs' = map (toList.getUC.getRange) xs in
      let vs = zip vars $ map (map intervalToTuple) xs' in
      do
        t <- range env e
        Mk (\k ->
          do
            b <- diffCheck (transformExpToPN e) vs
            putStrLn $ "nnDiff result of "  <> show e <> " is " <> show b
            if b then k [t]
            else k []
          )
  where
    diffCheck e vs =
      do
        let expStr = e
        let vsStr = vsToListStr vs
        let args = unwords $ expStr <> ["\"||\""] <> vsStr
        res <- readProcessStderr_ (shell ("python3 " <> "/home/dhz/probprog/src/nnDiff.py " <> args))
        return (read (L8.unpack res))

nnTuple :: Environment Dist -> Expr -> M [Type]
nnTuple env p@(Pair (p1,p2)) =
  let pList = flatPair p in
  let eList = map transformExpToPN pList in
  let vars = freeVars p in
  let allDiff = all diffFunction pList in
  let isSquare = length vars == length pList in
  do
    xs <- mapM (fmap getRange . range env . Variable) vars
    if not (all isUC xs) || not allDiff || not isSquare then
      log_ ("try NN-Tuple " <> show p <> " domains are not all uncount, or not differentiable, or map to a sub space") $ return []
    else
      let xs' = map (toList.getUC) xs in
      let vs = zip vars $ map (map intervalToTuple) xs' in
      do
        t <- range env p
        Mk (\k ->
          do
            b <- fixCheck eList vs
            putStrLn $ "nnTuple result of "  <> show p <> " is " <> show b
            if b then k [t]
            else k []
          )
  where
    flatPair (Pair (p1,p2)) = flatPair p1 <> flatPair p2
    flatPair e = [e]
    fixCheck e vs =
      do
        let expStr = List.intercalate ["\"##\""] e
        let vsStr = vsToListStr vs
        let args = unwords $ expStr <> ["\"||\""] <> vsStr
        res <- readProcessStderr_ (shell ("python3 " <> "/home/dhz/probprog/src/nnTuple.py " <> args))
        return (read (L8.unpack res))


failnn :: Expr -> M ([Type], Btree String)
failnn e = log_ (show e <> " is not nn'") $ return ([], leafNode "")


nn :: Environment Dist -> Expr -> M [Type]
nn env e = 
  do
    (t, tr) <- nn' env e
    Mk (\k ->
      if null t then k t
      else do
        printt tr
        print e
        k t)

-- Nothing means not NN, can result in the type of high demension, everything demensition can be only Count or only UnCount, or both Count and UCount
nn' :: Environment Dist -> Expr -> M ([Type], Btree String)
nn' env (Variable x) = log_ ("apply NN-VAR on " <> show x) $
  do
    r <- imageDist env (find env x)
    return ([r], leafNode ("NN-Var " <> show x))

nn' env (Number n) = log_ ("apply NN-Count on " <> show n)
  $ return ([T (C (singleton $ Finite n <=..<= Finite n))], leafNode ("NN-Count on " <> show n))

nn' env e@(If e1 e2 e3) =
  do
    t <- range env e1
    (mt1, tr1) <- nn' env e2
    (mt2, tr2) <- nn' env e3
    if t == T (C $ singleton (Finite 0 <=..<= Finite 0))
      then log_ ("apply NN-COND on " <> show e) $
      return (mt2, Node ("NN-Cond on " <> show e) tr2 Leaf)
    else if t == T (C $ singleton (Finite 1 <=..<= Finite 1))
      then log_ ("apply NN-COND on " <> show e) $
      return (mt1, Node ("NN-Cond on " <> show e) tr1 Leaf)
    else
      do
        let res = do
             t1 <- mt1
             t2 <- mt2
             if checkType t1 t2 then return (unionType t1 t2) else []
        if not (null res) then
          log_ ("apply NN-IF on " <> show e) $ return (res, Node ("NN-If on " <> show e) tr1 tr2)
        else failnn e

nn' env e@(Apply (Variable "+") xs) =
  if length xs /= 2 then error (show xs <> " + takes two arguments")
    else
  do
    let x = head xs
    let y = last xs
    (xt, trx) <- nn' env x
    (yt, try) <- nn' env y
    let ts = [[x,y] | x <- xt, y <- yt]
    resTs <- mapM (imageFunc "+") ts
    if (isConst env x && not (null yt)) || (isConst env y && not (null xt)) then
      log_ ("apply NN-Linear on " <> show e) $ return (resTs, Node ("NN-Linear on " <> show e) trx try)
    else
      do
        (ts, trp) <- nn' env (Pair (x, y))
        if not (null ts) then
            log_ ("apply NN-PLUS on " <> show e) $ return (resTs, Node ("NN-Plus on " <> show e) trp Leaf)
        else do
          t' <- nnDiff env e
          if not (null t') then
            log_ ("apply NN-Diff on " <> show e) $ return (t', Node ("NN-Diff on " <> show e) Leaf Leaf)
          else
            failnn e

nn' env e@(Apply (Variable "*") xs) =
  if length xs /= 2 then error "* takes two arguments"
    else
  do
    (t, tr) <- do
      (ts, trp) <- nn' env (Pair (head xs, last xs))
      (t1, trx) <- nn' env (head xs)
      (t2, try) <- nn' env (last xs)
      let ts' =
            if not (null ts) then
              do
                t <- ts
                let t1 = fstType t
                let t2 = sndType t
                return [t1, t2]
            else
              do
                t1' <- t1
                t2' <- t2
                if not (memberType 0 t1' && memberType 0 t2') || any (unCountConst env) xs
                  then return [t1', t2']
                else []
      let l | not (null ts) = ("apply NN-Mult on " <> show e, Node ("NN-Mult on " <> show e) trp Leaf)
            | not (null ts') = ("apply NN-Scale on " <> show e, Node ("NN-Scale on " <> show e) trx try)
            | otherwise = (show e <> " is not NN-Mult and NN-Scale", leafNode "")
      tRes <- mapM (imageFunc "*") ts'
      log_ (fst l) $ return (tRes, snd l)

    if not (null t) then return (t, tr)
    else
      do
        t' <- nnDiff env e
        if not (null t') then
          log_ ("apply NN-Diff on " <> show e) $ return (t', leafNode ("NN-Diff on " <> show e))
        else
          failnn e
  where
    memberType n t =
      let t' = getRange t in
       all (Intervals.member n . fst) (rangeToList t')

nn' env e@(Apply (Variable id) xs)
  | id `elem` ["~", "inv", "log", "exp", "sin", "cos", "tan", "fst", "snd"] =
    if length xs /= 1 then error $ id <> " takes two arguments"
    else
      do
        (t,tr) <- do
          (t, tr) <- nn' env (head xs)
          let t' = fmap (:[]) t
          resT <- mapM (imageFunc id) t'
          return (resT, tr)
        if not (null t) then
          if id `elem` ["fst", "snd"] then
            log_ ("apply NN-PROJ on " <> show e) $ return (t, Node ("NN-Proj on " <> show e) tr Leaf)
          else
            log_ ("apply NN-OP on " <> show e) $ return (t, Node ("NN-Op on " <> show e) tr Leaf)
        else do
          t' <- nnDiff env e
          if not (null t') then
           log_ ("apply NN-Diff on " <> show e) $ return (t', leafNode ("NN-Diff on " <> show e))
          else failnn e
  | otherwise = error $ id <> " not implemeneted"

nn' env p@(Pair (x,y)) =
  do
    (xt, trx) <- nn' env x
    (yt, try) <- nn' env y
    let intersectVars = filter (`elem` freeVars x) (freeVars y)
    intersT' <- mapM (range env . Variable) intersectVars
    let intersT = filter (not.isSingleValue) intersT'
    if not (any null [xt, yt]) && null intersT
      then log_ ("apply NN-Pair on " <> show p) $ return (P <$> xt <*> yt, Node ("NN-Pair on " <> show p) trx try)
    else
      do
        t <- nnTuple env p
        if not (null t) then return (t, leafNode ("NN-Tuple on " <> show p))
        else do
          let varsV = map (find env) intersectVars
          let newEnv = defargs env intersectVars (map Const intersT')
          (xt', trx') <- nn' newEnv x
          (yt', try') <- nn' newEnv y
          if not (all null [xt, yt]) then do
            let t1 = P <$> xt <*> yt'
            let t2 = P <$> xt' <*> yt
            log_ ("apply NN-Fix on " <> show p) $ return (t1 ++ t2, Node ("NN-Fix on " <> show p) trx' try')
          else failnn p
nn' env e@Loop {} = failnn e
