module Helpers where
import Syntax
import Environment
import Data.Interval
import Data.IntervalSet
import Data.Maybe
import qualified Data.List as List
import Text.Read(readMaybe)



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
substitute env (Inverse e1 e2) = Inverse (substitute env e1) e2
substitute env (Diff e1 e2) = Diff (substitute env e1) e2
substitute env (Integrate e1 e2) = Integrate (substitute env e1) e2
substitute env (IntegrateBound e1 e2 me3 me4) = IntegrateBound (substitute env e1) e2 me3 me4
substitute env (Func e1@(Variable x) e2) = Func e1 (substitute (define env x (Variable x)) e2)
substitute env e = e

newIdent :: Environment a -> Ident
newIdent env = head $ filter (\x -> x `notElem` names env) allStrings
  where
    allStrings = [c:s | s <- "":allStrings, c <- ['a'..'z'] <> ['0'..'9']]



isConst :: Environment Dist -> Expr -> Bool
isConst _ (Number n) = True
isConst env (Variable a) =
  case find env a of
    Const _ -> True
    _ -> False
isConst _ _ = False

splitBy :: (Foldable t, Eq a) => a -> t a -> [[a]]
splitBy delimiter = foldr f [[]]
            where f c l@(x:xs) | c == delimiter = []:l
                             | otherwise = (c:x):xs

unCountConst :: Environment Dist -> Expr -> Bool
unCountConst env (Variable e) =
  case find env e of
    Const d -> not $ isCountType d
    _  -> False
unCountConst _ _ = False

intersect :: Eq a => [a] -> [a] -> [a]
intersect [] _ = []
intersect (x:xs) l | x `elem` l = x : intersect xs l
                   | otherwise = intersect xs l

removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates = foldl (\seen x -> if x `elem` seen then seen
                                      else seen ++ [x]) []
freeVars :: Expr -> [Ident]
freeVars e = removeDuplicates $ freeVars' e

freeVars' :: Expr -> [Ident]
freeVars' (Variable x) =
  [x | x /= "true" || x /= " false"]
freeVars' (If e1 e2 e3) = freeVars' e1 <> freeVars' e2 <> freeVars' e3
freeVars' (Apply f es) = concatMap freeVars' es
freeVars' (Pair (x, y)) = freeVars' x <> freeVars' y
freeVars' (Loop bs1 e1 e2 bs2) =
  concatMap freeVars' es1 <> filerLocal (freeVars' e1 <> freeVars' e2 <> concatMap freeVars' es2)
  where
    (xs1, es1) = unzip bs1
    (xs2, es2) = unzip bs2
    filerLocal = filter (`notElem` xs1)
freeVars' _ = []

isSingleValue :: Type -> Bool
isSingleValue (T (C r)) = let r' = toList r in length r' == 1 && isSingleton (head r')
isSingleValue (P t1 t2) = isSingleValue t1 && isSingleValue t2
isSingleValue _ = False

functionNameMap :: [(String,String)]
functionNameMap =  [("sin", "Sin"), ("cos", "Cos"), ("tan", "Tan"), ("exp", "Exp"), ("log", "Log"), ("+", "Plus"),
                ("-", "Subtract"), ("*", "Times"), ("~", "Minus"), ("inv", "Inv"), ("power", "Power")]

functions1 :: [[Char]]
functions1 = ["Sin", "Cos", "Tan", "Exp", "Log", "Minus", "Inv"]

functions2 :: [[Char]]
functions2 = ["Plus", "Subtract", "Times"]

reverseFunctionMap :: [(String,String)]
reverseFunctionMap = [(b,a) | (a,b) <- functionNameMap]
--Returns if x is an int to n decimal places
isInt :: (Integral a, RealFrac b) => a -> b -> Bool
isInt n x = round (10^fromIntegral n*(x-fromIntegral (round x)))==0


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
checkType _ _ = False

mapType :: (Range -> Range) -> Type -> Type
mapType f (T r) = T (f r)
mapType f (P r1 r2) = P (mapType f r1) (mapType f r2)

isCountType :: Type -> Bool
isCountType (T (C r)) = True
isCountType (P r1 r2) = isCountType r1 && isCountType r2
isCountType _ = False

unionType :: Type -> Type -> Type
unionType = lift2Type (lift2CCtoC Data.IntervalSet.union)

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


intervalToTuple :: Interval a -> (Maybe a, String, Maybe a, String)
intervalToTuple interval =
      (mapER lb,  show lbt, mapER ub, show ubt)
      where
        (lb, lbt) = lowerBound' interval
        (ub, ubt) = upperBound' interval

justLookupFunctionName :: String -> String
justLookupFunctionName id = fromJust $ lookup id functionNameMap

transformExpToPN :: Expr -> [String]
transformExpToPN (Apply (Variable id) es) =
  justLookupFunctionName id:concatMap transformExpToPN es
transformExpToPN (Number n) = [show n]
transformExpToPN (Variable id) = [id]
transformExpToPN (Diff e1 e2) = "D":transformExpToPN e1 ++ transformExpToPN e2
transformExpToPN (Inverse e1 e2) = "Inverse":transformExpToPN e1 ++ transformExpToPN e2
transformExpToPN (Integrate e1 e2) = "Integrate":transformExpToPN e1 ++ transformExpToPN e2
transformExpToPN (IntegrateBound e1 e2 me3 me4) =
  "IntegrateBound":transformExpToPN e1 ++ transformExpToPN e2 ++ maybe ["-Infinity"] transformExpToPN me3
  ++ maybe ["Infinity"] transformExpToPN me4

transformExpToPN (Func e1 e2) = "Function":transformExpToPN e1 ++ transformExpToPN e2
transformExpToPN (Apply f@(Func e1 e2) [e3]) = "Apply":transformExpToPN f ++ transformExpToPN e3

diffFunction :: Expr -> Bool
diffFunction (Number _) = True
diffFunction (Variable _) = True
diffFunction (Apply (Variable id) es)
  | id `elem` ["+", "-", "*", "~", "inv", "sin", "cos", "tan", "exp", "log"] =
    all diffFunction es
  | otherwise = False
diffFunction _ = False

boundTostr :: Show a => Maybe a -> String
boundTostr = maybe "Nothing" show

vsToListStr :: Show a => [(Ident, [(Maybe a, String, Maybe a, String)])] -> [String]
vsToListStr xs = List.intercalate ["\"##\""] $ map vsTostr xs
    where vsTostr (v, xs) = v:concatMap (\(a,b,c,d) -> [boundTostr a, show b, boundTostr c, show d]) xs


readInfixExpr :: [String] -> Expr
readInfixExpr xs = case readInfixExpr' xs of
  (e, []) -> e
  (e, xs) -> error ("read " <> show e <> ", but " <> show xs <> " left.")

readInfixExpr' :: [String] -> (Expr, [String])
readInfixExpr' (x:xs) =
  case lookup x reverseFunctionMap of
    Just f ->
      let (e1, ys) = readInfixExpr' xs in
        if x `elem` functions1 then (Apply (Variable f) [e1], ys)
      else
        let (e2, zs) = readInfixExpr' ys in
         (Apply (Variable f) [e1,e2], zs)
    Nothing ->
      case readMaybe x :: Maybe Double of
        Just n -> (Number n, xs)
        Nothing  -> (Variable x, xs)
