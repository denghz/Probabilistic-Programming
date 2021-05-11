module Parser(parser) where
import Parsing
import Syntax
import Data.Char
import Data.IntervalSet(whole)

data Token =
    IDENT IdKind Ident | NUMBER Double
  | IF | THEN | ELSE | LET  | LOOP | SCORE | RETURN | IN
  | LPAR | RPAR | COMMA | EQUAL | SEMI | MINUS
  | BRA | KET | LBRACE | RBRACE | TILDE | DO | GET | CT | UCT
  | BADTOK Char
  deriving Eq

data IdKind =
  ID | MONOP | CONSOP | MULOP | ADDOP | RELOP | D
  deriving (Eq, Show)

instance Show Token where
  show t =
    case t of
      IDENT _ x -> show x; NUMBER n -> show n;
      IF -> "if"; THEN -> "then"; ELSE -> "else";
      LET -> "let"; LOOP -> "loop"; GET -> "get"; DO -> "do"
      SCORE -> "score"; RETURN -> "return"; IN -> "in";
      LPAR -> "("; RPAR -> ")"; COMMA -> ","
      EQUAL -> "="; SEMI -> ";";  MINUS -> "-";
      BRA -> "["; KET -> "]"; LBRACE -> "{";
      RBRACE -> "}"; TILDE -> "~"; CT -> "Countable"; UCT -> "Uncountable"
      BADTOK c -> [c]

kwlookup :: String -> Token
kwlookup =
  make_kwlookup (IDENT ID)
    [("if", IF), ("then", THEN), ("else", ELSE), ("let", LET),
    ("in", IN), ("loop", LOOP), ("score", SCORE), ("do", DO),
    ("return", RETURN), ("get", GET),
    ("Roll", IDENT D "Roll"), ("WRoll", IDENT D "WRoll"),
    ("Uniform", IDENT D "Uniform"), ("Normal", IDENT D "Normal"), ("c", CT), ("uc", UCT)]

tokenToType :: Token -> Type
tokenToType CT = T (C whole)
tokenToType UCT = T (UC whole)
tokenToType t = error (show t <> " is not a Type")

lexer :: Lexer Token
lexer =
  do
    c <- nextch
    case c of
      _ | isAlpha c ->
        do
          s <- star (\c -> isAlphaNum c || c == '_')
          return (kwlookup (c:s))
      _ | isDigit c ->
        do s <- star isDigit; return (NUMBER (read (c:s)))
      '=' -> return EQUAL
      '+' -> return (IDENT ADDOP "+")
      '-' -> switch [('-', do scanComment; lexer)] (return MINUS)
      '*' -> return (IDENT MULOP "*")
      '!' -> return (IDENT MONOP "!")
      '~' -> return TILDE
      ',' -> return COMMA
      '<' -> switch [('=', return (IDENT RELOP "<=")),
                    ('>', return (IDENT RELOP "<>"))]
                    (return (IDENT RELOP "<"))
      '>' -> switch [('=', return (IDENT RELOP ">="))]
                     (return (IDENT RELOP ">"))
      '(' -> return LPAR
      ')' -> return RPAR
      '[' -> return BRA
      ']' -> return KET
      '{' -> return LBRACE
      '}' -> return RBRACE
      ';' -> return SEMI
      ' ' -> lexer
      '\t' -> lexer
      '\n' -> do incln; lexer
      _ -> return (BADTOK c)

scanComment :: Lexer ()
scanComment =
  do
    c <- nextch
    case c of
      '\n' -> incln
      _ -> scanComment

p_phrase :: Parser Token Phrase
p_phrase =
  do dt <- p_dist; eat SEMI; return $ Calculate dt
  <+> do e <- p_expr; eat SEMI; return $ Evaluate e
  <+> do d <- p_def; eat SEMI; return $ Define d

p_def :: Parser Token Defn
p_def =
  do x <- p_name; eat EQUAL; Prob x <$> p_dist'

p_bind :: Parser Token Bind
p_bind =
  do (x, e) <- p_eqn; return $ Val x e
  <+> do (x, d) <- p_rand; return $ Rand x d

p_rand :: Parser Token (Ident, Dist)
p_rand =
  do x <- p_name; eat TILDE; d <- p_dist'; return (x,d)


p_eqn :: Parser Token (Ident, Expr)
p_eqn =
  do x <- p_name; eat EQUAL; e <- p_expr; return (x, e)


p_formals :: Parser Token [Ident]
p_formals = p_lrpar $ p_list0 p_name COMMA

p_dist :: Parser Token (Dist, Type)
p_dist =
  do
    d <- p_dist'
    do eat IN
    t <- p_type
    return (d,t)
p_dist' :: Parser Token Dist
p_dist' = do eat LET; b <- p_bind; eat IN; Let b <$> p_dist'
          <+> do eat RETURN; Return <$> p_expr
          <+> do eat SCORE; e <- p_expr; eat IN;Score e <$> p_dist'
          <+> p_buildInDist

p_buildInDist :: Parser Token Dist
p_buildInDist =
  do
    d <- p_ident D
    case d of
      "Roll" -> do e <- p_lrpar p_expr; return (PrimD DZ "Roll" [e])
      "WRoll" -> do ps <- p_lrpar $ p_list0 p_pair COMMA;
                    return (PrimD DZ "WRoll" ps)
      "Uniform" -> PrimD DR "Uniform" . (\(Pair (x,y)) -> [x, y]) <$> p_pair
      "Normal" -> PrimD DR "Normal" . (\(Pair (x,y)) -> [x, y]) <$> p_pair
      _ -> p_fail

p_expr :: Parser Token Expr
p_expr =
  do eat IF; e1 <- p_expr; eat THEN; e2 <- p_expr;
      eat ELSE; If e1 e2 <$> p_expr
  <+> do eat LOOP; bs1 <- p_loopBinds; e1 <- p_expr; eat GET; -- "GET" res "DO" binds
          e2 <- p_expr; eat DO; Loop bs1 e1 e2 <$> p_loopBinds
  <+> p_term5

p_loopBinds :: Parser Token [(Ident, Expr)]
p_loopBinds = p_lrpar $ p_list0 p_bind COMMA
  where p_bind = p_lrpar $ do x <- p_name; eat COMMA; e <- p_expr; return (x,e)

p_term5 :: Parser Token Expr
p_term5 = p_opchainl p_relop p_term4
p_term4 :: Parser Token Expr
p_term4 = p_opchainl p_addop p_term3
p_term3 :: Parser Token Expr
p_term3 = p_opchainl p_mulop p_term2
p_term2 :: Parser Token Expr
p_term2 = p_opchainr (p_ident CONSOP) p_term1

p_relop :: Parser Token Ident
p_relop = p_ident RELOP <+> do eat EQUAL; return "="
p_addop :: Parser Token Ident
p_addop = p_ident ADDOP <+> do eat MINUS; return "-"
p_mulop :: Parser Token Ident
p_mulop = p_ident MULOP

p_opchainl :: Parser t Ident -> Parser t Expr -> Parser t Expr
p_opchainl p_op p_rand =
  do e0 <- p_rand; p_tail e0
  where
    p_tail e1 =
      do w <- p_op; e2 <- p_rand; p_tail (Apply (Variable w) [e1, e2])
      <+> return e1

p_opchainr :: Parser t Ident -> Parser t Expr -> Parser t Expr
p_opchainr =
  p_chainr mkop
  where mkop w e1 e2 = Apply (Variable w) [e1, e2]

p_chainr :: (a -> b -> b -> b) ->
    Parser t a -> Parser t b -> Parser t b
p_chainr mk p_op p_rand =
  do e1 <- p_rand; p_tail e1
  where
    p_tail e1 =
      do w <- p_op; e2 <- p_chainr mk p_op p_rand;
          return (mk w e1 e2)
      <+> return e1

p_term1 :: Parser Token Expr
p_term1 =
  do w <- p_monop; e <- p_term1; return (Apply (Variable w) [e])
  <+> p_term0

p_monop :: Parser Token Ident
p_monop = p_ident MONOP <+> do eat MINUS; return "~"

p_term0 :: Parser Token Expr
p_term0 =
  do e0 <- p_primary; p_qualifiers e0
  where
    p_qualifiers e1 =
      do aps <- p_actuals; p_qualifiers (Apply e1 aps)
      <+> return e1

p_actuals :: Parser Token [Expr]
p_actuals = p_lrpar $ p_list0 p_expr COMMA

p_primary :: Parser Token Expr
p_primary =
  (Number <$> p_number)
  <+> (Variable <$> p_name)
  <+> p_lrpar p_expr
  <+> p_pair

p_pair :: Parser Token Expr
p_pair = p_lrpar $
  do e1 <- p_expr; eat COMMA
     e2 <- p_expr
     return $ Pair (e1, e2)

p_type :: Parser Token Type
p_type = p_lrpar (
  do  t1 <- p_type; eat COMMA
      P t1 <$> p_type
  )
  <+>
  do tokenToType <$> scan;

p_number :: Parser Token Double
p_number =
  do t <- scan; case t of NUMBER n -> return n; _ -> p_fail

p_name :: Parser Token Ident
p_name = p_ident ID <+> p_lrpar p_op

p_op :: Parser Token Ident
p_op =
  p_ident MONOP <+> p_addop <+> p_mulop <+> p_relop

p_ident :: IdKind -> Parser Token Ident
p_ident k =
  do t <- scan; case t of IDENT k' x | k == k' -> return x; _ -> p_fail

p_lrpar :: Parser Token t -> Parser Token t
p_lrpar p = do eat LPAR; x <- p; eat RPAR; return x;

parser :: Syntax Token Phrase
parser = (lexer, p_phrase)