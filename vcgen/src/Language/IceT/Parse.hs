{-# LANGUAGE ParallelListComp #-}

module Language.IceT.Parse where

import           Language.IceT.Types
import           Text.ParserCombinators.Parsec
import           Text.ParserCombinators.Parsec.Expr
import           Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token    as Token
import qualified Data.Functor.Identity                  as Identity

{-
Core languange:
---------------
 prog(ds, t)         : declarations ds, trace t
 decl(x, s)          : declare x, sort s

 int                 : sorts
 map(s, s)           :
 set                 :

 par([A,B,C])        : A || B || C.
 seq([A,B,C])        : A; B; C.
 skip                : no-operation.
 send(p, x, v)       : process p sends value v to
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
 send(p, x, type, v)  : send a message of type "type".
 recv(p, v)          : process p receives value v.
 recv(p, x, v)       : process p receives value v from
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
  | x=type(t)        :       - of type t.
 recv(p, x, type, v) : receive messages of type "type", only.
 sym(P, S, A)        : composition of symmetric processes p in set s with source A.
                       s must be distinct from process ids.
 for(m, P, S, A)     : process m executes A for each process p in s.
 iter(p, k, A)       : process p executes A k-times.
 while(p, cond, A)   : process p executes A while cond is true.
 nondet(P, s, A)        : process P is chosen non-deterministically in A.
 assign(p, x, v)     : process p assigns value v to variable x.
 ite(P, Cond, A, B)  : process p executes A if Cond holds and B, otherwise.
 if(P, Cond, A)      : Short for ite(P, Cond, A, skip).
 pair(x, y)          : pair of values x and y.
 cases(p, x, C, d)   : proccess p performs a case switch on x with cases specified in
 | C=case(p, exp, A) : C and default case d.
 seq([x,y,z])
-}  

{-> parseString "for(P, X, bs, seq([assign(X,v,0),skip]))"
-}

type ParsedAnnot = Id  
type ParsedProgram = Program ParsedAnnot

parseFile :: String -> IO ParsedProgram
parseFile file
  = readFile file >>= return . parseString

parseString :: String -> ParsedProgram
parseString str
  = case parse iceTParser "" str of
      Left e  -> error $ show e
      Right r -> r

iceTParser :: Parser ParsedProgram  
iceTParser = whiteSpace >> program

program :: Parser ParsedProgram
program = do reserved "prog"  
             p <- parens $ do
               _     <- ident
               comma
               declarations <- list (fmap B decl <|> fmap C declCard)
               comma
               p     <- functor "ensures" prop
               comma
               t     <- stmt
               let vars  = [ v | B v <- declarations ]
                   cards = [ k | C k <- declarations ]
               return Program { decls     = vars
                              , cardDecls = cards
                              , ensures   = p
                              , prog      = t
                              }
             dot
             return p
  where
    tryCards = try (comma >> list declCard) <|> return []

data ParsedDecl a = B Binder | C (Card a)

decl :: Parser Binder
decl = do reserved "decl"
          parens $ do
            v <- ident
            comma
            s <- sort
            return $ Bind v s

declCard :: Parser (Card ParsedAnnot)
declCard = functor "decl_card" $ do
  nm    <- ident
  comma
  owner <- ident
  comma
  i     <- ident
  comma
  e     <- ident
  comma
  p     <- prop
  return $ Card nm owner i e p

sort :: Parser Sort
sort = int <|> set <|> array

int, set, array :: Parser Sort
int   = reserved "int" >> return Int
set   = reserved "set" >> return Set
array = do reserved "map"
           parens $ do
             t1 <- index
             comma
             t2 <- sort
             return $ Map t1 t2

index :: Parser Index
index = (reserved "int" >> return IntIdx)
    <|> (reserved "set" >> parens ident >>= return . SetIdx)
            

stmt :: Parser (Stmt ParsedAnnot)
stmt =  skip
    <|> assignment
    <|> seqs
    <|> cases
    <|> ite
    <|> foreach
    <|> iter
    <|> while
    <|> par
    <|> atomic
    <|> havoc
    <|> pre <|> assert <|> assume

havoc :: Parser (Stmt ParsedAnnot)
havoc = functor "havoc" $ do
  p <- ident
  comma
  x <- ident
  return (Assign p (Bind x Int) p NonDetValue p)

pre :: Parser (Stmt ParsedAnnot)
pre        = do (Assert p _ w) <- functor "pre" $ assertBody
                return (Assert p True w)

assume :: Parser (Stmt ParsedAnnot)
assume     = functor "assume" $ do
  w <- ident
  comma
  p <- prop <?> "prop"
  return (Assume p w)

assert :: Parser (Stmt ParsedAnnot)
assert     = functor "assert" $ assertBody

assertBody :: Parser (Stmt ParsedAnnot)  
assertBody = do w <- ident
                comma
                p <- prop <?> "prop"
                return (Assert p False w)
  
par :: Parser (Stmt ParsedAnnot)
par = functor "sym" $ do
  p <- ident
  comma
  ps <- ident
  comma
  s <- stmt
  return (Par p ps TT s "")

atomic :: Parser (Stmt ParsedAnnot)
atomic = do s <- functor "atomic" $ stmt
            return $ Atomic { atomicStmt  = s
                            , atomicPost  = TT
                            , atomicLabel = 0
                            , stmtData    = ""
                            }

skip :: Parser (Stmt ParsedAnnot)
skip = reserved "skip" >> return (Skip "")

assignment :: Parser (Stmt ParsedAnnot)
assignment = functor "assign" (try assignVars <|> assignConst)

assignConst :: Parser (Stmt ParsedAnnot)
assignConst = do
  p <- ident
  comma
  xs <- assignLHS
  comma
  es <- assignRHS
  matchAssign p p xs es
  
assignVars :: Parser (Stmt ParsedAnnot)
assignVars = do 
    p <- ident
    comma
    xs <- assignLHS
    comma
    q <- ident
    comma
    ys <- assignRHS
    matchAssign p q xs ys

matchAssign :: Id -> Id -> [Id] -> [Expr ParsedAnnot] -> Parser (Stmt ParsedAnnot)
matchAssign p q [i] [e] = return $ Assign p (Bind i Int) q e p
matchAssign p q is es
  | length is == length es = return $ Seq ([Assign p (Bind i Int) q e p | i <- is | e <- es]) p
  | otherwise              = error "matchAssign: lists have to be of equal size"

assignLHS :: Parser [String]
assignLHS = pairNested ident 

assignRHS :: Parser [Expr ParsedAnnot]
assignRHS = pairNested expr

pairNested :: Parser a -> Parser [a]
pairNested p
  = one <|> pair
  where one  = do { i <- p; return [i] }
        pair = functor "pair" $ do
          i1 <- (pairNested p)
          comma
          i2 <- (pairNested p)
          return (i1 ++ i2)

seqs :: Parser (Stmt ParsedAnnot)
seqs = do reserved "seq"
          stmts <- parens $ list stmt
          case stmts of
            [s] -> return s
            _   -> return $ Seq stmts ""

ite :: Parser (Stmt ParsedAnnot)
ite = functor "ite" $ do
  p <- ident
  comma
  test <- prop
  comma
  s1 <- stmt
  comma
  s2 <- stmt
  return $ If test s1 s2 p

cases :: Parser (Stmt ParsedAnnot)
cases = functor "cases" $ do
  p <- ident
  comma
  discr <- expr
  comma
  cs <- list casestmt
  comma
  stmt
  return $ Cases discr cs p

casestmt :: Parser (Case ParsedAnnot)
casestmt = functor "case" $ do
  p <- ident
  comma
  e <- expr
  comma
  s <- stmt
  return $ Case e s p

foreach :: Parser (Stmt ParsedAnnot)
foreach = functor "for" $ do
  who <- ident
  comma
  x   <- ident
  comma
  xs  <- ident
  comma
  rest <- ident
  comma
  inv  <- prop
  comma
  s   <- stmt
  return $ ForEach (Bind x Int)
                   (Bind xs Set)
                   (rest, inv)
                   s
                   who

iter :: Parser (Stmt ParsedAnnot)
iter = functor "iter" $ do
  k <- ident
  comma
  inv <- prop
  comma
  s <- stmt
  return $ ForEach (Bind "!iter" Int)
                   (Bind k Set)
                   ("!i", inv)
                   s
                   ""
prop :: Parser (Prop ParsedAnnot)  
prop = (reserved "true"  >> return TT)
   <|> (reserved "false" >> return FF)
   <|> (reserved "ndet" >> return NonDetProp)
   <|> atom
   <|> implies
   <|> andProp
   <|> orProp
   <|> notProp
   <|> forallProp
   <|> existsProp
   <|> elemProp
   <|> hereProp
   <|> doneProp
   
doneProp :: Parser (Prop ParsedAnnot)
doneProp = functor "done" $ do
  p <- ident
  comma
  ps <- ident
  return $ Atom Eq (pc ps p) (Const (-1))

atom :: Parser (Prop ParsedAnnot)
atom = do e1 <- expr
          r  <- rel
          e2 <- expr
          return $ Atom r e1 e2

rel :: Parser Rel
rel =  try (reservedOp "=<"  >> return Le)
   <|> (reservedOp "<"  >> return Lt)
   <|> (reservedOp ">"  >> return Gt)
   <|> (reservedOp "=" >> return Eq)

forallProp :: Parser (Prop ParsedAnnot)
forallProp = functor "forall" $ do
  ds <- list decl
  comma
  p <- prop
  return $ Forall ds p

existsProp :: Parser (Prop ParsedAnnot)
existsProp = functor "exists" $ do
  ds <- list decl
  comma
  p <- prop
  return $ Exists ds p

implies :: Parser (Prop ParsedAnnot)
implies = functor "implies" $ do
  p1 <- prop
  comma
  p2 <- prop
  return (p1 :=>: p2)

andProp :: Parser (Prop ParsedAnnot)
andProp = functor "and" $ do
  ps <- list prop
  return $ And ps

orProp :: Parser (Prop ParsedAnnot)
orProp = functor "or" $ do
  ps <- list prop
  return $ Or ps

notProp :: Parser (Prop ParsedAnnot)
notProp = functor "not" $ (Not <$> prop)

elemProp :: Parser (Prop ParsedAnnot)
elemProp = functor "elem" $ do
  e1 <- expr
  comma
  e2 <- expr
  return $ Atom SetMem e1 e2

hereProp :: Parser (Prop ParsedAnnot)
hereProp = functor "here" $ (Here <$> expr)

while :: Parser (Stmt ParsedAnnot)
while = do reserved "While"
           parens $ do
             who <- ident
             comma
             (Var x) <- expr
             comma
             s <- stmt
             return $ While x s who

expr :: Parser (Expr ParsedAnnot)
expr = buildExpressionParser table term <?> "expression"
  where
    table = [ [ Infix (reservedOp "*" >> return (Bin Mul)) AssocLeft
              , Infix (reservedOp "/" >> return (Bin Div)) AssocLeft
              ]
            , [ Infix (reservedOp "+" >> return (Bin Plus)) AssocLeft
              , Infix (reservedOp "-" >> return (Bin Minus)) AssocLeft
              ]
            ]
    term  = num <|> var <|> sel <|> set_add <|> size <|> upd <|> ndet <?> "term" 

num :: Parser (Expr ParsedAnnot)
num = do i <- integer
         return $ Const (fromInteger i)

var :: Parser (Expr ParsedAnnot)
var = do i <- ident
         return $ Var i

sel :: Parser (Expr ParsedAnnot)
sel = functor "sel" sel'
  <|> functor "ref" sel'
  <|> do {Select e1 e2 <- functor "varOf" sel'; return (Select e2 e1)}
  where
   sel' = do
     e1 <- expr
     comma
     e2 <- expr
     return (Select e1 e2)

set_add :: Parser (Expr ParsedAnnot)
set_add = functor "set_add" $ do
  e1 <- expr
  comma
  e2 <- expr
  return (Bin SetAdd e1 e2)

size :: Parser (Expr ParsedAnnot)
size = functor "card" $ do
  e <- expr
  return (Size e)

upd :: Parser (Expr ParsedAnnot)
upd = functor "upd" $ do
  Store <$> expr <*> (comma >> expr) <*> (comma >> expr)

ndet :: Parser (Expr ParsedAnnot)
ndet = reserved "ndet" >> return NonDetValue

op :: Parser Op
op = symbol "+" >> return Plus

list :: Parser a -> Parser [a]
list p = brackets $ commaSep p

functor :: String -> Parser a -> Parser a
functor f p = reserved f >> parens p

-------------------------------------------------------------------------------
-- Lexer
-------------------------------------------------------------------------------

lexer :: Token.GenTokenParser String a Identity.Identity
lexer  = Token.makeTokenParser languageDef

ident :: Parser String
ident = Token.identifier lexer

reserved :: String -> Parser ()
reserved = Token.reserved lexer

integer :: Parser Integer
integer = Token.integer lexer

comma :: Parser String
comma = Token.comma lexer

dot :: Parser String
dot = Token.dot lexer

whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer

parens :: Parser a -> Parser a
parens = Token.parens lexer

brackets :: Parser a -> Parser a
brackets   = Token.brackets lexer

commaSep :: Parser a -> Parser [a]
commaSep = Token.commaSep lexer

symbol :: String -> Parser String
symbol = Token.symbol lexer

reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer

languageDef :: GenLanguageDef String a Identity.Identity
languageDef =
  emptyDef { Token.identStart    = letter <|> char '_'
           , Token.identLetter   = alphaNum <|> char '_'
           , Token.reservedNames = [ "par"
                                   , "seq"
                                   , "skip"
                                   , "for"
                                   , "iter"
                                   , "while"
                                   , "nondet"
                                   , "ndet"
                                   , "assign"
                                   , "cases"
                                   , "ite"
                                   , "if"
                                   , "case"
                                   , "skip"
                                   , "prog"
                                   , "int"
                                   , "decl"
                                   , "map"
                                   , "true"
                                   , "false"
                                   , "implies"
                                   , "forall"
                                   , "exists"
                                   , "and"
                                   , "or"
                                   , "not"
                                   , "elem"
                                   , "sel"
                                   , "upd"
                                   , "ref"
                                   , "ensures"
                                   , "sym"
                                   , "atomic"
                                   , "done"
                                   , "pair"
                                   , "assert"
                                   , "assume"
                                   , "here"
                                   , "varOf"
                                   , "havoc"
                                   , "card"
                                   , "decl_card"
                                   ]
           , Token.commentStart = "/*"
           , Token.commentEnd   = "*/"
           , Token.commentLine  = "//"
           , Token.reservedOpNames = [ "-", "+", "<", "=<", "/", "=", ">" ]
           }
