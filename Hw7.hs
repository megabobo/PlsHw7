module Hw7 where

import Control.Applicative
import Data.Char
import Data.List

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Either
import Data.Maybe
import System.Environment
import System.Exit

data Type = Tint | TBool | TFun Type Type | TPair Type Type deriving (Eq, Ord)

newtype Parser a = Parser { parse :: String -> Maybe (a,String) }

instance Functor Parser where
  fmap f p = Parser $ \s -> (\(a,c) -> (f a, c)) <$> parse p s

instance Applicative Parser where
   pure a = Parser $ \s -> Just (a,s)
   f <*> a = Parser $ \s ->
     case parse f s of
       Just (g,s') -> parse (fmap g a) s'
       Nothing -> Nothing

instance Alternative Parser where
   empty = Parser $ \s -> Nothing
   l <|> r = Parser $ \s -> parse l s <|> parse r s

type VarName = String

data Expr =
    Var VarName
  | App Expr Expr
  | Lam VarName Type Expr
  | Bool Bool
  | TExp Expr Type
  | Let Expr Expr Expr
  | LetRec Expr Expr Expr
  | Num Int
  | Less Expr Expr
  | Greater Expr Expr
  | Leq Expr Expr
  | Geq Expr Expr
  | Equal Expr Expr
  | Multiply Expr Expr
  | Divide Expr Expr
  | Plus Expr Expr
  | Minus Expr Expr
  | And Expr Expr
  | Or Expr Expr
  | Negative Expr
  | Not Expr
  | Fst Expr
  | Snd Expr
  | If Expr Expr Expr 
  | Pair Expr Expr deriving (Eq, Ord)


type Context = Map VarName Type

data TypeError = ExpectedFunction Expr Type
               | Mismatch Expr Type Type {- expression, got, expected -}
               | UnboundVariable VarName deriving Show

instance Show Type where
  show (Tint) = "int"
  show (TBool) = "bool"
  show (TFun x y) = show x ++ " -> " ++ show y
  show (TPair x y) = "(" ++ show x ++ "," ++ show y ++ ")"

instance Show Expr where
  show (Lam x t y)                    = "lambda " ++ x ++ ":" ++ show t ++ ". " ++ show y
  show (Var x)                        = x
  show (App (Var x) (Var y))          = x ++ " " ++ y
  show (App (Var a) (Lam x t y))      = a ++ " " ++ parens' (show (Lam x t y))
  show (App (Lam x t y) (Var a))      = parens' (show (Lam x t y)) ++ " " ++ a
  show (App (Lam x t y) (Lam a t2 b)) = parens' (show (Lam x t y)) ++ " " ++ parens' (show (Lam a t2 b))
  show (App a (Lam x t y))            = parens' (show a) ++ " " ++ parens' (show (Lam x t y))
  show (App (Lam x t y) a)            = parens' (show (Lam x t y)) ++ " " ++ parens' (show a)
  show (App a (App x y))              = show a ++ " " ++ parens' (show (App x y))
  show (App x y)                      = show x ++ " " ++ show y 
  show (Let x y z)                    = "let " ++ show x ++ " " ++ show y ++ " in " ++ show z   
  show (Bool True)                    = "true"
  show (Bool False)                   = "false"
  show (TExp e t)                     = show e ++ ":" ++ show t
  show (LetRec a b c)                 = show a ++ " " ++ show b ++ " " ++ show c
  show (Num x)                        = show x
  show (Less x y)                     = show x ++ " < " ++ show y
  show (Greater x y)                  = show x ++ " > " ++ show y 
  show (Leq x y)                      = show x ++ " <= " ++ show y
  show (Geq x y)                      = show x ++ " >= " ++ show y
  show (Equal x y)                    = show x ++ " == " ++ show y
  show (Multiply x y)                 = show x ++ " * " ++ show y
  show (Divide x y)                   = show x ++ " / " ++ show y
  show (Plus x y)                     = show x ++ " + " ++ show y
  show (Minus x y)                    = show x ++ " - " ++ show y
  show (And x y)                      = show x ++ " && " ++ show y
  show (Or x y)                       = show x ++ " || " ++ show y
  show (Negative x)                   = "-" ++ show x
  show (Not x)                        = "not " ++ show x
  show (Fst (Pair x y))               = show x
  show (Snd (Pair x y))               = show y
  show (If x y z)                     = "if " ++ show x ++ " then " ++ show y ++ " else " ++ show z
  show (Pair x y)                     = "(" ++ show x ++ "," ++ show y ++ ")"

parens' :: String -> String
parens' a = "(" ++ a ++ ")"

typeOf :: Context -> Expr -> Either TypeError Type
typeOf g (Var x) =
  case Map.lookup x g of
    Nothing -> Left $ UnboundVariable x
    Just t -> pure t
typeOf g (Lam x t1 e) = do
  t2 <- typeOf (Map.insert x t1 g) e
  pure $ TFun t1 t2
typeOf g e@(App e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  case t1 of
    TFun t11 t12 | t11 == t2 -> pure t12
    TFun t11 t12 -> Left $ Mismatch e t2 t11
    _ -> Left $ ExpectedFunction e1 t1
typeOf _ (Bool _) = pure TBool
typeOf _ (Num _) = pure Tint
typeOf g (If e1 e2 e3) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  t3 <- typeOf g e3
  case t1 of
    TBool | t2 == t3 -> pure t2
    TBool -> Left $ Mismatch e3 {- arbitrary! -} t3 t2
    _ -> Left $ Mismatch e1 t1 TBool
typeOf g (TExp e t) = do
  t1 <- typeOf g e
  if (t1 ==  t) then pure t1
  else Left $ Mismatch (TExp e t) t1 t

typeOf g (Multiply e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  case (t1,t2) of
     (Tint, Tint) -> pure t1
     _         -> Left $ Mismatch (Multiply e1 e2) t1 t2

typeOf g (Divide e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  case (t1,t2) of
     (Tint, Tint) -> pure t1
     _         -> Left $ Mismatch (Divide e1 e2) t1 t2

typeOf g (Plus e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  case (t1,t2) of
     (Tint, Tint) -> pure t1
     _         -> Left $ Mismatch (Plus e1 e2) t1 t2 

typeOf g (Minus e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  case (t1,t2) of
     (Tint, Tint) -> pure t1
     _         -> Left $ Mismatch (Minus e1 e2) t1 t2

typeOf g (Equal e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  if (t1 == t2) then pure TBool 
    else Left $ Mismatch (Multiply e1 e2) t1 t2

typeOf g (Less e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  case (t1,t2) of
     (Tint, Tint) -> pure TBool
     _         -> Left $ Mismatch (Less e1 e2) t1 t2

typeOf g (Greater e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  case (t1,t2) of
     (Tint, Tint) -> pure TBool
     _         -> Left $ Mismatch (Greater e1 e2) t1 t2  

typeOf g (Leq e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  case (t1,t2) of
     (Tint, Tint) -> pure TBool
     _         -> Left $ Mismatch (Leq e1 e2) t1 t2

typeOf g (Geq e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  case (t1,t2) of
     (Tint, Tint) -> pure TBool
     _         -> Left $ Mismatch (Geq e1 e2) t1 t2

typeOf g (And e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  case (t1,t2) of
     (TBool, TBool) -> pure t1
     _         -> Left $ Mismatch (And e1 e2) t1 t2

typeOf g (Or e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  case (t1,t2) of
     (TBool, TBool) -> pure t1
     _         -> Left $ Mismatch (Or e1 e2) t1 t2

typeOf g (Negative e1) = do
  t1 <- typeOf g e1
  case t1 of
     Tint -> pure t1
     _         -> Left $ Mismatch (Negative e1) t1 Tint

typeOf g (Not e1) = do
  t1 <- typeOf g e1
  case t1 of
     TBool -> pure t1
     _         -> Left $ Mismatch (Not e1) t1 TBool

typeOf g (Fst e1) = do
  t1 <- typeOf g e1
  case t1 of
     TPair t2 t3 -> pure t2
     _         -> Left $ Mismatch (Fst e1) t1 (TPair t1 t1)

typeOf g (Snd e1) = do
  t1 <- typeOf g e1
  case t1 of
     TPair t2 t3 -> pure t3
     _         -> Left $ Mismatch (Snd e1) t1 (TPair t1 t1)

typeOf g (Pair e1 e2) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  pure (TPair t1 t2)

typeOf g (Let e e1 e2) = do
                          t1 <- typeOf g e1
                          case e of
                            (Var x) -> do
                                         t2 <- typeOf (Map.insert x t1 g) e2
                                         pure t2
                            _     -> Left $ Mismatch (Let e e1 e2) t1 t1
typeOf g (LetRec (TExp e1 t) e2 e3) = 
      case e1 of
        (Var x) -> do
                     t1 <- typeOf (Map.insert x t g) e2
                     if (t == t1) then do
                                         t3 <- typeOf (Map.insert x t g) e3
                                         pure t3
                      else
                          Left $ Mismatch (LetRec e1 e2 e3) t t1
        _       -> Left $ Mismatch (LetRec e1 e2 e3) t t


isAlphaNumOrQuote :: Char -> Bool
isAlphaNumOrQuote x = (isAlphaNum x) || (x == '\'')

spaces' :: Parser ()
spaces' = some (satisfy isSpace) *> pure ()

char' :: Char -> Parser Char
char' c = spaces' *> satisfy (==c)

var' :: Parser String
var' = ensure (not . isKeyword) $ spaces' *> (Parser $ \s -> if (length s /= 0 && isAlpha (head s)) then Just("", s) else Nothing) 
       *> many (satisfy isAlphaNumOrQuote)

isDot :: Char -> Bool
isDot c = c == '.'

isColon :: Char -> Bool
isColon c = c == ':'

int :: Parser Int
int = spaces *> (read <$> some (satisfy isDigit))


chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p sep = foldl (\acc (op,v) -> op acc v) <$>
                p <*> many ((\op v -> (op,v)) <$> sep <*> p)

char :: Char -> Parser Char
char c = spaces *> satisfy (==c)

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = Parser f
  where f [] = Nothing
        f (x:xs) = if p x then Just (x,xs) else Nothing

spaces :: Parser ()
spaces = many (satisfy isSpace) *> pure ()

parens :: Parser a -> Parser a
parens p = (char '(' *> p) <* char ')'

ws :: Parser ()
ws = pure () <* many (satisfy isSpace)

keywords :: [String]
keywords = ["let", "in", "lambda", "if", "then", "else", "+", "*", "and", "or", "-", "/", "==", "<", "<=", ">", ">=", "not", "fst", "snd", "let rec"]

isKeyword = (`elem` keywords)

str :: String -> Parser String
str s = ws *> loop s
  where loop [] = pure []
        loop (c:cs) = (:) <$> satisfy (==c) <*> loop cs

str' :: String -> Parser String
str' s = spaces' *> loop s
  where loop [] = pure []
        loop (c:cs) = (:) <$> satisfy (==c) <*> loop cs        

var :: Parser String
var = ensure (not . isKeyword) $ ws *> (Parser $ \s -> if (length s /= 0 && isAlpha (head s)) then Just("", s) else Nothing) 
      *> many (satisfy isAlphaNumOrQuote)

ensure :: (a -> Bool) -> Parser a -> Parser a
ensure p parser = Parser $ \s ->
   case parse parser s of
     Nothing -> Nothing
     Just (a,s') -> if p a then Just (a,s') else Nothing

lam :: Parser Expr
lam = spaces *> str "lambda" *> spaces' *> vars <|> TExp <$> (spaces *> char '(' *> lam <* spaces <* str ":" <* spaces) <*> (tfun <* char ')') <|> ifelse 

ifelse :: Parser Expr
ifelse = If <$> (spaces *> str "if" *> spaces' *> binop)
          <*> (str "then" *> spaces' *> assign) --changed, was lam
          <*> (spaces' *> str "else" *> spaces' *> assign) --changed, was lam
          <|> app

binop :: Parser Expr
binop = comp `chainl1` comparison
    where comparison =  str "==" *> pure Equal
                    <|> str ">=" *> pure Geq     --changed, switched the order of >,< with >=, <= 
                    <|> str "<=" *> pure Leq
                    <|> str "<"  *> pure Less
                    <|> str ">"  *> pure Greater

comp =  loose `chainl1` compOp
      where compOp = str "+"  *> pure Plus
                 <|> str "-"  *> pure Minus
                 <|> str "or" *> pure Or

loose = tight `chainl1` compOp
     where compOp = str "*"   *> pure Multiply
                <|> str "/"   *> pure Divide
                <|> str "and" *> pure And

tight = compOp <|> app
     where compOp = Negative <$> (str "-"   *> atom)
                <|> Not      <$> (str "not" *> atom)
                <|> Fst      <$> (str "fst" *> atom)
                <|> Snd      <$> (str "snd" *> atom)


vars' :: Parser (Expr -> Expr)
vars' = Lam <$> (var <* spaces <* char ':' <* spaces) 
           <*> (tfun <* spaces) 
           <|> spaces *> char '(' *> vars' <* spaces <* char ')' --added, lambda ((x:int)). x

vars :: Parser Expr
vars = Lam <$> (var <* char ':' <* spaces) 
           <*> (tfun <* spaces <* char '.' <* spaces <|> tfun <* spaces) <*> assign -- changed, was lam
           <|> spaces *> char '(' *> vars' <*  spaces <* char ')' <* spaces <* char '.' <* spaces <*> assign --changed, was lam
           <|> spaces *> char '(' *> vars' <* spaces <* char ')' <* spaces <*> vars

parsePair :: Parser Expr
parsePair = Pair <$> (spaces *> char '(' *> spaces *> assign <* spaces <* char ',' <* spaces)
                 <*> (assign <* spaces <* char ')') 

app, assign, atom :: Parser Expr
typer :: Parser Type
assign = LetRec <$> (spaces *> str "let rec" *> ((TExp <$> (Var <$> var' <* spaces <* char ':' <* spaces) 
      <*> (tfun <* spaces))) <* char '=' <* spaces) <*> (TExp <$> (char '(' *> assign <* spaces <* char ':' <* spaces) <*> (tfun <* char ')')  <|> assign) 
      <*> (str' "in" *> spaces' *> assign)
     <|> Let <$> (spaces *> str "let" *> (Var <$> var' <* spaces) <* char '=' <* spaces) <*> ((TExp <$> (char '(' *> assign <* spaces <* char ':' <* spaces) 
      <*> (tfun <* char ')')) <|> assign) <*> (str' "in" *> spaces' *> assign) 
     <|> helper <$> (Let <$> (spaces *> str "let" *> ((TExp <$> (Var <$> var' <* spaces <* char ':' <* spaces) <*> (tfun <* spaces))) <* char '=' <* spaces) 
    <*> ((TExp <$> (char '(' *> assign <* spaces <* char ':' <* spaces) <*> (tfun <* char ')')) <|> assign) <*> (str' "in" *> spaces' *> assign)) 
     <|> binop <|> lam <|> parsePair
tfun = TFun <$> (typer <* spaces <* str "->") <*> (spaces *> tfun <* spaces) <|> typer
typer = Tint <$ str "int" <|> TBool <$ str "bool" <|> char '(' *> tfun <* char ')'
app = atom `chainl1` (spaces' *> pure App)  
atom = Bool True <$ str "true" <|> Bool False <$ str "false" <|> Num <$> int 
       <|> Var <$> var <|> (char '(' *> lam <* char ')') <|> (char '(' *> binop <* char ')')
       <|> parsePair
       <|> char '(' *> assign <* char ')'


helper:: Expr -> Expr
helper (Let (TExp exp t) (exp2) (exp3)) = Let (exp) (TExp (exp2) t) (exp3)
helper _                                = error "dumbass"


sub :: Map Expr Expr -> Expr -> Expr
sub m (Var x) = case Map.lookup (Var x) m of
             Just v  -> v
             Nothing -> Var x
sub m (Bool x) = Bool x
sub m (App x y) = App (sub m x) (sub m y)
sub m (Lam x t y) = Lam x t (sub (Map.delete (Var x) m) y)
sub m (Pair x y) = Pair (sub m x) (sub m y)
sub m (If x y z) = If (sub m x) (sub m y) (sub m z)
sub m (TExp e t) = sub m e
sub m (Less x y) = Less (sub m x) (sub m y)
sub m (Greater x y) = Greater (sub m x) (sub m y)
sub m (Leq x y) = Leq (sub m x) (sub m y)
sub m (Geq x y) = Geq (sub m x) (sub m y)
sub m (Equal x y) = Equal (sub m x) (sub m y)
sub m (Divide x y) = Divide (sub m x) (sub m y)
sub m (Multiply x y) = Multiply (sub m x) (sub m y)
sub m (Plus x y) = Plus (sub m x) (sub m y)
sub m (Minus x y) = Minus (sub m x) (sub m y)
sub m (And x y) = And (sub m x) (sub m y)
sub m (Or x y) = Or (sub m x) (sub m y)
sub m (Negative x) = Negative (sub m x) 
sub m (Num x) = Num x
sub m (Not x) = Not (sub m x)
sub m (Fst x) = Fst (sub m x)  
sub m (Snd x) = Snd (sub m x)  
sub m (Let x y rest) = case eval (sub m y) of
                           (Var interpreted) -> sub (Map.insert x (Var interpreted) m) rest
                           test        -> sub (Map.insert x test m) rest
sub m (LetRec f@(TExp (Var x) t) y (App (App a b) c)) =  LetRec f (sub m y) (App (App a (sub m b)) (sub m c))
sub m (LetRec f@(TExp (Var x) t) y (App a b)) = LetRec f (sub m y) (App a (sub m b)) 
sub m (LetRec f@(TExp (Var x) t) y e2) = LetRec f (sub m y) e2
sub _ _ = error $ "you screwed up"

substitute :: String -> Expr -> Expr -> Expr
substitute s (Var a) subIn = if (s == a) then
                               subIn 
                             else
                               (Var a)
substitute _ (Num x) _ = Num x
substitute _ (Bool x) _ = Bool x
substitute s (Lam l t a) subIn = if (s == l) then
                                    Lam l t a 
                                  else 
                                    Lam l t (substitute s a subIn)
substitute s (App a b) subIn = App (substitute s a subIn) (substitute s b subIn)
substitute s (Equal x y) subIn = Equal (substitute s x subIn) (substitute s y subIn)
substitute s (Less x y) subIn = Less (substitute s x subIn) (substitute s y subIn)
substitute s (Greater x y) subIn = Greater (substitute s x subIn) (substitute s y subIn)
substitute s (Leq x y) subIn = Leq (substitute s x subIn) (substitute s y subIn)
substitute s (Geq x y) subIn = Geq (substitute s x subIn) (substitute s y subIn)
substitute s (Multiply x y) subIn = Multiply (substitute s x subIn) (substitute s y subIn)
substitute s (Divide x y) subIn = Divide (substitute s x subIn) (substitute s y subIn)
substitute s (Plus x y) subIn = Plus (substitute s x subIn) (substitute s y subIn)
substitute s (Minus x y) subIn = Minus (substitute s x subIn) (substitute s y subIn)
substitute s (Negative x) subIn = Negative (substitute s x subIn)
substitute s (And x y) subIn = And (substitute s x subIn) (substitute s y subIn)
substitute s (Or x y) subIn = Or (substitute s x subIn) (substitute s y subIn)
substitute s (Pair x y) subIn = Pair (substitute s x subIn) (substitute s y subIn)
substitute s (Not x) subIn = Not (substitute s x subIn)
substitute s (If x y z) subIn = If (substitute s x subIn) (substitute s y subIn) (substitute s z subIn)
substitute s (LetRec x y z) subIn = LetRec x (substitute s y subIn) z                      

replace :: String -> Expr -> Expr -> Expr
replace x l (Var a) = if (a == x) then
                        l
                      else
                        substitute x l (Var a)
replace x l a = substitute x l a

eval :: Expr -> Expr
eval (App (Lam x t y) (App a b)) = eval (App (Lam x t y) (eval (App a b)))
eval (App (Lam x t y) z) = eval (replace x y z)
eval (App (App a b) z) = eval (App (eval (App a b)) z)
eval (App (LetRec (TExp x t) b c) n) = eval (LetRec (TExp x t) b (App c n))
eval (Less x y) = Bool ((evalNums x) < (evalNums y))
eval (Greater x y) = Bool ((evalNums x) > (evalNums y))
eval (Leq x y) = Bool ((evalNums x) <= (evalNums y))
eval (Geq x y) = Bool ((evalNums x) >= (evalNums y))
eval (Multiply x y) = Num ((evalNums x) * (evalNums y))
eval (Divide x y) = Num ((evalNums x) `div` (evalNums y))
eval (Plus x y) = Num ((evalNums x) + (evalNums y))
eval (Minus x y) = Num ((evalNums x) - (evalNums y))
eval (And x y) = Bool ((evalBools x) && (evalBools y))
eval (Or x y) = Bool ((evalBools x) || (evalBools y))
eval (Negative x) = Num (- (evalNums x))
eval (Not x) = Bool (not $ evalBools x)
eval (Fst (Pair x _)) = eval x
eval (Snd (Pair _ y)) = eval y
eval (If x y z) = if (evalBools x) then --changed
                    eval y
                  else 
                    eval z
eval (Pair x y) = Pair (eval x) (eval y)
eval (Equal (Pair a b) (Pair c d)) = Bool ((eval a) == (eval c) && (eval b) == (eval d))
eval (Equal x y) = Bool (eval x == eval y)
eval (LetRec (TExp (Var x) t) e1 e2) = eval (App (Lam x t e2) (App (Lam x t e1) (LetRec (TExp (Var x) t) e1 (Var x))))
eval x = x

evalBools :: Expr -> Bool
evalBools (Bool x) = x
evalBools (And x y) = (evalBools x) && (evalBools y)
evalBools (Or x y) = (evalBools x) || (evalBools y)
evalBools (Not x) = not $ evalBools x
evalBools (Equal x y) = (eval x) == (eval y)
evalBools (Less x y) = (evalNums x) < (evalNums y)
evalBools (Greater x y) = (evalNums x) > (evalNums y)
evalBools (Leq x y) = (evalNums x) <= (evalNums y)
evalBools (Geq x y) = (evalNums x) >= (evalNums y)
evalBools (App x y) = case eval (App x y) of
                           Bool b -> b
evalBools _ = error $ "You screwed up"

evalNums :: Expr -> Int
evalNums (Num x) = x
evalNums (Plus x y) = (evalNums x) + (evalNums y)
evalNums (Multiply x y) = (evalNums x) * (evalNums y)
evalNums (Divide x y) = (evalNums x) `div` (evalNums y)
evalNums (Minus x y) = (evalNums x) - (evalNums y)
evalNums (Negative x) =  - (evalNums x)
evalNums (App x y) = case eval (App x y) of
                           Num b -> b
evalNums _ = error $ "You screwed up"

isDash :: [String] -> Bool
isDash [] = False
isDash lst = elem "-" lst 

isU :: [String] -> Bool
isU [] = False
isU lst = elem "-u" lst

isFile :: [String] -> Bool
isFile [] = False
isFile (x:xs) = if (not (isDash [x] || isU [x])) then
                  True
                else
                  isFile xs

getFile :: [String] -> IO String
getFile lst = if (isFile lst) then
                readFile (findFile lst)
              else
                getContents
          where findFile [] = []
                findFile (x:xs) = if (isFile [x]) then
                                     x
                                  else
                                     findFile xs  

getDash :: [String] -> IO String
getDash lst = if (isDash lst) then
                getContents
              else
                getFile lst

getU :: String -> [String] -> IO ()
getU str lst = if (isU lst) then
                 if (isJust (parse assign str)) then                           
                   putStr (show (eval lc))
                 else
                   die "Not parseable input"
               else
                 if (isJust (parse assign str) && (isRight(typeOf Map.empty lc))) then
                   putStr (show (eval lc))
                 else
                   die "Does not Type Check"
                where lc = sub Map.empty (fst (fromJust (parse assign str)))


main :: IO ()
main = getArgs >>= (\x -> getDash x >>= (\y -> getU y x))

