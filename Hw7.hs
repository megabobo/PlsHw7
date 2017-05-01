module Hw7 where

import Control.Applicative
import Data.Char
import Data.List

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import System.Environment
import System.Exit

data Type = Trash | Tint | TBool | TFun Type Type deriving (Eq, Show)

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
  | Num Int
  | TCompare Expr Comparison Expr
  | TBinop Expr Binop Expr
  | TUnop Unop Expr
  | If Expr Expr Expr deriving (Eq, Show)

data Comparison = 
  Less
  | Greater
  | Leq
  | Geq
  | Equal deriving (Eq,Show) 

data Binop = 
  Multiply
  | Divide
  | Plus
  | Minus
  | And
  | Or deriving (Eq,Show)
data Unop = 
  Negative
  | Not
  | Fst
  | Snd deriving (Eq,Show)


type Context = Map VarName Type

data TypeError = ExpectedFunction Expr Type
               | Mismatch Expr Type Type {- expression, got, expected -}
               | UnboundVariable VarName deriving Show

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
typeOf g (If e1 e2 e3) = do
  t1 <- typeOf g e1
  t2 <- typeOf g e2
  t3 <- typeOf g e3
  case t1 of
    TBool | t2 == t3 -> pure t2
    TBool -> Left $ Mismatch e3 {- arbitrary! -} t3 t2
    _ -> Left $ Mismatch e1 t1 TBool

parens' :: String -> String
parens' a = "(" ++ a ++ ")"

spaces' :: Parser ()
spaces' = some (satisfy isSpace) *> pure ()

char' :: Char -> Parser Char
char' c = spaces' *> satisfy (==c)

var' :: Parser String
var' = ensure (not . isKeyword) $ spaces' *> (Parser $ \s -> if (length s /= 0 && isAlpha (head s)) then Just("", s) else Nothing) *> many (satisfy isAlphaNum)

isDot :: Char -> Bool
isDot c = c == '.'

isColon :: Char -> Bool
isColon c = c == ':'

int :: Parser Int
int = read <$> some (satisfy isDigit)


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
keywords = ["let", "in", "lambda", "if", "then", "else"]

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
var = ensure (not . isKeyword) $ ws *> (Parser $ \s -> if (length s /= 0 && isAlpha (head s)) then Just("", s) else Nothing) *> many (satisfy isAlphaNum)

ensure :: (a -> Bool) -> Parser a -> Parser a
ensure p parser = Parser $ \s ->
   case parse parser s of
     Nothing -> Nothing
     Just (a,s') -> if p a then Just (a,s') else Nothing

parseCompare :: Parser Comparison
parseCompare = Leq <$ str "<=" <|> Geq <$ str ">=" <|> Less <$ str "<" <|> Greater <$ str ">" <|> Equal <$ str "=="

lam' :: Parser Expr
lam' = spaces *> str "lambda" *> spaces' *> vars <|> ifelse

--inLambda :: Parser Expr
--inLambda = vars <*> lam' <|> char '(' *> inLambda <* char ')'

vars' :: Parser (Expr -> Expr)
vars' = Lam <$> (var <* spaces <* char ':' <* spaces) 
           <*> (tfun <* spaces) 

vars :: Parser Expr
vars = Lam <$> (var <* spaces <* char ':' <* spaces) 
           <*> (tfun <* spaces <* char '.' <* spaces <|> tfun <* spaces) <*> lam'
           <|> char '(' *> vars' <* char ')' <* spaces <* char '.' <* spaces <*> lam'
           <|> char '(' *> vars' <* char ')' <* spaces <*> vars

app, assign, lam, atom, ifelse :: Parser Expr
typer :: Parser Type
assign = Let <$> (spaces *> str "let" *> (Var <$> var' <* spaces) <* char '=' <* spaces) <*> ((TExp <$> (char '(' *> lam <* spaces <* char ':' <* spaces) <*> (tfun <* char ')')) <|> lam) <*> (str' "in" *> spaces' *> assign) 
     <|> helper <$> (Let <$> (spaces *> str "let" *> ((TExp <$> (Var <$> var' <* spaces <* char ':' <* spaces) <*> (tfun <* spaces))) <* char '=' <* spaces) <*> ((TExp <$> (char '(' *> lam <* spaces <* char ':' <* spaces) <*> (tfun <* char ')')) <|> lam) <*> (str' "in" *> spaces' *> assign)) 
     <|> lam
lam = Lam <$> (spaces *> str "lambda" *> var') <*> (spaces *> char ':' *> spaces *> tfun <* spaces) <*> (spaces *> char '.' *> spaces *> lam) <|> Lam <$> (spaces *> str "lambda" *> spaces' *> str "(" *> var) <*> (spaces *> char ':' *> spaces *> tfun <* str ")") <*> lam2 
      <|> ifelse
lam2 = Lam <$> (spaces' *> str "(" *> var) <*> (spaces *> char ':' *> spaces *> tfun <* str ")") <*> lam2 <|> spaces *> char '.' *> spaces *> lam 
      <|> ifelse
tfun = TFun <$> (typer <* spaces <* str "->") <*> (spaces *> tfun <* spaces) <|> typer
typer = Tint <$ str "int" <|> TBool <$ str "bool" <|> char '(' *> tfun <* char ')'
ifelse = If <$> (spaces *> str "if" *> spaces' *> (TCompare <$> lam <* spaces <*> parseCompare <* spaces <*> lam <|> lam) <* spaces' <* str "then" <* spaces') 
         <*> (assign <* spaces' <* str "else" <* spaces') <*> assign 
         <|> app
app = atom `chainl1` (spaces' *> pure App)  
atom =  Num <$> int <|> Var <$> var <|> (char '(' *> lam <* char ')')
helper:: Expr -> Expr
helper (Let (TExp exp t) (exp2) (exp3)) = Let (exp) (TExp (exp2) t) (exp3)
helper _                                = error "dumbass"


