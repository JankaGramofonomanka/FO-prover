module Parser where

import System.IO
import Control.Monad
import Text.Parsec
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import qualified Text.ParserCombinators.Parsec as Parsec
import Test.QuickCheck hiding (Fun)
import Utils
import Formula

languageDef =
   emptyDef { Token.commentStart    = "(-"
            , Token.commentEnd      = "-)"
            , Token.commentLine     = "--"
            , Token.identStart      = letter <|> oneOf "_"
            , Token.identLetter     = alphaNum <|> oneOf "_"
            , Token.reservedNames   = [ "Var"
                                      , "Fun"
                                      , "Rel"
                                      , "Prop"
                                      , "And"
                                      , "Not"
                                      , "Or"
                                      , "Implies"
                                      , "Iff"
                                    --   , "T"
                                    --   , "F"
                                      , "Exists"
                                      , "Forall"
                                      ]
            , Token.reservedOpNames = ["\"", ",", "[", "]"]
           }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis:
                                    --   parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
integer    = Token.integer    lexer -- parses an integer
semi       = Token.semi       lexer -- parses a semicolon
whiteSpace = Token.whiteSpace lexer -- parses whitespace

formulaParser :: Parser Formula
formulaParser = whiteSpace >> formula

term :: Parser Term
term = parens term
    <|> varTerm
    <|> funTerm

varTerm :: Parser Term
varTerm = do reserved "Var"
             reservedOp "\"" 
             name <- identifier
             reservedOp "\""
             return $ Var name

funTerm :: Parser Term
funTerm = do
    reserved "Fun"
    reservedOp "\"" 
    f <- identifier
    reservedOp "\""
    ts <- list term
    return $ Fun f ts

list :: Parser a -> Parser [a]
list parser = do
    reservedOp "["
    list <- (oneOrMore parser <|> zero)
    reservedOp "]"
    return $ list

zero :: Parser [a]
zero = return []

oneOrMore :: Parser a -> Parser [a]
oneOrMore parser = Parsec.try (more parser) <|> one parser

one :: Parser a -> Parser [a]
one parser = do
    a <- parser
    return $ [a]

more :: Parser a -> Parser [a]
more parser = do
    a <- parser
    reservedOp ","
    as <- oneOrMore parser
    return $ a : as

relFormula :: Parser Formula
relFormula = do
    reserved "Rel"
    reservedOp "\"" 
    r <- identifier
    reservedOp "\""
    ts <- list term
    return $ Rel r ts

-- a proposition is just a 0-ary relation
propFormula :: Parser Formula
propFormula = do
    reserved "Prop"
    reservedOp "\"" 
    r <- identifier
    reservedOp "\""
    return $ Rel r []

formula :: Parser Formula
formula = parens formula
    <|> trueFormula
    <|> falseFormula
    <|> relFormula
    <|> propFormula
    <|> notFormula
    <|> andFormula
    <|> orFormula
    <|> impliesFormula
    <|> iffFormula
    <|> existsFormula
    <|> forallFormula

trueFormula :: Parser Formula
trueFormula = do reserved "T"
                 return T

falseFormula :: Parser Formula
falseFormula = do reserved "F"
                  return F

notFormula :: Parser Formula
notFormula = do reserved "Not"
                phi <- formula
                return $ Not phi

andFormula :: Parser Formula
andFormula = do reserved "And"
                phi <- formula
                psi <- formula
                return $ And phi psi
                
orFormula :: Parser Formula
orFormula = do reserved "Or"
               phi <- formula
               psi <- formula
               return $ Or phi psi

impliesFormula :: Parser Formula
impliesFormula = do reserved "Implies"
                    phi <- formula
                    psi <- formula
                    return $ Implies phi psi

iffFormula :: Parser Formula
iffFormula = do reserved "Iff"
                phi <- formula
                psi <- formula
                return $ Iff phi psi

existsFormula :: Parser Formula
existsFormula = do
    reserved "Exists"
    reservedOp "\"" 
    x <- identifier
    reservedOp "\""
    phi <- formula
    return $ Exists x phi

forallFormula :: Parser Formula
forallFormula = do
    reserved "Forall"
    reservedOp "\"" 
    x <- identifier
    reservedOp "\""
    phi <- formula
    return $ Forall x phi

parseString :: String -> Formula
parseString str =
    case parse formulaParser "" str of
        Left e  -> error $ show e
        Right r -> r

parseIntegers :: String -> [Integer]
parseIntegers str = 
    case parse (list integer)  "" str of
        Left e  -> error $ show e
        Right r -> r

prop_parse :: Formula -> Bool
prop_parse phi = phi == (parseString $ show phi)

phi0 = Rel "R" []
phi1 = Exists "x" (Rel "R" [Fun "f" [Var "x", Var "y"], Var "z"])
phi2 = Rel "R" [Fun "f" [Var "z",Var "t",Var "t",Var "t",Fun "f" [Var "y",Var "z"],Var "z",Var "z"]]

-- check = do quickCheck prop_parse