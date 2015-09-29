{
module DSL.RawExprParser
    ( parseRawExpr
    ) where

import DSL.Expr ( Type(..), RawExpr(..), BinOp(..), VarId(..)
                , InterleavingMarkedNet )
import DSL.RawExprLexer ( LexerTok(..), lexer )
import NFA ( NFAWithBoundaries(..) )

import Control.Applicative ( (<$>) )
import Control.Arrow ( first, second )
import Control.Monad ( liftM, liftM2, liftM3, (>=>), liftM3 )
import Control.Monad.Error ( throwError, ErrorT, runErrorT )
import Control.Monad.Reader ( ask, asks, local, Reader, runReader )
import Data.List ( elemIndex )
import Data.Map ( Map )
import Data.Maybe ( fromMaybe )
import qualified Data.Map.Strict as M
import qualified Data.Text as T
}

%tokentype { LexerTok }
%name parseExpInternal EXPR
%monad { Either String } { (>>=) } { return }
%error { throwError . ("Couldn't parse input, with remaining:" ++) . show }

%token
  name       { TokName $$ }
  bind       { TokBind }
  read       { TokRead }
  '='        { TokEq }
  in         { TokIn }
  lam        { TokLambda }
  '.'        { TokDotSep }
  ':'        { TokColon }
  net        { TokNet }
  arr        { TokArr }
  '('        { TokLPar }
  ')'        { TokRPar }
  num        { TokNum $$ }
  '+'        { TokPlus }
  '-'        { TokMinus }
  intcase    { TokIntCase }
  inttype    { TokIntType }
  n_sequence { TokSequence }
  tens       { TokTens }
  seq        { TokSeq }

%left '-'
%left '+'
%left tens
%left seq

%%

TYPE : inttype       { return TyInt }
     | net num num   { return $ TyArr $2 $3 }
     | TYPE arr TYPE { liftM2 (:->) $1 $3 }

EXPR : bind name '=' EXPR in EXPR { createBind $2 $4 $6 }
     | lam name ':' TYPE '.' EXPR { createLam $2 $4 $6 }
     | EXPR1                      { $1 }

EXPR1 : EXPR1 seq EXPR1           { liftM2 RSeq $1 $3 }
      | EXPR1 tens EXPR1          { liftM2 RTen $1 $3 }
      | n_sequence EXPR3 EXPR3    { liftM2 RNSequence $2 $3 }
      | intcase EXPR3 EXPR3 EXPR3 { liftM3 RIntCase $2 $3 $4 }
      | EXPR2                     { $1 }

EXPR2 : EXPR2 EXPR3 { liftM2 RApp $1 $2 }
      | EXPR3       { $1 }

EXPR3 : name            { createVarOrName $1 }
      | num             { return $ RNum $1 }
      | read            { return RRead }
      | EXPR3 '+' EXPR3 { liftM2 (RBin Add) $1 $3 }
      | EXPR3 '-' EXPR3 { liftM2 (RBin Sub) $1 $3 }
      | '(' EXPR ')'    { $2 }

{
type VarName = String
type Context = [VarName]

-- An exp can fail to parse if we can't lookup a var from the context, so
-- we allow for the possibility of error.
type FailureCtxExpr = FailureCtx RawExpr
type FailureCtx a = ErrorT String (Reader Context) a

parseRawExpr :: T.Text -> Either String RawExpr
parseRawExpr = parseExpInternal . lexer >=> runR
  where
    runR = flip runReader [] . runErrorT

addNameBinding :: VarName -> Context -> Context
addNameBinding var = (var :)

createBind :: String -> FailureCtxExpr -> FailureCtxExpr -> FailureCtxExpr
createBind var exp body =
    -- To allow recursive bindings, uncomment this.
    -- local (addNameBinding var) $ liftM2 RBind exp body
    liftM2 RBind exp $ local (addNameBinding var) body

createLam :: String -> FailureCtx Type -> FailureCtxExpr -> FailureCtxExpr
createLam var varType body = local (addNameBinding var) $ do
    vt <- varType
    b <- body
    return $ RLam vt b

-- A name can be either a bound (by let/lambda) variable, a constant name or an
-- imported name. We assume that imports are shadowed by constants, which are
-- shadowed by bound variables. That is, if we have imported x, then the x in
-- the body of \x -> x refers to the lambda parameter, not the import.
--
-- Here, we only check if the name is a bound variable, otherwise we assume
-- it's an (in-scope) import/constant.
createVarOrName :: String -> FailureCtxExpr
createVarOrName var =  fromMaybe (RName var) <$> tryCreateVar var

tryCreateVar :: String -> FailureCtx (Maybe RawExpr)
tryCreateVar name = ((RVar . VarId) <$>) <$> asks (elemIndex name)
}
