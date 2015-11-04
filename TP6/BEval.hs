module BEval where

import qualified Prelude

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
type Value = Prelude.Bool

data BoolExpr =
   Bbool Prelude.Bool
 | Or BoolExpr BoolExpr
 | Bnot BoolExpr

beval :: BoolExpr -> Value
beval e =
  case e of {
   Bbool b -> b;
   Or e1 e2 ->
    case beval e1 of {
     Prelude.True -> Prelude.True;
     Prelude.False -> beval e2};
   Bnot e1 ->
    case beval e1 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

sbeval :: BoolExpr -> Value
sbeval e =
  case e of {
   Bbool b -> b;
   Or e1 e2 ->
    case sbeval e1 of {
     Prelude.True -> Prelude.True;
     Prelude.False -> sbeval e2};
   Bnot e1 ->
    case sbeval e1 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

bevalC :: BoolExpr -> Value
bevalC e =
  beval e

sbevalC :: BoolExpr -> Value
sbevalC e =
  sbeval e

