module Predecesor where

import qualified Prelude

data Nat =
   O
 | S Nat

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
predspec :: Nat -> Nat
predspec n =
  case n of {
   O -> O;
   S n0 -> n0}

