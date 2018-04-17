data Zero : Set where

record One : Set where

data _+_ (S : Set)(T : Set) : Set where
     inl : S -> S + T 
     inr : T -> S + T


{- 
Sigma type, behaves like existential quantitifcation
ie, 'there exists an S, for which T holds' ...I think 
-}
record Sg (S : Set)(T : S -> Set) : Set where
  constructor  _,_
  field
    fst : S
    snd : T fst


{- Product type is the non dependant version of Sigma -}
_*_ : (S : Set)(T : Set) -> Set
S * T = Sg S \ _ -> T


comm-* : {S : Set}{T : Set} -> S * T -> T * S
comm-* (fst , snd) = snd , fst
