data Zero : Set where

record One : Set where

data _+_ (S : Set)(T : Set) : Set where
     inl : S -> S + T 
     inr : T -> S + T


{- A proof that 'A or B implies B or A' -}
comm-+ : {S : Set}{T : Set} -> S + T -> T + S
comm-+ (inl x) = inr x
comm-+ (inr x) = inl x

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

{- A proof that 'A and B implies B and A' -} 
comm-* : {S : Set}{T : Set} -> S * T -> T * S
comm-* (fst , snd) = snd , fst

-- not just defining a set, but one that depends on two values
data _==_ {X : Set} : X -> X -> Set where
  refl : (x : X) -> x == x

-- dont know what this means
{-# BUILTIN EQUALITY _==_ #-}




-- If we have equal functions and equal arguments, the return values are equal
_=$=_ : { X Y : Set }{ f f' : X -> Y }{ x x' : X } -> (f == f') -> (x == x') -> (f x == f' x')
refl f =$= refl x = refl (f x)



data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
zero +N j = j
suc i +N j = suc (i +N j)

-- this definition of plus makes sense
see5 : (2 +N 3) == 5
see5 = refl 5

-- this compiles
_+stupid_ : Nat -> Nat -> Nat
zero +stupid j = zero
suc i +stupid j = suc (i +stupid j)

-- while this does not. We cannot provide evidence that 2 `stupidPlus` 3 is equal to 5
-- cannotsee5 : (2 +stupid 3) == 5
-- cannotsee5 = refl 5

-- given two natural numbers, one is greater than the other
_>=_ : Nat -> Nat -> Set
m >= zero = One
zero >= suc n = Zero
suc m >= suc n = m >= n


-- Note in thist definition for `>=` the return of the function is a TYPE
-- Totally different to haskell... Here we are allowed to 'compute types'



{-
comm-+N : {A : Set}{B : Set} -> A +N B -> B +N A
comm-+N exp = ?
-}
