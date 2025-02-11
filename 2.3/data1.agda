module data1 where

data _∨_ (A B : Set) : Set where
  case1 : A → A ∨ B
  case2 : B → A ∨ B

ex1 : {A B : Set} → A → ( A ∨ B ) 
ex1 a = case1 a

ex2 : {A B : Set} → ( B → ( A ∨ B ) )
ex2 = λ b → case2 b

ex3 : {A B : Set} → ( A ∨ A ) → A 
ex3 (case1 x) = x
ex3 (case2 x) = x

ex4 : {A B C : Set} →  A ∨ ( B ∨ C ) → ( A ∨  B ) ∨ C 
ex4 (case1 a) = case1 (case1 a )
ex4 (case2 (case1 b)) = case1 (case2 b)
ex4 (case2 (case2 c)) = case2 c

record _∧_ A B : Set where
  constructor  ⟪_,_⟫
  field
     proj1 : A
     proj2 : B

open _∧_

ex3' : {A B : Set} → ( A ∨ B ) →   A ∧ B   -- これは不可能
ex3' (case1 x) = {!   !} --不可能
ex3' (case2 x) = {!   !} --不可能


ex4' : {A B : Set} → ( A ∧ B ) →   A ∨ B   
ex4' ⟪ a , b ⟫ = case1 a

ex5 :  {A B C : Set} →  (( A → C ) ∨ ( B  → C ) ) → ( ( A ∧  B ) → C )
ex5 = ?

data ⊥ : Set where

⊥-elim : {A : Set } →  ⊥ →  A
⊥-elim ()

¬_ : Set → Set
¬ A = A → ⊥

record PetResearch ( Cat Dog Goat Rabbit : Set ) : Set where
     field
        fact1 : ( Cat ∨ Dog ) → ¬ Goat
        fact2 : ¬ Cat →  ( Dog ∨ Rabbit )
        fact3 : ¬ ( Cat ∨ Goat ) →  Rabbit

postulate
     lem : (a : Set) → a ∨ ( ¬ a )

module tmp ( Cat Dog Goat Rabbit : Set ) (p :  PetResearch  Cat Dog Goat Rabbit ) where

    open PetResearch

    problem0 : Cat ∨ Dog ∨ Goat ∨ Rabbit
    problem0 with lem Cat  | lem Goat
    ... | case1 cat | y = case1 (case1 (case1 cat))
    ... | case2 x | case1 goat = case1 (case2 goat)
    ... | case2 ¬cat | case2 ¬goat = case2 (fact3 p lemma1 ) where
       lemma1 : ¬ (Cat ∨ Goat)
       lemma1 (case1 cat) = ¬cat cat
       lemma1 (case2 goat) = ¬goat goat

    problem2 : Goat → Rabbit
    problem2 g with lem Cat
    ... | case1 cat = ⊥-elim ((fact1 p (case1 cat)) g)
    ... | case2 ¬cat = lemma2 (fact2 p ¬cat) where
      lemma2 : (Dog ∨ Rabbit) → Rabbit
      lemma2 (case1 dog) = ⊥-elim ((fact1 p (case2 dog)) g)
      lemma2 (case2 rabbit) = rabbit

data Nat : Set where
  zero : Nat
  suc  : Nat →  Nat

one : Nat
one = suc zero

five : Nat
five = suc (suc (suc (suc (suc zero))))

add : ( a b : Nat ) → Nat
add zero x = x
add (suc x) y = suc ( add x y )

data _≡_ {A : Set } : ( x y : A ) → Set where
  refl : {x : A} → x ≡ x

test11 : add one five ≡ suc five
test11 = refl

mul : ( a b : Nat ) → Nat
mul zero x = zero
mul (suc x) y = add y (mul x y)

ex6 : Nat
ex6 = mul ( suc ( suc zero)) (suc ( suc ( suc zero)) )

ex7 : mul ( suc ( suc zero)) (suc ( suc ( suc zero)) ) ≡  suc (suc (suc (suc (suc (suc zero)))))
ex7 = refl

data Three : Set where
  t1 : Three
  t2 : Three
  t3 : Three

open Three

infixl 110 _∨_ 

data 3Ring : (dom cod : Three) → Set where
   r1 : 3Ring t1 t2
   r2 : 3Ring t2 t3
   r3 : 3Ring t3 t1

data connected { V : Set } ( E : V -> V -> Set ) ( x y : V ) : Set  where
   direct :   E x y -> connected E x y
   indirect :  { z : V  } -> E x z  ->  connected {V} E z y -> connected E x y

dag :  { V : Set } ( E : V -> V -> Set ) →  Set
dag {V} E =  ∀ (n : V)  →  ¬ ( connected E n n )

lemma : ¬ (dag 3Ring )
lemma  = λ f →
   let c : connected 3Ring t1 t1
       c = indirect r1 (indirect r2 (direct r3))
   in f t1 c

--   t1 → t2 → t3
--
data 3Line : (dom cod : Three) → Set where
   line1 : 3Line t1 t2
   line2 : 3Line t2 t3

lemma1 : dag 3Line
lemma1 t1 (direct ())
lemma1 t1 (indirect line1 (direct()))
lemma1 t1 (indirect line1 (indirect line2 (direct ())))
