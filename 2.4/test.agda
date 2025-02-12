module test where

open import Data.Nat 
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import logic

-- data _<=_ : ℕ → ℕ → Set where
--  z<=n : {x : ℕ} → zero <= x
--  s<=s : {x y : ℕ} → x <= y → suc x <= suc y

-- hint : it has two inputs, use recursion
nat-<> : { x y : ℕ } → x < y → y < x → ⊥
nat-<>   (s≤s x<y) (s≤s y<x) = nat-<> x<y y<x

-- hint : use recursion
nat-<≡ : { x : ℕ } → x < x → ⊥
nat-<≡ (s≤s x<x) = nat-<≡ x<x

-- hint : use refl and recursion
nat-≡< : { x y : ℕ } → x ≡ y → x < y → ⊥
nat-≡< refl (s≤s x<y) = nat-≡< refl x<y

¬a≤a : {la : ℕ} → suc la ≤ la → ⊥
¬a≤a (s≤s lt) = ¬a≤a lt

-- hint : make case with la first
a<sa : {i : ℕ} → i < suc i 
a<sa {zero} = s≤s z≤n
a<sa {suc i} =  s≤s a<sa 

-- hint  : ¬ has an input, use recursion
=→¬< : {x : ℕ  } → ¬ ( x < x )
=→¬< = λ x<x → nat-<≡ x<x

-- hint : two inputs, try nat-<>
>→¬< : {x y : ℕ  } → (x < y ) → ¬ ( y < x )
>→¬< = λ x<y y<x → nat-<> x<y y<x


¬x<zero : { x : ℕ } → x < zero → ⊥
¬x<zero ()

-- hint : make cases on all arguments. return case1 or case2
-- hint : use with on suc case
<-∨ : { x y : ℕ } → x < suc y → ( (x ≡ y ) ∨ (x < y) )
<-∨ {x = zero} {y = zero} _ = case1 refl
<-∨ {x = zero} {y = suc y} _ = case2 (s≤s z≤n)
<-∨ {x = suc x} {y = zero} p = ⊥-elim (¬x<zero (s<s⁻¹ p) )
<-∨ {x = suc a} {y = suc b} p with <-∨ (s<s⁻¹ p)
... | case1 eq = case1 (cong suc eq)
... | case2 lt = case2 (s≤s lt)

max : (x y : ℕ) → ℕ
max zero y = y
max x zero = x
max (suc x) (suc y) = suc (max x y)

sum :  (x y : ℕ) → ℕ
sum zero y = y
sum (suc x) y = suc ( sum x y )

sum' :  (x y : ℕ) → ℕ
sum' x zero = x
sum' x (suc y) = suc (sum' x y)

sum-sym0 :  {x y : ℕ} → sum x y ≡ sum' y x
sum-sym0 {zero} {zero} = refl
sum-sym0 {suc x} {y} = cong (λ k → suc k ) (sum-sym0 {x} {y})
sum-sym0 {zero} {y}  = refl

sum-6 : sum 3 4 ≡ 7
sum-6 = refl

sum1 : (x y : ℕ) → sum x (suc y)  ≡ suc (sum x y )
sum1 zero y = refl
sum1 (suc x) y = let open ≡-Reasoning in 
  begin
    suc (sum x (suc y))
  ≡⟨ cong suc (sum1 x y) ⟩
    suc (suc (sum x y))
  ∎


sum0 : (x : ℕ) → sum 0 x  ≡ x
sum0 zero = refl
sum0 (suc x) = refl 

sum-zero : (x : ℕ) → sum x zero ≡ x
sum-zero zero = refl
sum-zero (suc x) = cong suc (sum-zero x)

sum-sym : (x y : ℕ) → sum x y ≡ sum y x
sum-sym zero y = sym (sum-zero y)
sum-sym (suc x) y = let open ≡-Reasoning in 
  begin
    sum (suc x) y
  ≡⟨ refl ⟩
    suc (sum x y)
  ≡⟨ cong suc (sum-sym x y) ⟩
    suc (sum y x)
  ≡⟨ sym (sum1 y x) ⟩
    sum y (suc x)
  ∎

sum-assoc : (x y z : ℕ) → sum x (sum y z ) ≡ sum (sum x y)  z 
sum-assoc zero y z = refl
sum-assoc (suc x) y z = let open ≡-Reasoning in
  begin
    suc (sum x (sum y z))
  ≡⟨ cong suc (sum-assoc x y z) ⟩
    suc (sum (sum x y) z)
  ∎


mul :  (x y : ℕ) → ℕ
mul x zero = zero
mul x (suc y) = sum x ( mul x y )

mulr :  (x y : ℕ) → ℕ
mulr zero y = zero
mulr (suc x) y = sum y ( mulr x y )

mul-sym1 : {x y : ℕ } → mul x y ≡ mulr y x
mul-sym1 {zero} {zero} = refl
mul-sym1 {zero} {suc y} = let open ≡-Reasoning in
  begin
     mul zero (suc y)
   ≡⟨⟩
     sum 0 (mul 0 y)
   ≡⟨ cong (λ k → sum 0 k ) (mul-sym1 {0} {y}) ⟩
     mulr (suc y) zero
   ∎ 

mul-sym1 {x} {suc y} = let open ≡-Reasoning in
  begin
    mul x (suc y)
  ≡⟨⟩
    sum x (mul x y)
  ≡⟨ cong (λ k → sum x k) (mul-sym1 {x} {y}) ⟩
    mulr (suc y) x
   ∎
mul-sym1 {suc x} {zero} = refl

mul-9 : mul 3 4 ≡ 12
mul-9 = refl

mul-distr1 : (x y : ℕ) → mul x (suc y) ≡ sum x ( mul x y )
mul-distr1 x y = let open ≡-Reasoning in
  begin
    mul x (suc y)
  ≡⟨⟩
    sum x (mul x y)
   ∎



mul-sym0 : (x : ℕ) → mul zero x  ≡ mul x zero 
mul-sym0 zero = refl
mul-sym0 (suc x) = let open ≡-Reasoning in
  begin
    mul zero (suc x)
  ≡⟨ mul-distr1 zero x ⟩
    sum zero (mul zero x)
  ≡⟨ ( mul-sym0 x) ⟩
    zero
  ∎

mul-sym : (x y : ℕ) → mul x y  ≡ mul y x
mul-sym zero zero = refl
mul-sym x zero = sym (mul-sym0 x)
mul-sym zero y = mul-sym0 y
mul-sym (suc x) (suc y) = let open ≡-Reasoning in
  begin
    mul (suc x) (suc y) 
  ≡⟨⟩
    sum (suc x) (mul (suc x) y)
  ≡⟨ cong (λ k → sum (suc x) k) (mul-sym (suc x) y) ⟩
    sum (suc x) (sum y (mul y x))
  ≡⟨ sum-assoc (suc x) y (mul y x) ⟩
    sum (sum (suc x) y) (mul y x)
  ≡⟨ cong (λ k → sum (sum (suc x) y) k ) (mul-sym y x)⟩
    sum (sum (suc x) y) (mul x y)
  ≡⟨ cong (λ k → sum k (mul x y) ) (sum-sym (suc x) y) ⟩
    sum (sum y (suc x)) (mul x y)
  ≡⟨ cong (λ k → sum k (mul x y)) (sum1 y x) ⟩
    sum (suc (sum y x)) (mul x y)
  ≡⟨ cong (λ k → sum (suc k) (mul x y) ) (sum-sym y x) ⟩
    sum (suc (sum x y)) (mul x y)
  ≡⟨ cong (λ k → sum k (mul x y)) (sym (sum1 x y)) ⟩
    sum (sum x (suc y)) (mul x y)
  ≡⟨ cong (λ k → sum k (mul x y)) (sum-sym x (suc y)) ⟩
    sum (sum (suc y) x) (mul x y)
  ≡⟨ sym (sum-assoc (suc y) x (mul x y)) ⟩
    sum (suc y) (sum x (mul x y))
  ≡⟨ cong (λ k → sum (suc y) k) (mul-sym x (suc y)) ⟩
    sum (suc y) ( mul (suc y) x )
  ≡⟨⟩
    mul (suc y) (suc x)
  ∎

mul-distr : (y z w : ℕ) → sum (mul y z) ( mul w z ) ≡ mul (sum y w)  z
mul-distr zero zero w = refl
mul-distr y zero w = let open ≡-Reasoning in
  begin
    sum (mul y zero) (mul w zero)
  ≡⟨⟩
    sum zero zero  
  ≡⟨⟩
    mul (sum y w) zero  
  ∎


mul-distr zero (suc z) w = let open ≡-Reasoning in
  begin
    sum (mul zero (suc z)) (mul w (suc z))
  ≡⟨ cong (λ k → sum k (mul w (suc z))) (mul-sym zero (suc z)) ⟩
    sum (mul (suc z) zero) (mul w (suc z))
  ≡⟨ sum0 (mul w (suc z)) ⟩
    mul w (suc z)
  ≡⟨ cong (λ k → sum k (mul k z)) (sym (sum0 w)) ⟩
    sum (sum zero w) (mul (sum zero w) z)
  ≡⟨⟩
    mul (sum zero w) (suc z)
  ∎


mul-distr (suc y) (suc z) w = let open ≡-Reasoning in
  begin
    sum (mul (suc y) (suc z)) (mul w (suc z))
  ≡⟨ sum-sym (mul (suc y) (suc z)) (mul w (suc z)) ⟩
    sum (mul w (suc z)) (mul (suc y) (suc z))
  ≡⟨ sym (sum-assoc w (mul w z) (mul (suc y) (suc z))) ⟩
    sum w ( sum (mul w z) (mul (suc y) (suc z)) )
  ≡⟨ cong (λ k → sum w k) ( sum-sym (mul w z) (mul (suc y) (suc z)) ) ⟩
    sum w ( sum (mul (suc y) (suc z)) (mul w z) )
  ≡⟨ cong (λ k → sum w k) (sym (sum-assoc (suc y) (mul (suc y) z) (mul w z))) ⟩
    sum w ( sum (suc y) (sum (mul (suc y) z) (mul w z)) )
  ≡⟨ sum-assoc w (suc y) (sum (mul (suc y) z) (mul w z)) ⟩ 
    sum (sum w (suc y)) (sum (mul (suc y) z) (mul w z))
  ≡⟨ cong (λ k → sum k (sum (mul (suc y) z) (mul w z))) (sum-sym w (suc y)) ⟩
    sum (sum (suc y) w) (sum (mul (suc y) z) (mul w z))
  ≡⟨ cong (λ k → sum (sum (suc y) w) k) (mul-distr (suc y) z w) ⟩
    sum (sum (suc y) w) (mul (sum (suc y) w) z)
  ≡⟨⟩
    mul (sum (suc y) w) (suc z)
  ∎

mul-assoc : (x y z : ℕ) → mul x (mul y z ) ≡ mul (mul x y)  z 
mul-assoc zero zero zero = refl
mul-assoc zero zero z = let open ≡-Reasoning in
  begin
    mul zero (mul zero z)
  ≡⟨ cong (λ k → mul zero k) (mul-sym zero z) ⟩
    mul zero (mul z zero)
  ≡⟨⟩
    mul zero zero
  ≡⟨⟩
    mul z zero
  ≡⟨ mul-sym z zero ⟩
    mul zero z
  ≡⟨⟩
    mul (mul zero zero) z
  ∎
mul-assoc x zero zero = let open ≡-Reasoning in
  begin
    mul x (mul zero zero)
  ≡⟨⟩
    mul x zero
  ≡⟨⟩
    mul (mul x zero) zero
  ∎
mul-assoc zero y zero = let open ≡-Reasoning in
  begin
    mul zero (mul y zero)
  ≡⟨⟩
    mul zero zero
  ≡⟨⟩
    mul (mul y zero) zero
  ≡⟨ cong (λ k → mul k zero) (mul-sym y zero) ⟩
    mul (mul zero y) zero
  ∎
mul-assoc zero y z = let open ≡-Reasoning in
  begin
    mul zero (mul y z)
  ≡⟨ mul-sym zero (mul y z) ⟩
    mul (mul y z) zero
  ≡⟨⟩
    mul z zero
  ≡⟨ mul-sym z zero ⟩
    mul zero z
  ≡⟨⟩
    mul (mul y zero) z
  ≡⟨ cong (λ k → mul k z) (mul-sym y zero) ⟩
    mul (mul zero y) z
  ∎
mul-assoc x y zero = let open ≡-Reasoning in
  begin
    mul x (mul y zero)
  ≡⟨⟩
    mul x zero
  ≡⟨⟩
    mul (mul x y) zero
  ∎
mul-assoc x zero z = let open ≡-Reasoning in
  begin
    mul x (mul zero z)
  ≡⟨ cong (λ k → mul x k) (mul-sym zero z) ⟩
    mul x (mul z zero)
  ≡⟨⟩
    mul z zero
  ≡⟨ mul-sym z zero ⟩
    mul zero z
  ≡⟨⟩
    mul (mul x zero) z
  ∎
mul-assoc x y (suc z) = let open ≡-Reasoning in
  begin
    mul x (mul y (suc z))
  ≡⟨ mul-sym x (mul y (suc z)) ⟩
    mul (mul y (suc z)) x
  ≡⟨⟩
    mul (sum y (mul y z)) x  -- mul y (suc z) = sum y (mul y z) より
  ≡⟨ sym (mul-distr y x (mul y z)) ⟩
    sum (mul y x) (mul (mul y z) x)
  ≡⟨ cong (λ k → sum (mul y x) k) (mul-sym (mul y z) x) ⟩
    sum (mul y x) (mul x (mul y z))
  ≡⟨ cong (λ k → sum k (mul x (mul y z))) (mul-sym y x) ⟩
    sum (mul x y) (mul x (mul y z))
  ≡⟨ cong (λ k → sum (mul x y) k) (mul-assoc x y z) ⟩
    sum (mul x y) (mul (mul x y) z)
  ≡⟨⟩
    mul (mul x y) (suc z)
  ∎

evenp : (x : ℕ) → Bool
evenp zero = true
evenp (suc zero) = false
evenp (suc (suc x)) = evenp x
 