module lambda ( A B : Set) (a : A ) (b : B ) where

--   λ-intro 
--
--      A
--   -------- id
--      A
--   -------- λ-intro ( =  λ ( x : A ) → x )
--    A → A 

A→A : A → A 
A→A = λ ( x : A ) → x

A→A'' : A → A 
A→A'' = λ x  → x

A→A' : A → A 
A→A' x = x

--      A
--  --------- λ-intro ( = λ ( x : A ) → x ) 
--    A → A

lemma2 : (A : Set ) →  A → A   --  これは  A → ( A  → A ) とは違う
lemma2 x = λ x → x

lemma3 : {A B : Set } → B → ( A → B )  -- {} implicit variable
lemma3  b = λ _ → b    -- _ anonymous variable

-- λ-intro 
--
--    a :  A
--     :              f : A → B
--    b :  B 
--  ------------- f
--    A → B

--   λ-elim
--
--     a : A     f : A → B
--   ------------------------ λ-elim 
--          f a :  B      

→elim : A → ( A → B ) → B
→elim a f = f a 

ex1 : {A B : Set} → Set 
ex1 {A} {B} = ( A → B ) → A → B -- ( A → B ) → A → B

ex2 : {A : Set} → Set 
ex2 {A}  =  A → ( A  → A )

--
--      A
--  ---------
--    A → A
--

proof2 : {A : Set } → ex2 {A}
proof2 {A} = p1  where
  p1 : { A : Set } → A → A → A      --- ex2 {A} を C-C C-N する
  p1 = λ x y → x

--  [A]₁     [A]₂       --引数 x : A と y : A をそれぞれ [A]₁ と [A]₂ として仮定
--  ------------------ (₂) λ-elim
--      A
--  ------------------ (₁) λ-intro
--    A → A → A


ex3 :  A → B     -- インチキの例
ex3 a = b

ex4 : {A B : Set} → A → (B → B)  -- 仮定を無視してる
ex4 {A}{B} a b = b

---           [A]₁               not used   --- a
---         ────────────────────
---                 [B]₂                    --- b
---         ──────────────────── (₂)
---             B → B
---         ──────────────────── (₁)  λ-intro
---              A → (B → B) 


ex4' :  A → (B → B)   -- インチキできる / 仮定を使える
ex4'  = λ a b → b

-- λ-intro 
--
--    a :  A
--     :     
--    b :  B 
--  ------------- f
--      A

ex5 : {A B : Set} → A → B → A
ex5 = λ a b → a

--
--       Range
--  -----------------
--   Domain → Range
--


postulate
  Domain : Set   --  Range Domain : Set
  Range : Set    -- codomain     Domain → Range, coRange ← coDomain
  r : Range 

ex6 : Domain → Range
ex6 a = r


---                   A → B
--                     :
---                   A → B
---         ─────────────────────────── 
---              ( A → B ) → A → B
---
---              [A]₁     [A → B ]₂
---         ───────────────────────────  λ-elim
---                    B
---         ───────────────────────────  ₁
---                   A → B
---         ───────────────────────────  ₂
---              ( A → B ) → A → B

--
--  上の二つの図式に対応する二つの証明に対応するラムダ項がある
--
ex11 : ( A → B ) → A → B
ex11  x = λ a → x a 

ex12 : (A B : Set) → ( A → B ) → A → B
ex12 = λ a b f x → f x


--
--             A
--             :
--             B 
--  ------------------------
--           A → B 
--  ------------------------
--     ( A → B ) → A → B 
--

ex13 : {A B : Set} → ( A → B ) → A → B
ex13 {A} {B} f a = f a

--
--    A → B
--  ----------
--    A → B
--

ex14 : {A B : Set} → ( A → B ) → A → B
ex14 x a = x a


   