{-
Name: Duncan Enzmann
Date: 10/31/2019

Collaboration & Resources Statement:
«Help Sami Connolly on E3 with using {n = n} Help on E6 in which order to rewrite by (invol and distr)»
-}

---------------
-- LOGISTICS --
---------------

-- To submit the assignment, upload your solution to Gradescope as a
-- single .agda file.
--
-- Make sure you write your name, the date, and your collaboration
-- & Resources statement above, as indicated by the course
-- collaboration and resources policy:
--
--     Collaboration on the high-level ideas and approach on assignments
--     is encouraged. Copying someone else's work is not allowed. Copying
--     solutions from an online source is not allowed. Any collaboration
--     or online resources, even if used only at a high level, must be
--     declared when you submit your assignment. Every assignment must
--     include a collaboration and resources statement. E.g., “I discussed
--     high-level strategies for solving problem 2 and 5 with Alex; I
--     found this stackoverflow post helpful while working on problem 3 ”
--     Students caught copying work are eligible for immediate failure of
--     the course and disciplinary action by the University. All academic
--     integrity misconduct will be treated according to UVM's Code of
--     Academic Integrity.
--
-- This assignment consists of a LIB section which contains relevant
-- definitions and lemmas which you should refer to throughout the
-- assignment, and an ASSIGNMENT section which contains definitions
-- and lemmas with “holes” in them. *If you only change the code
-- within the holes and your entire assignment compiles without
-- errors, you are guaranteed 100% on the assignment.*

---------
-- LIB --
---------

-- equality --

infix 8 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  ↯ : x ≡ x
  
{-# BUILTIN EQUALITY _≡_ #-}

-- booleans --

data 𝔹 : Set where
  T : 𝔹
  F : 𝔹

-- naturals --

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 15 _+_
_+_ : ℕ → ℕ → ℕ
Z    + n  =  n
(S m) + n  =  S (m + n)

infixl 16 _×_
_×_ : ℕ → ℕ → ℕ
Z × _ = Z
S m × n = n + m × n

-- order --

infix 8 _≤_
data _≤_ : ℕ → ℕ → Set where
  Z : ∀ {n} → Z ≤ n
  S : ∀ {m n} → m ≤ n → S m ≤ S n

infix 8 _<_
data _<_ : ℕ → ℕ → Set where
  Z : ∀ {n} → Z < S n
  S : ∀ {m n} → m < n → S m < S n

data ≤! : Set where
  [≤] : ≤!
  [>] : ≤!

infix 8 _≤⋆!_
data _≤⋆!_ (m n : ℕ) : Set where
  [≤] : m ≤ n → m ≤⋆! n
  [>] : n < m → m ≤⋆! n

data ⋚! : Set where
  [<] : ⋚!
  [≡] : ⋚!
  [>] : ⋚!

infix 8 _⋚⋆!_
data _⋚⋆!_ (m n : ℕ) : Set where
  [<] : m < n → m ⋚⋆! n
  [≡] : m ≡ n → m ⋚⋆! n
  [>] : n < m → m ⋚⋆! n

_≤?_ : ℕ → ℕ → ≤!
Z ≤? n = [≤]
S m ≤? Z = [>]
S m ≤? S n = m ≤? n

_⋚?_ : ℕ → ℕ → ⋚!
Z ⋚? Z = [≡]
Z ⋚? S n = [<]
S m ⋚? Z = [>]
S m ⋚? S n = m ⋚? n

-- type-level connectives --

data 𝟘 : Set where

infixr 9 ¬_
¬_ : Set → Set
¬ A = A → 𝟘

data 𝟙 : Set where
  • : 𝟙

infix 5 _∨_
data _∨_ (A B : Set) : Set where
  Inl : A → A ∨ B
  Inr : B → A ∨ B

infix 6 _∧_
record _∧_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    π₁ : A
    π₂ : B
open _∧_

data existential (A : Set) (B : A → Set) : Set where
  ⟨∃_,_⟩ : ∀ (x : A) → B x → existential A B

-- lists --

infixr 20 _∷_
data list (A : Set) : Set where
  [] : list A
  _∷_ : A → list A → list A

length : ∀ {A : Set} → list A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs

infix 8 _≤[first]_
data _≤[first]_ (m : ℕ) : list ℕ → Set where
  [] : m ≤[first] []
  ⟨_⟩ : ∀ {n ns}
    → m ≤ n
    → m ≤[first] n ∷ ns

data sorted : list ℕ → Set where
  [] : sorted []
  _∷_ : ∀ {x xs}
    → x ≤[first] xs
    → sorted xs
    → sorted (x ∷ xs)

infix 8 _≤[all]_
data _≤[all]_ (x : ℕ) : list ℕ → Set where
  [] : x ≤[all] []
  _∷_  : ∀ {y : ℕ} {ys : list ℕ}
    → x ≤ y
    → x ≤[all] ys
    → x ≤[all] (y ∷ ys)

infixl 16 _⧺_
_⧺_ : ∀ {A : Set} → list A → list A → list A
[] ⧺ ys = ys
(x ∷ xs) ⧺ ys = x ∷ (xs ⧺ ys)

-- functions -- 

id : ∀ {A : Set} → A → A
id x = x

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

-- POSTULATES --

infixl 18 _⊚[≡]_
infixl 18 _⊚[≤]_
infixl 17 _⋈[≤]_

postulate
  _⊚[≡]_ : ∀ {A} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
  ◇[≡] : ∀ {A} {x y : A} → x ≡ y → y ≡ x

  runit[+] : ∀ (m : ℕ) → m + 0 ≡ m
  assoc[+] : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
  commu[+] : ∀ (m n : ℕ) → m + n ≡ n + m

  lmono[+] : ∀ {m n} p → m ≤ n → m + p ≤ n + p
  rmono[+] : ∀ m {n p} → n ≤ p → m + n ≤ m + p

  runit[×] : ∀ (m : ℕ) → m × 1 ≡ m
  rzero[×] : ∀ (m : ℕ) → m × 0 ≡ 0
  assoc[×] : ∀ (m n p : ℕ) → m × (n × p) ≡ (m × n) × p
  commu[×] : ∀ (m n : ℕ) → m × n ≡ n × m
  ldist[×] : ∀ (m n p : ℕ) → m × (n + p) ≡ m × n + m × p
  rdist[×] : ∀ (m n p : ℕ) → (m + n) × p ≡ m × p + n × p

  runit[⧺] : ∀ (ms : list ℕ) → ms ⧺ [] ≡ ms
  assoc[⧺] : ∀ (ms ns ps : list ℕ) → ms ⧺ (ns ⧺ ps) ≡ (ms ⧺ ns) ⧺ ps

  xRx[≤] : ∀ (m : ℕ) → m ≤ m
  _⊚[≤]_ : ∀ {m n p : ℕ} → n ≤ p → m ≤ n → m ≤ p
  _⋈[≤]_ : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n

  ¬xRx[<] : ∀ {m : ℕ} → m < m → 𝟘
  _⊚[<]_ : ∀ {m n p : ℕ} → n < p → m < n → m < p
  _⊚[</≤]_ : ∀ {m n p : ℕ} → n < p → m ≤ n → m < p
  _⊚[≤/<]_ : ∀ {m n p : ℕ} → n ≤ p → m < n → m < p
  _¬◇_ : ∀ {m n : ℕ} → m < n → n < m → 𝟘

  s[≤] : ∀ (m : ℕ) → m ≤ S m
  s[<] : ∀ (m : ℕ) → m < S m

  to[</≤] : ∀ {m n : ℕ} → m < n → S m ≤ n
  fr[</≤] : ∀ {m n : ℕ} → S m ≤ n → m < n

  to[≤/<] : ∀ {m n : ℕ} → m ≤ n → m < S n
  fr[≤/<] : ∀ {m n : ℕ} → m < S n → m ≤ n

  wk[<] : ∀ {m n : ℕ} → m < n → m ≤ n
  in[≤] : ∀ {m n : ℕ} → m ≤ n → m < n ∨ m ≡ n

  snd[≤?/≤] : ∀ {m n : ℕ} → m ≤? n ≡ [≤] → m ≤ n
  snd[≤?/>] : ∀ {m n : ℕ} → m ≤? n ≡ [>] → n < m

  cmp[≤?/≤] : ∀ {m n : ℕ} → m ≤ n → m ≤? n ≡ [≤]
  cmp[≤?/>] : ∀ {m n : ℕ} → n < m → m ≤? n ≡ [>]

  snd[⋚?/<] : ∀ {m n : ℕ} → m ⋚? n ≡ [<] → m < n
  snd[⋚?/≡] : ∀ {m n : ℕ} → m ⋚? n ≡ [≡] → m ≡ n
  snd[⋚?/>] : ∀ {m n : ℕ} → m ⋚? n ≡ [>] → n < m

  cmp[⋚?/<] : ∀ {m n : ℕ} → m < n → m ⋚? n ≡ [<]
  cmp[⋚?/≡] : ∀ {m n : ℕ} → m ≡ n → m ⋚? n ≡ [≡]
  cmp[⋚?/>] : ∀ {m n : ℕ} → n < m → m ⋚? n ≡ [>]

  _≤⋆_ : ∀ (m n : ℕ) → m ≤⋆! n
  _⋚⋆_ : ∀ (m n : ℕ) → m ⋚⋆! n

-- well-founded --

data acc (x : ℕ) : Set where
  Acc : (∀ {y} → y < x → acc y) → acc x

acc[<] : ∀ {m} (n : ℕ) → m < n → acc m
acc[<] Z ()
acc[<] (S n) Z = Acc λ where ()
acc[<] (S n) (S ε) = Acc λ where ε′ → (acc[<] n) ( to[</≤] ε ⊚[≤/<] ε′)

wf[<] : ∀ (n : ℕ) → acc n
wf[<] n = Acc (acc[<] n)

-----------------
-- DEFINITIONS --
-----------------

data vec (A : Set) : ℕ → Set where
  [] : vec A Z
  _∷_ : ∀ {n} → A → vec A n → vec A (S n)

vec[_] : ℕ → Set → Set
vec[ n ] A = vec A n
{-# DISPLAY vec A n = vec[ n ] A #-}

pattern [_] a = a ∷ []
pattern [_,_] a b = a ∷ [ b ]
pattern [_,_,_] a b c = a ∷ [ b , c ]
pattern [_,_,_,_] a b c d = a ∷ [ b , c , d ]
pattern [_,_,_,_,_] a b c d e = a ∷ [ b , c , d , e ]
pattern [_,_,_,_,_,_] a b c d e f = a ∷ [ b , c , d , e , f ]
pattern [_,_,_,_,_,_,_] a b c d e f g = a ∷ [ b , c , d , e , f , g ]
pattern [_,_,_,_,_,_,_,_] a b c d e f g h = a ∷ [ b , c , d , e , f , g , h ]
pattern [_,_,_,_,_,_,_,_,_] a b c d e f g h i = a ∷ [ b , c , d , e , f , g , h , i ]
pattern [_,_,_,_,_,_,_,_,_,_] a b c d e f g h i j = a ∷ [ b , c , d , e , f , g , h , i , j ]

matrix[_,_] : ℕ → ℕ → Set → Set
matrix[ m , n ] A = vec[ m ] (vec[ n ] A)

---------------
-- EXERCISES --
---------------

-- E1: [★☆☆]
-- Define the constant vector: `const[vec]< m > x` should be a vector
-- with `m` elements, all of which are copies of the value `x`
-- HINTS:
-- ‣ define by recursion on `m`
const[vec]<_> : ∀ {A : Set} (m : ℕ) → A → vec[ m ] A
const[vec]< Z > x = []
const[vec]< S m > x = x ∷ (const[vec]< m > x)

_ : const[vec]< 3 > 1 ≡ [ 1 , 1 , 1 ]
_ = ↯

_ : const[vec]< 4 > 2 ≡ [ 2 , 2 , 2 , 2 ]
_ = ↯

-- this is a helper function which lets you omit the length argument
-- `m` to `const[vec]< m > x`
const[vec] : ∀ {A : Set} {m : ℕ} → A → vec[ m ] A
const[vec] x = const[vec]< _ > x

-- notice that the usual cons `(xs ∷ xss)` adds a single row to a
-- matrix vertically

_ : let xs  : vec[ 2 ] ℕ
        xs  = [ 1 , 2 ]

        xss : matrix[ 3 , 2 ] ℕ
        xss = [ [ 3 , 4 ]
              , [ 5 , 6 ]
              , [ 7 , 8 ]
              ]

        yss : matrix[ 1 + 3 , 2 ] ℕ
        yss = [ [ 1 , 2 ]
              , [ 3 , 4 ]
              , [ 5 , 6 ]
              , [ 7 , 8 ]
              ]
    in xs ∷ xss ≡ yss
_ = ↯

-- E2: [★☆☆]
-- Define an operation which adds a single column to a
-- matrix horizontally.
-- HINTS:
-- ‣ define by recursion on both `xs` and `yss`
infixr 20 _⁘_
_⁘_ : ∀ {A : Set} {m n : ℕ} → vec[ m ] A → matrix[ m , n ] A → matrix[ m , S n ] A
[] ⁘ [] = []
(x ∷ xs) ⁘ x₁ ∷ yss = (x ∷ x₁) ∷ xs ⁘ yss

_ : let xs  : vec[ 3 ] ℕ
        xs  = [ 1
              , 2
              , 3
              ]

        xss : matrix[ 3 , 2 ] ℕ
        xss = [ [ 4 , 5 ]
              , [ 6 , 7 ]
              , [ 8 , 9 ]
              ]

        yss : matrix[ 3 , 1 + 2 ] ℕ
        yss = [ [ 1 , 4 , 5 ]
              , [ 2 , 6 , 7 ]
              , [ 3 , 8 , 9 ]
              ]
    in xs ⁘ xss ≡ yss
_ = ↯

-- E3: [★☆☆]
-- Define matrix transpose
-- HINTS:
-- ‣ define by recursion on `xss`
-- ‣ use E2
tr : ∀ {A : Set} {m n : ℕ} → matrix[ m , n ] A → matrix[ n , m ] A
tr {n = n}  [] = const[vec]< n > []
tr (x ∷ xss) =  x ⁘  tr xss

_ : let xss : matrix[ 3 , 2 ] ℕ
        xss = [ [ 1 , 2 ]
              , [ 3 , 4 ]
              , [ 5 , 6 ]
              ]

        yss : matrix[ 2 , 3 ] ℕ
        yss = [ [ 1 , 3 , 5 ]
              , [ 2 , 4 , 6 ]
              ]
    in tr xss ≡ yss
_ = ↯

-- E4: [★☆☆]
-- Prove that the transpose of a constant vector of empty vectors (an
-- “m by 0” matrix) is the empty vector of vectors (a “0 by m” matrix)
-- HINTS:
-- ‣ do induction on `m`
zero[T] : ∀ (A : Set) (m : ℕ) → tr (const[vec]< m > []) ≡ ([] {A = vec[ m ] A})
zero[T] A Z = ↯
zero[T] A (S m) with zero[T] A m
... | IH rewrite IH = ↯

-- E5: [★☆☆]
-- Prove that transpose after adding a new column horizontally is the
-- same as adding a single row vertically after a transpose
-- HINTS:
-- ‣ do induction on `xs` and `yss`
distr[T/⁘] : ∀ {A : Set} {m n : ℕ} (xs : vec[ m ] A) (xss : matrix[ m , n ] A) → tr (xs ⁘ xss) ≡ xs ∷ tr xss
distr[T/⁘] [] [] = ↯
distr[T/⁘] (x ∷ xs) (x₁ ∷ yss) with distr[T/⁘] xs yss
... | IH rewrite IH = ↯

-- E6: [★★☆]
-- Prove that transpose is involutive, that is, transpose of transpose
-- is the identity
-- HINTS:
-- ‣ do induction on `xss` and case analysis on `m`
-- ‣ use E4 and E5
invol[T] : ∀ (A : Set) (m n : ℕ) (xs : matrix[ m , n ] A) → tr (tr xs) ≡ xs
invol[T] A .0 n [] = zero[T] A n
invol[T] A (S m) n (x ∷ xss) with distr[T/⁘] x (tr xss)
... | H rewrite H with invol[T] A m n xss
... | IH rewrite IH = ↯
