module Containers where

open import Agda.Primitive
open import Prelude
open import Indexing

infix 0 _▹_
infix 0 _◃_$_
infix 0 ⟪_⟫

--------------------------------------------------------------------------------
-- Indexed Containers
--------------------------------------------------------------------------------

record _▹_ {i} (I O : Set i) : Set (lsuc i) where
  constructor _◃_$_
  field
    shp : O → Set i
    pos : Σ O shp → Set i
    nxt : Σ (Σ O shp) pos → I
open _▹_ public

-- extension functors

⟦_⟧ : ∀ {i} {I O : Set i} → I ▹ O → I [ 𝔓 ]→ O
⟦ 𝔠 ⟧ φ o =
  Σ (shp 𝔠 o) λ s →
  Π (pos 𝔠 (o , s)) λ p →
  φ (nxt 𝔠 ((o , s) , p))

-- trees

data ⟪_⟫ {i} {O : Set i} (𝔠 : O ▹ O) (o : O) : Set i where
  into : ⟦ 𝔠 ⟧ ⟪ 𝔠 ⟫ o → ⟪ 𝔠 ⟫ o

-- modalities

□ : ∀ {I O X} → (𝔠 : I ▹ O) → Σ I X ▹ Σ O (⟦ 𝔠 ⟧ X)
□ 𝔠 =
  ! ⊤
  ◃ pos 𝔠 ⋘ ⟨ id × fst ⟩ ⋘ fst
  $ (λ { (((o , s , k) , _) , p) → nxt 𝔠 ((o , s) , p) , k p })

◇ : ∀ {I O X} → (𝔠 : I ▹ O) → Σ I X ▹ Σ O (⟦ 𝔠 ⟧ X)
◇ 𝔠 =
  pos 𝔠 ⋘ ⟨ id × fst ⟩
  ◃ ! ⊤
  $ (λ { (((o , s , k) , p) , _) → nxt 𝔠 ((o , s) , p) , k p })

-- Jacobians

𝒥 : ∀ {I O : Set₀} → I ▹ O → I ▹ (O × I)
𝒥 𝔠 = record
  { shp = λ { (o , i) → Σ[ s ∶ shp 𝔠 o ] inv (λ x → nxt 𝔠 ((o , s) , x)) i }
  ; pos = λ { ((o , ._) , s , p , refl) → pos 𝔠 (o , s) - p }
  ; nxt = λ { (((o , ._) , s , _ , refl) , p′ , _) → nxt 𝔠 ((o , s) , p′) }
  }

plug : ∀ {I O : Set₀} {i o X} (𝔠 : I ▹ O)
  → Π[ s ∶ Σ O (shp 𝔠) ] Π[ p₀ ∶ pos 𝔠 s ] Π[ p₁ ∶ pos 𝔠 s ] Dec (p₀ ≡ p₁)
  → X i → ⟦ 𝒥 𝔠 ⟧ X (o , i) → ⟦ 𝔠 ⟧ X o
plug {o = o} {X = X} 𝔠 eq? x ((s , p , refl) , k) = s , aux where
  aux : Π[ p' ∶ pos 𝔠 (o , s) ] X (nxt 𝔠 ((o , s) , p'))
  aux p' with eq? _ p p'
  aux p' | false , φ = k (p' , φ)
  aux ._ | true , refl = x

-- zippers

𝒵 : ∀ {I : Set₀} → I ▹ I → (I × I) ▹ (I × I)
𝒵 {I = I} 𝔠 = record
  { shp = λ { (ir , ih) → ir ≡ ih + Σ[ ip ∶ I ] ⟦ 𝒥 𝔠 ⟧ ⟪ 𝔠 ⟫ (ip , ih) }
  ; pos = λ
    { (_ , false , _) → ⊥
    ; (_ , true , _) → ⊤
    }
  ; nxt = λ
    { ((_ , false , _) , ())
    ; (((ir , ih) , true , ip , _) , _) → ir , ip }
  }

zip : ∀ {I : Set₀} {ir ih} (𝔠 : I ▹ I)
  → Π[ s ∶ Σ I (shp 𝔠) ] Π[ p₀ ∶ pos 𝔠 s ] Π[ p₁ ∶ pos 𝔠 s ] Dec (p₀ ≡ p₁)
  → ⟪ 𝒵 𝔠 ⟫ (ir , ih) → ⟪ 𝔠 ⟫ ih → ⟪ 𝔠 ⟫ ir
zip 𝔠 eq? (into ((false , refl) , _)) t =
  t
zip 𝔠 eq? (into ((true , _ , c) , cz)) t =
  zip 𝔠 eq? (cz tt) (into (plug 𝔠 eq? t c))

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

VecC : (A : Set₀) → Nat ▹ Nat
VecC A = record
  { shp = shp′
  ; pos = pos′
  ; nxt = nxt′
  }
  where
  shp′ : Nat → Set₀
  shp′ ze = ⊤
  shp′ (su n) = A

  pos′ : Σ Nat shp′ → Set₀
  pos′ (ze , _) = ⊥
  pos′ (su n , _) = ⊤

  nxt′ : Σ (Σ Nat shp′) pos′ → Nat
  nxt′ ((ze , _) , ())
  nxt′ ((su n , _) , _) = n

nil : ∀ {A} → ⟪ VecC A ⟫ ze
nil = into (_ , λ())

con : ∀ {A n}
  → A
  → ⟪ VecC A ⟫ n
  → ⟪ VecC A ⟫ (su n)
con x xs = into (x , ! xs)

decVecPos : {A : Set₀}
  → Π[ s ∶ Σ Nat (shp (VecC A)) ]
    Π[ p₀ ∶ pos (VecC A) s ]
    Π[ p₁ ∶ pos (VecC A) s ]
    Dec (p₀ ≡ p₁)
decVecPos (ze , _) () _
decVecPos (su fst , snd) tt tt = true , refl

-- data * : Set where
--   ι : *
--   _⇒_ : * → * → *

-- infixl 5 _▸_
-- data Cx : Set where
--   ε : Cx
--   _▸_ : Cx → * → Cx

-- var : Cx × * ▹ Cx × *
-- var = record
--   { shp = shp′
--   ; pos = pos′
--   ; nxt = nxt′
--   }
--   where
--   shp′ : Cx × * → Set
--   shp′ (ε , τ) = ⊥
--   shp′ (Γ ▸ τ₀ , τ₁) = τ₀ ≡ τ₁

--   pos′ : Σ (Cx × *) shp′ → Set
--   pos′ ((ε , τ) , ())
--   pos′ ((Γ ▸ τ , .τ) , refl) = Cx × *

--   nxt′ : Σ (Σ (Cx × *) shp′) pos′ → Cx × *
--   nxt′ (((ε , _) , ()) , _)
--   nxt′ (((Γ ▸ τ , .τ) , refl) , Γ′ , τ′) = {!!}

-- abs : Cx × * ▹ Cx × *
-- abs = record
--   { shp = shp′
--   ; pos = pos′
--   ; nxt = nxt′
--   }
--   where
--   shp′ : Cx × * → Set
--   shp′ (Γ , τ) = {!!}

--   pos′ : Σ (Cx × *) shp′ → Set
--   pos′ = {!!}

--   nxt′ : Σ (Σ (Cx × *) shp′) pos′ → Cx × *
--   nxt′ = {!!}

-- -- abs : Cx × * ▹ Nat
-- -- abs = record
-- --   { shp = shp′
-- --   ; pos = pos′
-- --   ; nxt = nxt′
-- --   }
-- --   where
-- --   shp′ : Nat → Set
-- --   shp′ ze = ⊤
-- --   shp′ (su _) = ⊥

-- --   pos′ : Σ Nat shp′ → Set
-- --   pos′ = ! (Cx × * × *)

-- --   nxt′ : Σ (Σ Nat shp′) pos′ → Cx × *
-- --   nxt′ ((ze , tt) , Γ , τ₁ , τ₂) = {!!}
-- --   nxt′ ((su _ , ()) , _)

-- -- app : Cx × * ▹ Nat
-- -- app = record
-- --   { shp = shp′
-- --   ; pos = pos′
-- --   ; nxt = nxt′
-- --   }
-- --   where
-- --   shp′ : Nat → Set
-- --   shp′ ze = ⊤
-- --   shp′ (su ze) = ⊤
-- --   shp′ (su (su _)) = ⊥

-- --   pos′ : Σ Nat shp′ → Set
-- --   pos′ = ! (Cx × * × *)

-- --   nxt′ : Σ (Σ Nat shp′) pos′ → Cx × *
-- --   nxt′ ((ze , tt) , Γ , τ₁ , τ₂) = Γ , (τ₁ ⇒ τ₂)
-- --   nxt′ ((su ze , tt) , Γ , τ₁ , τ₂) = Γ , τ₁
-- --   nxt′ ((su (su _) , ()) , _)
