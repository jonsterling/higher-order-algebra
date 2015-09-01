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
    pos : ∐ O shp → Set i
    nxt : ∐ (∐ O shp) pos → I
open _▹_ public

-- extension functors

⟦_⟧ : ∀ {i} {I O : Set i} → I ▹ O → I [ 𝔓 ]→ O
⟦ 𝔠 ⟧ φ o =
  ∐ (shp 𝔠 o) λ sh →
  Π (pos 𝔠 (o , sh)) λ po →
  φ (nxt 𝔠 ((o , sh) , po))

-- trees

data ⟪_⟫ {i} {O : Set i} (𝔠 : O ▹ O) (o : O) : Set i where
  into : ⟦ 𝔠 ⟧ ⟪ 𝔠 ⟫ o → ⟪ 𝔠 ⟫ o

-- modalities

□ : ∀ {I O X} → (𝔠 : I ▹ O) → ∐ I X ▹ ∐ O (⟦ 𝔠 ⟧ X)
□ 𝔠 =
  ! ⊤
  ◃ pos 𝔠 ⋘ ⟨ id × fst ⟩ ⋘ fst
  $ (λ { (((o , sh , k) , _) , po) → nxt 𝔠 ((o , sh) , po) , k po })

◇ : ∀ {I O X} → (𝔠 : I ▹ O) → ∐ I X ▹ ∐ O (⟦ 𝔠 ⟧ X)
◇ 𝔠 =
  pos 𝔠 ⋘ ⟨ id × fst ⟩
  ◃ ! ⊤
  $ (λ { (((o , sh , k) , po) , _) → nxt 𝔠 ((o , sh) , po) , k po })

-- Jacobians

𝒥 : ∀ {I O : Set₀} → I ▹ O → I ▹ (O × I)
𝒥 𝔠 = record
  { shp = λ { (o , i) → ∐[ s ∶ shp 𝔠 o ] inv (λ x → nxt 𝔠 ((o , s) , x)) i }
  ; pos = λ { ((o , ._) , sh , po , refl) → pos 𝔠 (o , sh) - po }
  ; nxt = λ { (((o , ._) , sh , _ , refl) , po′ , _) → nxt 𝔠 ((o , sh) , po′) }
  }

plug : ∀ {I O : Set₀} {i o X} (𝔠 : I ▹ O)
  → Π[ s ∶ ∐ O (shp 𝔠) ] Π[ p₀ ∶ pos 𝔠 s ] Π[ p₁ ∶ pos 𝔠 s ] Dec (p₀ ≡ p₁)
  → X i → ⟦ 𝒥 𝔠 ⟧ X (o , i) → ⟦ 𝔠 ⟧ X o
plug {o = o} {X = X} 𝔠 eq? x ((sh , po , refl) , k) = sh , aux where
  aux : Π[ po' ∶ pos 𝔠 (o , sh) ] X (nxt 𝔠 ((o , sh) , po'))
  aux po' with eq? _ po po'
  aux po' | false , φ = k (po' , φ)
  aux ._ | true , refl = x

-- zippers

𝒵 : ∀ {I : Set₀} → I ▹ I → (I × I) ▹ (I × I)
𝒵 {I = I} 𝔠 = record
  { shp = λ { (ir , ih) → ir ≡ ih + ∐[ ip ∶ I ] ⟦ 𝒥 𝔠 ⟧ ⟪ 𝔠 ⟫ (ip , ih) }
  ; pos = λ
    { (_ , false , _) → ⊥
    ; (_ , true , _) → ⊤
    }
  ; nxt = λ
    { ((_ , false , _) , ())
    ; (((ir , ih) , true , ip , _) , _) → ir , ip }
  }

zip : ∀ {I : Set₀} {ir ih} (𝔠 : I ▹ I)
  → Π[ s ∶ ∐ I (shp 𝔠) ] Π[ p₀ ∶ pos 𝔠 s ] Π[ p₁ ∶ pos 𝔠 s ] Dec (p₀ ≡ p₁)
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
  shp′ z = ⊤
  shp′ (s n) = A

  pos′ : ∐ Nat shp′ → Set₀
  pos′ (z , _) = ⊥
  pos′ (s n , _) = ⊤

  nxt′ : ∐ (∐ Nat shp′) pos′ → Nat
  nxt′ ((z , _) , ())
  nxt′ ((s n , _) , _) = n

nil : ∀ {A} → ⟪ VecC A ⟫ z
nil = into (_ , λ())

con : ∀ {A n}
  → A
  → ⟪ VecC A ⟫ n
  → ⟪ VecC A ⟫ (s n)
con x xs = into (x , ! xs)

decVecPos : {A : Set₀}
  → Π[ s ∶ ∐ Nat (shp (VecC A)) ]
    Π[ p₀ ∶ pos (VecC A) s ]
    Π[ p₁ ∶ pos (VecC A) s ]
    Dec (p₀ ≡ p₁)
decVecPos (z , _) () _
decVecPos (s fst , snd) tt tt = true , refl
