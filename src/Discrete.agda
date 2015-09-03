module Discrete where

open import Polynomials
open import Prelude

nat : ∀ {n} → Fin n → Nat
nat z = z
nat (s i) = s (nat i)

_⊗_ : Nat → Set → Set
𝔏 ⊗ 𝔍 = ∐ (Fin 𝔏) (! 𝔍)

match : ∀ {𝔏 𝔍} {𝒞 : Set} → (Fin 𝔏 → (𝔍 → 𝒞)) → (𝔏 ⊗ 𝔍) → 𝒞
match 𝔣 (i , x) = 𝔣 i x

▿ : ∀ {𝔏 𝔍} → 𝔏 ⊗ 𝔍 → 𝔍
▿ = snd

rule[_#_]_⊢_
  : ∀ {𝒞 𝒟} 𝔏 𝔍
  → (δ : 𝔍 → 𝒟)
  → (π : Fin 𝔏 → (𝔍 → 𝒞))
  → Pol 𝒞 𝒟
rule[ 𝔏 # 𝔍 ] δ ⊢ π = record
  { Shp = 𝔍
  ; shp = δ
  ; bun = (𝔏 ⊗ 𝔍) , ▿
  ; nxt = match π
  }

TCtx = Nat

-- ----------------
-- Δ, X : * ⊢ X : *

`ν : Pol TCtx TCtx
`ν = rule[ 0 # TCtx ] s ⊢ λ
  {()}

-- Δ ⊢ A : *
-- Δ ⊢ B : *
-- -------------
-- Δ ⊢ A ⇒ B : *

`⇒ : Pol TCtx TCtx
`⇒ = rule[ 2 # TCtx ] id ⊢ λ
  { z → id
  ; (s z) → id
  ; (s (s ()))
  }

-- Δ, X : * ⊢ A : *
-- ------------------
-- Δ ⊢ ∀ X : *. A : *

`∀ : Pol TCtx TCtx
`∀ = rule[ 1 # TCtx ] id ⊢ λ
  { z → s
  ; (s ())
  }

-- Δ, X : * ⊢ A : *
-- Δ ⊢ B : *
-- ----------------------
-- Δ ⊢ ς(X : *. A; B) : *

`ς : Pol TCtx TCtx
`ς = rule[ 2 # TCtx ] id ⊢ λ
  { z → s
  ; (s z) → id
  ; (s (s ()))
  }
