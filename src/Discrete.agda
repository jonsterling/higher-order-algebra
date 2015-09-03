module Discrete where

open import Polynomials
open import Prelude

infix 0 _▸*
infix 5 _⊗_
infix 0 rule[_#_]_⊢_

nat : ∀ {n} → Fin n → Nat
nat z = z
nat (s i) = s (nat i)

_⊗_ : Nat → Set → Set
𝔏 ⊗ 𝔍 = ∐ (Fin 𝔏) (! 𝔍)

match : ∀ {𝔏 𝔍} {𝒞 : Set} → (Fin 𝔏 → (𝔍 → 𝒞)) → (𝔏 ⊗ 𝔍 → 𝒞)
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
  ; bun = 𝔏 ⊗ 𝔍 , ▿
  ; nxt = match π
  }

TCtx = Nat

pattern _▸* Δ = s Δ

-- ----------------
-- Δ, X : * ⊢ X : *

`ν : Pol TCtx TCtx
`ν = rule[ 0 # TCtx ] (λ Δ → Δ ▸*) ⊢ λ
  {()}

-- Δ ⊢ A : *
-- Δ ⊢ B : *
-- -------------
-- Δ ⊢ A ⇒ B : *

`⇒ : Pol TCtx TCtx
`⇒ = rule[ 2 # TCtx ] (λ Δ → Δ) ⊢ λ
  { (z) Δ → Δ
  ; (s z) Δ → Δ
  ; (s s ())
  }

-- Δ, X : * ⊢ A : *
-- ------------------
-- Δ ⊢ ∀ X : *. A : *

`∀ : Pol TCtx TCtx
`∀ = rule[ 1 # TCtx ] (λ Δ → Δ) ⊢ λ
  { (z) Δ → Δ ▸*
  ; (s ())
  }

-- Δ, X : * ⊢ A : *
-- Δ ⊢ B : *
-- ----------------------
-- Δ ⊢ ς(X : *. A; B) : *

`ς : Pol TCtx TCtx
`ς = rule[ 2 # TCtx ] (λ Δ → Δ) ⊢ λ
  { (z) Δ → Δ ▸*
  ; (s z) Δ → Δ
  ; (s s ())
  }
