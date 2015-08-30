module Syntax where

infix 0 _⊧_▸_⊢
infixr 0 ,_
infixr 0 _,_
infixr 1 _∷_
infixr 1 _+_
infixr 1 s_
infixl 0 _·_

open import Agda.Primitive

record ∐ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open ∐ public

syntax ∐ A (λ x → B) = ∐[ x ∶ A ] B

,_ : ∀ {a b} {A : Set a} {B : A → Set b} {x} → B x → ∐ A B
, y = _ , y

_×_ : ∀ {a b} → (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = ∐ A λ _ → B

data Nat : Set where
  z : Nat
  s_ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
z + n = n
(s m) + n = s (m + n)

data Fin : Nat → Set where
  z : ∀ {n} → Fin (s n)
  s_ : ∀ {n} → Fin n → Fin (s n)

data Vec {a} (A : Set a) : Nat → Set a where
  [] : Vec A z
  _∷_ : ∀ {n} → (x : A) (xs : Vec A n) → Vec A (s n)

idx : ∀ {a n} {A : Set a} → Vec A n → (Fin n → A)
idx (x ∷ xs) z = x
idx (x ∷ xs) (s i) = idx xs i

record Signature : Set₁ where
  field
    𝒪 : Set₀
    𝔄 : 𝒪 → ∐ Nat (Vec Nat)
open Signature public

data _⊧_▸_⊢ {n} (Σ : Signature) (Ψ : Vec Nat n) (Γ : Nat) : Set where
  ` : Fin Γ
    → Σ ⊧ Ψ ▸ Γ ⊢

  #_⟨_⟩ : (i : Fin n)
    → Vec (Σ ⊧ Ψ ▸ Γ ⊢) (idx Ψ i)
    → Σ ⊧ Ψ ▸ Γ ⊢

  _·_ : ∀ (𝔣 : 𝒪 Σ)
    → ((i : Fin (fst (𝔄 Σ 𝔣))) → Σ ⊧ Ψ ▸ Γ + idx (snd (𝔄 Σ 𝔣)) i ⊢)
    → Σ ⊧ Ψ ▸ Γ ⊢

module Examples where
  module Λ where
    data T : Set where
      lm ap : T

    Σ : Signature
    Σ = record
      { 𝒪 = T
      ; 𝔄 = λ
        { lm → , 1 ∷ []
        ; ap → , 0 ∷ 0 ∷ []
        }
      }

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ ap(lm(x. M[x]); N[])
    test₀ : Σ ⊧ 1 ∷ 0 ∷ [] ▸ z ⊢
    test₀ = ap · λ
      { z → lm · λ
        { z → # z ⟨ ` z ∷ [] ⟩
        ; (s ())
        }
      ; (s z) → # s z ⟨ [] ⟩
      ; (s s ())
      }

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ M[N[]]
    test₁ : Σ ⊧ 1 ∷ 0 ∷ [] ▸ z ⊢
    test₁ = # z ⟨ # s z ⟨ [] ⟩ ∷ [] ⟩
