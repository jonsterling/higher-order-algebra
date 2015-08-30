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
