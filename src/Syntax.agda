module Syntax where

infix 2 #_
infix 3 _⟨_⟩
infix 0 _⊧_▸_⊢
infixr 0 ,_
infixr 0 _,_
infixr 1 _∷_
infixr 1 _+_
infix 4 s_
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

nth : ∀ {a n} {A : Set a} → Vec A n → (Fin n → A)
nth (x ∷ xs) z = x
nth (x ∷ xs) (s i) = nth xs i

record Signature : Set₁ where
  field
    𝒪 : Set₀
    𝔄 : 𝒪 → ∐ Nat (Vec Nat)
open Signature public

TCtx : Set
TCtx = Nat

TVar : TCtx → Set
TVar = Fin

MCtx : Nat → Set
MCtx = Vec TCtx

Op : Signature → Set
Op Σ = 𝒪 Σ

⊧Sp
  : (ϕ : ∀ {n} → Signature → MCtx n → TCtx → Set)
  → ∀ {n}
  → (Σ : Signature)
  → (Ψ : MCtx n)
  → (Γ : TCtx)
  → (𝔣 : Op Σ)
  → Set
⊧Sp ϕ Σ Ψ Γ 𝔣 = (i : Fin (fst (𝔄 Σ 𝔣))) → ϕ Σ Ψ (Γ + nth (snd (𝔄 Σ 𝔣)) i)

mutual
  record MVar {n} (Σ : Signature) (Ψ : MCtx n) (Γ : TCtx) : Set where
    inductive
    constructor _⟨_⟩
    field
      idx : Fin n
      vec : Vec (Σ ⊧ Ψ ▸ Γ ⊢) (nth Ψ idx)

  Sp : ∀ {n} (Σ : Signature) (Ψ : MCtx n) (Γ : TCtx) (𝔣 : Op Σ) → Set
  Sp = ⊧Sp _⊧_▸_⊢

  data _⊧_▸_⊢ {n} (Σ : Signature) (Ψ : MCtx n) (Γ : TCtx) : Set where
    ` : TVar Γ → Σ ⊧ Ψ ▸ Γ ⊢
    #_ : MVar Σ Ψ Γ → Σ ⊧ Ψ ▸ Γ ⊢
    _·_ : ∀ (𝔣 : Op Σ) → Sp Σ Ψ Γ 𝔣 → Σ ⊧ Ψ ▸ Γ ⊢

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
