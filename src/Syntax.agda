module Syntax where

infix 6 #_
infixl 0 _·_
infixr 1 _+_
infixr 5 _∷_

open import Agda.Primitive
open import Prelude
  hiding (δ; _+_)

_+_ : Nat → Nat → Nat
m + z = m
m + (s n) = s (m + n)

data Vec {a} (A : Set a) : Nat → Set a where
  [] : Vec A z
  _∷_ : ∀ {n} → (x : A) (xs : Vec A n) → Vec A (s n)

idx : ∀ {a n} {A : Set a} → Vec A n → (Fin n → A)
idx (x ∷ xs) z = x
idx (x ∷ xs) (s i) = idx xs i

record Sign : Set₁ where
  field
    𝒪 : Set₀
    𝔄 : 𝒪 → ∐ Nat (Vec Nat)

  arity : 𝒪 → Nat
  arity 𝔣 = fst (𝔄 𝔣)

  valence : (𝔣 : 𝒪) → Fin (arity 𝔣) → Nat
  valence 𝔣 = idx (snd (𝔄 𝔣))

  TCtx : Set
  TCtx = Nat

  TVar : TCtx → Set
  TVar = Fin

  MCtx : TCtx → Set
  MCtx = Vec TCtx

  infix 7 _⟨_⟩
  record MVar {Δ : TCtx} (Ψ : MCtx Δ) (Γ : TCtx) (ϕ : TCtx → Set) : Set where
    constructor _⟨_⟩
    field
      var : TVar Δ
      vec : Vec (ϕ Γ) (idx Ψ var)
  open MVar public

  ⟦_⊢_⟧_ : (TCtx → Set) → (TCtx → Set)
  ⟦_⊢_⟧_ ϕ Γ = ∐[ 𝔣 ∶ 𝒪 ] Π[ i ∶ Fin (arity 𝔣) ] ϕ (Γ + valence 𝔣 i)
open Sign public

data Tm (Σ : Sign) {Δ : TCtx Σ} (Ψ : MCtx Σ Δ) (Γ : TCtx Σ) : Set where
  ` : TVar Σ Γ → Tm Σ Ψ Γ
  #_ : MVar Σ Ψ Γ (Tm Σ Ψ) → Tm Σ Ψ Γ
  op : ⟦ Σ ⊢ Tm Σ Ψ ⟧ Γ → Tm Σ Ψ Γ

pattern _·_ 𝔣 xs = op (𝔣 , xs)

module Examples where
  module Λ where
    data Op : Set where
      lm ap : Op

    Σ : Sign
    Σ = record
      { 𝒪 = Op
      ; 𝔄 = λ
        { lm → , 1 ∷ []
        ; ap → , 0 ∷ 0 ∷ []
        }
      }

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ ap(lm(x. M[x]); N[])
    test₀ : Tm Σ (1 ∷ 0 ∷ []) z
    test₀ = ap · λ
      { z → lm · λ
        { z → # z ⟨ ` z ∷ [] ⟩
        ; (s ())
        }
      ; (s z) → # s z ⟨ [] ⟩
      ; (s (s ()))
      }

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ M[N[]]
    test₁ : Tm Σ (1 ∷ 0 ∷ []) z
    test₁ = # z ⟨ # s z ⟨ [] ⟩ ∷ [] ⟩
