module Syntax where

infix 0 ⌞_⌟
infix 6 #_
infixl 0 _·_
infixr 1 _+_
infixr 5 _∷_
infixr 1 _=≪_
infixl 1 _≫=_

open import Agda.Primitive
open import Prelude
  hiding (δ; _+_)

_+_ : Nat → Nat → Nat
m + z = m
m + (s n) = s (m + n)

data Vec {a} (A : Set a) : Nat → Set a where
  [] : Vec A z
  _∷_ : ∀ {n} → (x : A) (xs : Vec A n) → Vec A (s n)

map : ∀ {a} {A : Set a} {B : Set} {n} (f : A → B) → (Vec A n → Vec B n)
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

idx : ∀ {a n} {A : Set a} → Vec A n → (Fin n → A)
idx (x ∷ xs) z = x
idx (x ∷ xs) (s i) = idx xs i

TCtx : Set
TCtx = Nat

TVar : TCtx → Set
TVar = Fin

record Sign : Set₁ where
  field
    𝒪 : Set₀
    𝔄 : 𝒪 → ∐ Nat (Vec Nat)

  arity : 𝒪 → Nat
  arity 𝔣 = fst (𝔄 𝔣)

  valence : (𝔣 : 𝒪) → Fin (arity 𝔣) → Nat
  valence 𝔣 = idx (snd (𝔄 𝔣))

  MCtx : TCtx → Set
  MCtx = Vec TCtx

  infix 7 _⟨_⟩
  record MVar {Θ : TCtx} (Ψ : MCtx Θ) (Γ : TCtx) (ϕ : TCtx → Set) : Set where
    constructor _⟨_⟩
    field
      var : TVar Θ
      vec : Vec (ϕ Γ) (idx Ψ var)
  open MVar public

  ⟦_⊢_⟧_ : (TCtx → Set) → (TCtx → Set)
  ⟦_⊢_⟧_ ϕ Γ = ∐[ 𝔣 ∶ 𝒪 ] Π[ i ∶ TVar (arity 𝔣) ] ϕ (Γ + valence 𝔣 i)
open Sign public

data _* (Σ : Sign) {Θ : TCtx} (Ψ : MCtx Σ Θ) (Γ : TCtx) : Set where
  ⌞_⌟ : TVar Γ → (Σ *) Ψ Γ
  #_ : MVar Σ Ψ Γ ((Σ *) Ψ) → (Σ *) Ψ Γ
  op : ⟦ Σ ⊢ (Σ *) Ψ ⟧ Γ → (Σ *) Ψ Γ

pattern _·_ 𝔣 xs = op (𝔣 , xs)

SignAlg : (Σ : Sign) → Set₁
SignAlg Σ =
  ∐ (TCtx → Set₀) λ ϕ →
  Π TCtx λ Γ →
  Π (𝒪 Σ) λ 𝔣 →
  Π (TVar (arity Σ 𝔣)) (λ i → ϕ (Γ + valence Σ 𝔣 i)) →
  ϕ Γ

alg : (Σ : Sign) {Θ : TCtx} (Ψ : MCtx Σ Θ) → SignAlg Σ
alg Σ Ψ = (Σ *) Ψ , λ Γ 𝔣 α → op (𝔣 , α)

wkr : ∀ {Γ Δ} k
  → (ρ : TVar Γ → TVar Δ)
  → (TVar (Γ + k) → TVar (Δ + k))
wkr z ρ i = ρ i
wkr (s k) ρ z = z
wkr (s k) ρ (s i) = s (wkr k ρ i)

{-# TERMINATING #-}
ren
  : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ}
  → (ρ : TVar Γ → TVar Δ)
  → ((Σ *) Ψ Γ → (Σ *) Ψ Δ)
ren ρ ⌞ i ⌟ = ⌞ ρ i ⌟
ren ρ (# μ) = # var μ ⟨ map (ren ρ) (vec μ) ⟩ -- need sized types?
ren {Σ = Σ} ρ (op (𝔣 , xs)) = op (𝔣 , λ i → ren (wkr (valence Σ 𝔣 i) ρ) (xs i))

wks : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ} k
  → (ρ : TVar Γ → (Σ *) Ψ Δ)
  → (TVar (Γ + k) → (Σ *) Ψ (Δ + k))
wks z σ i = σ i
wks (s k) σ z = ⌞ z ⌟
wks (s k) σ (s i) = ren s (wks k σ i)

{-# TERMINATING #-}
sub
  : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ}
  → (ρ : TVar Γ → (Σ *) Ψ Δ)
  → ((Σ *) Ψ Γ → (Σ *) Ψ Δ)
sub σ ⌞ i ⌟ = σ i
sub σ (# μ) = # var μ ⟨ map (sub σ) (vec μ) ⟩ -- need sized types?
sub {Σ = Σ} σ (op (𝔣 , xs)) = op (𝔣 , λ i → sub (wks (valence Σ 𝔣 i) σ) (xs i))

ret : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ}
  → TVar Γ → (Σ *) Ψ Γ
ret = ⌞_⌟

_=≪_ : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ}
  → (TVar Γ → (Σ *) Ψ Δ)
  → ((Σ *) Ψ Γ → (Σ *) Ψ Δ)
_=≪_ = sub

_≫=_ : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ}
  → (Σ *) Ψ Γ
  → (TVar Γ → (Σ *) Ψ Δ)
  → (Σ *) Ψ Δ
m ≫= σ = σ =≪ m

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
    test₀ : (Σ *) (1 ∷ 0 ∷ []) z
    test₀ = ap · λ
      { z → lm · λ
        { z → # z ⟨ ⌞ z ⌟ ∷ [] ⟩
        ; (s ())
        }
      ; (s z) → # s z ⟨ [] ⟩
      ; (s (s ()))
      }

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ M[N[]]
    test₁ : (Σ *) (1 ∷ 0 ∷ []) z
    test₁ = # z ⟨ # s z ⟨ [] ⟩ ∷ [] ⟩
