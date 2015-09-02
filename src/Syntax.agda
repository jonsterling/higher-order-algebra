module Syntax where

infix 0 ⌞_⌟
infix 6 #_
infixl 0 _·_
infixr 1 _+_
infixr 1 _=≪_
infixl 1 _≫=_
infix 0 ⟦_⊧_⟧₀

open import Agda.Primitive
import Cats
open Cats.Cats
  hiding (Op)
open import Prelude
  hiding (δ; _+_)

_+_ : Nat → Nat → Nat
m + z = m
m + (s n) = s (m + n)

PSh : ∀ {o h} → Category o h → Set _
PSh 𝒞 = 𝒞 ⇒₀ Set𝒸 lzero

PSh𝒸 : ∀ {o h} → Category o h → Category _ _
PSh𝒸 𝒞 = 𝒞 ⇒₀𝒸 Set𝒸 lzero

TCtx : Set
TCtx = Nat

TVar : TCtx → Set
TVar = Fin

TVar𝒸 : Category _ _
TVar𝒸 = record
  { obj = Nat
  ; hom = λ m n → TVar m → TVar n
  ; idn = λ i → i
  ; cmp = λ g f i → g (f i)
  }

TVar⇒₀ : TVar𝒸 ⇒₀ Set𝒸 _
TVar⇒₀ = record
  { map₀ = TVar
  ; map₁ = id
  }

wkr : ∀ {Γ Δ} k
  → (ρ : TVar Γ → TVar Δ)
  → (TVar (Γ + k) → TVar (Δ + k))
wkr z ρ i = ρ i
wkr (s k) ρ z = z
wkr (s k) ρ (s i) = s (wkr k ρ i)

δ* : Nat → PSh𝒸 TVar𝒸 ⇒₀ PSh𝒸 TVar𝒸
δ* k = record
  { map₀ = λ ϕ → record
    { map₀ = λ i → map₀ ϕ (i + k)
    ; map₁ = λ ρ → map₁ ϕ (wkr k ρ)
    }
  ; map₁ = λ α → record { com = com α }
  }

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
open Sign public

⟦_⊧_⟧₀ : (Σ : Sign) (ϕ : TCtx → Set) (Γ : TCtx) → Set
⟦ Σ ⊧ ϕ ⟧₀ Γ = ∐[ 𝔣 ∶ 𝒪 Σ ] Π[ i ∶ TVar (arity Σ 𝔣) ] ϕ (Γ + valence Σ 𝔣 i)

⟦_⊧_⟧₁
  : (Σ : Sign)
  → (ϕ : PSh TVar𝒸)
  → {Γ Δ : TCtx} (ρ : TVar Γ → TVar Δ)
  → ⟦ Σ ⊧ map₀ ϕ ⟧₀ Γ
  → ⟦ Σ ⊧ map₀ ϕ ⟧₀ Δ
⟦ Σ ⊧ ϕ ⟧₁ ρ (𝔣 , κ) = 𝔣 , λ i → map₁ ϕ (wkr (valence Σ 𝔣 i) ρ) (κ i)

⟦_⟧ : Sign → PSh𝒸 TVar𝒸 ⇒₀ PSh𝒸 TVar𝒸
⟦_⟧ Σ = record
  { map₀ = λ ϕ → record
    { map₀ = ⟦ Σ ⊧ map₀ ϕ ⟧₀
    ; map₁ = ⟦ Σ ⊧ ϕ ⟧₁
    }
  ; map₁ = λ f → record { com = λ { (𝔣 , κ) → (𝔣 , λ i → com f (κ i)) } }
  }

data _* (Σ : Sign) {Θ : TCtx} (Ψ : MCtx Σ Θ) (Γ : TCtx) : Set where
  ⌞_⌟ : TVar Γ → (Σ *) Ψ Γ
  #_ : MVar Σ Ψ Γ ((Σ *) Ψ) → (Σ *) Ψ Γ
  op : ⟦ Σ ⊧ (Σ *) Ψ ⟧₀ Γ → (Σ *) Ψ Γ

pattern _·_ 𝔣 xs = op (𝔣 , xs)

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

Σ*-monad : (Σ : Sign) {Θ : TCtx} (Ψ : MCtx Σ Θ) → RMonad TVar⇒₀
Σ*-monad Σ Ψ = record
  { G = (Σ *) Ψ
  ; ret = ⌞_⌟
  ; ext = sub
  }

ret : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ}
  → TVar Γ → (Σ *) Ψ Γ
ret {Σ = Σ} {Ψ = Ψ} = RMonad.ret (Σ*-monad Σ Ψ)

_=≪_ : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ}
  → (TVar Γ → (Σ *) Ψ Δ)
  → ((Σ *) Ψ Γ → (Σ *) Ψ Δ)
_=≪_ {Σ = Σ} {Ψ = Ψ} = RMonad.ext (Σ*-monad Σ Ψ)

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
