module Syntax where

infix 0 ⌞_⌟
infix 6 #_
infixl 0 _·_
infixr 1 _⧺_
infixr 1 _=≪_
infixl 1 _≫=_
infix 0 ⟦_⊧_⟧₀

open import Agda.Primitive
import Cats
open Cats.Cats
  hiding (Op)
open import Prelude
  hiding (δ; _+_)

TCtx : Set
TCtx = Nat

TVar : TCtx → Set
TVar = Fin

pattern ∅ = z

_⧺_ : TCtx → TCtx → TCtx
Γ ⧺ ∅ = Γ
Γ ⧺ (s Δ) = s (Γ ⧺ Δ)

PSh : ∀ {o h} → Category o h → Set _
PSh 𝒞 = 𝒞 ⇒₀ Set𝒸 lzero

PSh𝒸 : ∀ {o h} → Category o h → Category _ _
PSh𝒸 𝒞 = 𝒞 ⇒₀𝒸 Set𝒸 lzero

Ren𝒸 : Category _ _
Ren𝒸 = record
  { obj = Nat
  ; hom = λ Γ Δ → TVar Γ → TVar Δ
  ; idn = λ i → i
  ; cmp = λ ρ₁ ρ₀ i → ρ₁ (ρ₀ i)
  }

TVar⇒₀ : Ren𝒸 ⇒₀ Set𝒸 _
TVar⇒₀ = record
  { map₀ = TVar
  ; map₁ = id
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

wkr : ∀ {Γ Δ} Φ
  → (ρ : TVar Γ → TVar Δ)
  → (TVar (Γ ⧺ Φ) → TVar (Δ ⧺ Φ))
wkr ∅ ρ i = ρ i
wkr (s Φ) ρ ∅ = ∅
wkr (s Φ) ρ (s i) = s (wkr Φ ρ i)

δᵣ* : Nat → PSh𝒸 Ren𝒸 ⇒₀ PSh𝒸 Ren𝒸
δᵣ* Φ = record
  { map₀ = λ ϕ → record
    { map₀ = λ i → map₀ ϕ (i ⧺ Φ)
    ; map₁ = λ ρ → map₁ ϕ (wkr Φ ρ)
    }
  ; map₁ = λ α → record { com = com α }
  }

⟦_⊧_⟧₀ : (Σ : Sign) (ϕ : TCtx → Set) (Γ : TCtx) → Set
⟦ Σ ⊧ ϕ ⟧₀ Γ = ∐[ 𝔣 ∶ 𝒪 Σ ] Π[ i ∶ TVar (arity Σ 𝔣) ] ϕ (Γ ⧺ valence Σ 𝔣 i)

⟦_⊧_⟧₁ᵣ
  : (Σ : Sign)
  → (ϕ : PSh Ren𝒸)
  → {Γ Δ : obj Ren𝒸} (ρ : hom Ren𝒸 Γ Δ)
  → ⟦ Σ ⊧ map₀ ϕ ⟧₀ Γ
  → ⟦ Σ ⊧ map₀ ϕ ⟧₀ Δ
⟦ Σ ⊧ ϕ ⟧₁ᵣ ρ (𝔣 , κ) = 𝔣 , λ i → map₁ ϕ (wkr (valence Σ 𝔣 i) ρ) (κ i)

⟦_⟧ : Sign → PSh𝒸 Ren𝒸 ⇒₀ PSh𝒸 Ren𝒸
⟦_⟧ Σ = record
  { map₀ = λ ϕ → record
    { map₀ = ⟦ Σ ⊧ map₀ ϕ ⟧₀
    ; map₁ = ⟦ Σ ⊧ ϕ ⟧₁ᵣ
    }
  ; map₁ = λ f → record { com = λ { (𝔣 , κ) → (𝔣 , λ i → com f (κ i)) } }
  }

data _* (Σ : Sign) {Θ : TCtx} (Ψ : MCtx Σ Θ) (Γ : TCtx) : Set where
  ⌞_⌟ : TVar Γ → (Σ *) Ψ Γ
  #_ : MVar Σ Ψ Γ ((Σ *) Ψ) → (Σ *) Ψ Γ
  op : ⟦ Σ ⊧ (Σ *) Ψ ⟧₀ Γ → (Σ *) Ψ Γ

pattern _·_ 𝔣 xs = op (𝔣 , xs)

mutual
  ren⇒₀ : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} → PSh Ren𝒸
  ren⇒₀ {Σ = Σ} {Ψ = Ψ} = record
    { map₀ = (Σ *) Ψ
    ; map₁ = ren
    }

  {-# TERMINATING #-}
  ren
    : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ}
    → (ρ : TVar Γ → TVar Δ)
    → ((Σ *) Ψ Γ → (Σ *) Ψ Δ)
  ren ρ ⌞ i ⌟ = ⌞ ρ i ⌟
  ren ρ (# μ) = # var μ ⟨ map (ren ρ) (vec μ) ⟩ -- need sized types?
  ren {Σ = Σ} ρ (op xs) = op (⟦ Σ ⊧ ren⇒₀ ⟧₁ᵣ ρ xs)

wks : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ} Φ
  → (ρ : TVar Γ → (Σ *) Ψ Δ)
  → (TVar (Γ ⧺ Φ) → (Σ *) Ψ (Δ ⧺ Φ))
wks z σ i = σ i
wks (s k) σ z = ⌞ z ⌟
wks (s k) σ (s i) = ren s (wks k σ i)

mutual
  Sub𝒸 : {Σ : Sign} {Θ : TCtx} (Ψ : MCtx Σ Θ) → Category _ _
  Sub𝒸 {Σ = Σ} Ψ = record
    { obj = TCtx
    ; hom = λ Γ Δ → TVar Γ → (Σ *) Ψ Δ
    ; idn = ⌞_⌟
    ; cmp = λ σ₁ σ₀ i → sub σ₁ (σ₀ i)
    }

  -- FIXME: combine this with ₁ᵣ again
  ⟦_⟧₁ₛ
    : (Σ : Sign)
    → {Θ : TCtx} {Ψ : MCtx Σ Θ}
    → {Γ Δ : TCtx} (σ : TVar Γ → (Σ *) Ψ Δ)
    → ⟦ Σ ⊧ (Σ *) Ψ ⟧₀ Γ
    → ⟦ Σ ⊧ (Σ *) Ψ ⟧₀ Δ
  ⟦ Σ ⟧₁ₛ σ (𝔣 , xs) = (𝔣 , λ i → sub (wks (valence Σ 𝔣 i) σ) (xs i))

  {-# TERMINATING #-}
  sub
    : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ}
    → (ρ : TVar Γ → (Σ *) Ψ Δ)
    → ((Σ *) Ψ Γ → (Σ *) Ψ Δ)
  sub σ ⌞ i ⌟ = σ i
  sub σ (# μ) = # var μ ⟨ map (sub σ) (vec μ) ⟩ -- need sized types?
  sub {Σ = Σ} σ (op xs) = op (⟦ Σ ⟧₁ₛ σ xs)

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
