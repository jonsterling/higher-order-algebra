module Inductive where

open import Agda.Primitive
import Cats
open Cats.Cats
  hiding (Op)
open import Containers
open import Prelude

infixr 6 `_
infix 0 ς_[_⇉_]
infix 0 ⌞_⌟
infix 0 ⟦_⊧_⟧₀
infix 6 #_
infix 6 #₀
infix 6 #₁_[_]
infixl 0 _·*_
infixr 5 _·_
infixr 1 _⧺_

infix 1 [_▹_]_⊧_⇓_
infix 1 [_▹_]_⇉_

[_▹_]_⊧_⇓_
  : (σ : Set₀)
  → (π : σ → Set₀)
  → (σ → Set₀)
  → (σ → Set₀)
  → ((σ → Set₀) → Set₀)
[ σ ▹ π ] ρ ⊧ 𝔏 ⇓ 𝔇 = 𝔏 ~> Ran oY oY ρ 𝔇 ⋘ π

[_▹_]_⇉_
  : (σ : Set₀)
  → (π : σ → Set₀)
  → (σ → Set₀)
  → (σ → Set₀)
  → (σ → Set₀)
[ σ ▹ π ] 𝔏 ⇉ 𝔇 = Lan oY _×_ π 𝔏 ⋘ 𝔇

TCtx : Set
TCtx = Nat

TVar : TCtx → Set
TVar = Fin

pattern ∅ = z

_⧺_ : TCtx → TCtx → TCtx
∅ ⧺ Γ = Γ
(s Φ) ⧺ Γ = s (Φ ⧺ Γ)

wkn : ∀ {𝔇 : TCtx → Set₀} Φ
  → TVar ~> 𝔇
  → [ TCtx ▹ TVar ] TVar ⊧ 𝔇 ⇓ 𝔇
  → [ TCtx ▹ TVar ] 𝔇 ⊧ (Φ ⧺_) ↑*· TVar ⇓ (Φ ⧺_) ↑*· 𝔇
wkn ∅ `z `s i ρ = ρ i
wkn (s Φ) `z `s z ρ = `z z
wkn (s Φ) `z `s (s i) ρ = `s (wkn Φ `z `s i ρ) s_

wkr : ∀ Φ → [ TCtx ▹ TVar ] TVar ⊧ (Φ ⧺_) ↑*· TVar ⇓ (Φ ⧺_) ↑*· TVar
wkr Φ = wkn Φ id (λ x → ¿ x)

record Sign : Set₁ where
  field
    𝒪 : Set₀
    𝔄 : 𝒪 → List TCtx

  MCtx : TCtx → Set
  MCtx = Vec TCtx

  infix 7 _⟨_⟩
  record MVar (ϕ : TCtx → Set) {Ξ : TCtx} (Ψ : MCtx Ξ) (Γ : TCtx) : Set where
    constructor _⟨_⟩
    field
      var : TVar Ξ
      vec : Vec (ϕ Γ) (idx Ψ var)
  open MVar public
open Sign public

data Sp (Σ : Sign) (ϕ : TCtx → Set) (Γ : TCtx) (𝔣 : 𝒪 Σ) : List TCtx → Set where
  ε : Sp Σ ϕ Γ 𝔣 []
  _·_ : ∀ {Φ Φ*} → ϕ (Φ ⧺ Γ) → Sp Σ ϕ Γ 𝔣 Φ* → Sp Σ ϕ Γ 𝔣 (Φ ∷ Φ*)

⟦_⊧_⟧-sp : ∀ Σ {𝔣 ϕ₀ Γ Δ}
  → (ϕ₁ : ∀ Φ → (TVar (Φ ⧺ Γ) → TVar (Φ ⧺ Δ)) → ϕ₀ (Φ ⧺ Γ) → ϕ₀ (Φ ⧺ Δ))
  → (ρ : TVar Γ → TVar Δ)
  → (∀ {Φ*} → Sp Σ ϕ₀ Γ 𝔣 Φ* → Sp Σ ϕ₀ Δ 𝔣 Φ*)
⟦ Σ ⊧ ϕ₁ ⟧-sp ρ {Φ* = []} ε =
  ε
⟦ Σ ⊧ ϕ₁ ⟧-sp ρ {Φ* = Φ ∷ Φ*} (e · sp) =
  ϕ₁ Φ (λ x → wkr Φ x ρ) e · ⟦ Σ ⊧ ϕ₁ ⟧-sp ρ sp

⟦_⊧_⟧₀ : (Σ : Sign) (ϕ : TCtx → Set) (Γ : TCtx) → Set
⟦ Σ ⊧ ϕ ⟧₀ Γ = ∐[ 𝔣 ∶ 𝒪 Σ ] Sp Σ ϕ Γ 𝔣 (𝔄 Σ 𝔣)

⟦_⊧_⟧₁
  : (Σ : Sign)
  → {ϕ₀ : TCtx → Set₀} {Γ Δ : TCtx}
  → (ϕ₁ : ∀ Φ → (TVar (Φ ⧺ Γ) → TVar (Φ ⧺ Δ)) → ϕ₀ (Φ ⧺ Γ) → ϕ₀ (Φ ⧺ Δ))
  → (ρ : TVar Γ → TVar Δ)
  → (⟦ Σ ⊧ ϕ₀ ⟧₀ Γ → ⟦ Σ ⊧ ϕ₀ ⟧₀ Δ)
⟦ Σ ⊧ ϕ₁ ⟧₁ ρ (𝔣 , κ) =
  𝔣 , ⟦ Σ ⊧ ϕ₁ ⟧-sp ρ κ

data _* (Σ : Sign) (ϕ : TCtx → Set₀) {Ξ : TCtx} (Ψ : MCtx Σ Ξ) (Γ : TCtx) : Set₀ where
  ⌞_⌟ : ϕ Γ → (Σ *) ϕ Ψ Γ
  #_ : MVar Σ ((Σ *) ϕ Ψ) Ψ Γ → (Σ *) ϕ Ψ Γ
  op : ⟦ Σ ⊧ (Σ *) ϕ Ψ ⟧₀ Γ → (Σ *) ϕ Ψ Γ
  ex : ([ TCtx ▹ ϕ ] (Σ *) ϕ Ψ ⇉ (Σ *) ϕ Ψ) Γ → (Σ *) ϕ Ψ Γ

Tm : (Σ : Sign) {Ξ : TCtx} (Ψ : MCtx Σ Ξ) (Γ : TCtx) → Set
Tm Σ = (Σ *) TVar

pattern `_ i = ⌞ i ⌟
pattern _·*_ 𝔣 xs = op (𝔣 , xs)
pattern #₀ μ = # μ ⟨ [] ⟩
pattern #₁_[_] μ e = # μ ⟨ e ∷ [] ⟩
pattern ς_[_⇉_] e Γ σ = ex (Γ , e , σ)

module Examples where
  module Λ where
    infixr 0 ƛ_
    infixl 1 _⊙_

    data Op : Set where
      lm : Op
      ap : Op
      def : TCtx → Op
      tel : TCtx → Op

    def-aux : (n : Nat) → List Nat
    def-aux z = []
    def-aux (s n) = 0 ∷ def-aux n

    tel-aux : (n : Nat) (cur : Nat) → List Nat
    tel-aux z cur = []
    tel-aux (s n) cur = cur ∷ tel-aux n (s cur)

    Σ : Sign
    Σ = record
      { 𝒪 = Op
      ; 𝔄 = λ
        { lm → 1 ∷ []
        ; ap → 0 ∷ 0 ∷ []
        ; (def Φ) → def-aux Φ ++l Φ ∷ []
        ; (tel Φ) → tel-aux Φ z
        }
      }

    ƛ_ : ∀ {Ξ Γ} {Ψ : MCtx Σ Ξ}
      → Tm Σ Ψ (s Γ) → Tm Σ Ψ Γ
    ƛ_ e = lm ·* ` z · ε

    _⊙_ : ∀ {Ξ Γ} {Ψ : MCtx Σ Ξ}
      → Tm Σ Ψ Γ → Tm Σ Ψ Γ → Tm Σ Ψ Γ
    e₀ ⊙ e₁ = ap ·* e₀ · e₁ · ε

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ ap(lm(x. M[x]); N[])
    test₀ : Tm Σ (1 ∷ 0 ∷ []) ∅
    test₀ = (ƛ #₁ z [ ` z ]) ⊙ #₀ (s z)

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ M[N[]]
    test₁ : Tm Σ (1 ∷ 0 ∷ []) ∅
    test₁ = #₁ z [ #₀ (s z) ]

    test₂ : Tm Σ [] 1
    test₂ = def 3 ·* ` z · ` z · ` z · ` s s s z · ε

    test₃ : Tm Σ [] 1
    test₃ = tel 3 ·* ` z · ` s z · ` s s z · ε
