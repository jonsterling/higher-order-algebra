module Syntax where

open import Agda.Primitive
open import Containers
open import Prelude

infix 0 _[_]
infix 0 ⌞_⌟
infix 0 ⟦_⊧_⟧₀
infix 6 #_
infixl 0 _·_
infixl 1 _≫=_
infixr 1 _=≪_
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
Γ ⧺ ∅ = Γ
Γ ⧺ (s Δ) = s (Γ ⧺ Δ)

wkr : ∀ {Γ Δ} Φ
  → (ρ : TVar Γ → TVar Δ)
  → (TVar (Γ ⧺ Φ) → TVar (Δ ⧺ Φ))
wkr ∅ ρ i = ρ i
wkr (s Φ) ρ ∅ = ∅
wkr (s Φ) ρ (s i) = s (wkr Φ ρ i)

record Sign : Set₁ where
  field
    𝒪 : Set₀
    𝔄 : 𝒪 → ∐ TCtx (Vec TCtx)

  arity : 𝒪 → TCtx
  arity 𝔣 = fst (𝔄 𝔣)

  valence : (𝔣 : 𝒪) → TVar (arity 𝔣) → TCtx
  valence 𝔣 = idx (snd (𝔄 𝔣))

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

⟦_⊧_⟧₀ : (Σ : Sign) (ϕ : TCtx → Set) (Γ : TCtx) → Set
⟦ Σ ⊧ ϕ ⟧₀ Γ = ∐[ 𝔣 ∶ 𝒪 Σ ] Π[ i ∶ TVar (arity Σ 𝔣) ] ϕ (Γ ⧺ valence Σ 𝔣 i)

⟦_⊧_⟧₁
  : (Σ : Sign)
  → {ϕ₀ : TCtx → Set₀} {Γ Δ : TCtx}
  → (∀ (𝔣 : 𝒪 Σ) (i : Fin (arity Σ 𝔣))
    → (TVar (Γ ⧺ valence Σ 𝔣 i) → TVar (Δ ⧺ valence Σ 𝔣 i))
    →   (ϕ₀ (Γ ⧺ valence Σ 𝔣 i) →   ϕ₀ (Δ ⧺ valence Σ 𝔣 i)))
  → (ρ : TVar Γ → TVar Δ)
  → ⟦ Σ ⊧ ϕ₀ ⟧₀ Γ
  → ⟦ Σ ⊧ ϕ₀ ⟧₀ Δ
⟦ Σ ⊧ ϕ₁ ⟧₁ ρ (𝔣 , κ) = 𝔣 , λ i → ϕ₁ 𝔣 i (wkr (valence Σ 𝔣 i) ρ) (κ i)

data _* (Σ : Sign) (ϕ : TCtx → Set₀) {Ξ : TCtx} (Ψ : MCtx Σ Ξ) (Γ : TCtx) : Set₀ where
  ⌞_⌟ : ϕ Γ → (Σ *) ϕ Ψ Γ
  #_ : MVar Σ ((Σ *) ϕ Ψ) Ψ Γ → (Σ *) ϕ Ψ Γ
  op : ⟦ Σ ⊧ (Σ *) ϕ Ψ ⟧₀ Γ → (Σ *) ϕ Ψ Γ
  ex : ([ TCtx ▹ ϕ ] (Σ *) ϕ Ψ ⇉ (Σ *) ϕ Ψ) Γ → (Σ *) ϕ Ψ Γ

pattern _·_ 𝔣 xs = op (𝔣 , xs)
pattern _[_] e θ = ex (_ , e , θ)

{-# TERMINATING #-}
cata
  : {Σ : Sign} {Ξ : TCtx} {Ψ : MCtx Σ Ξ}
  → {ϑ : TCtx → Set₀} {𝔇 : TCtx → Set₀} {ϕ : TCtx → Set₀}
  → ϑ ~> 𝔇
  → MVar Σ 𝔇 Ψ ~> 𝔇
  → ⟦ Σ ⊧ 𝔇 ⟧₀ ~> 𝔇
  → [ TCtx ▹ ϕ ] (Σ *) ϕ Ψ ⇉ 𝔇 ~> 𝔇
  → (∀ Φ → [ TCtx ▹ ϕ ] ϑ ⊧ (_⧺ Φ) ↑*· ϕ ⇓ (_⧺ Φ) ↑*· ϑ)
  → [ TCtx ▹ ϕ ] ϑ ⊧ (Σ *) ϕ Ψ ⇓ 𝔇
cata `v `me `op `ex `wkn ⌞ i ⌟ ρ =
  `v ·≪ ρ i
cata `v `me `op `ex `wkn (# μ ⟨ xs ⟩) ρ =
  `me (μ ⟨ map (λ e → cata `v `me `op `ex `wkn e ρ) xs ⟩) -- need sized types?
cata `v `me `op `ex `wkn (e [ σ ]) ρ =
  `ex ·≪ , e , λ i → cata `v `me `op `ex `wkn (σ i) ρ
cata {Σ = Σ} `v `me `op `ex `wkn (op (𝔣 , κ)) ρ =
  `op ·≪ 𝔣 , λ i → cata `v `me `op `ex `wkn (κ i) (λ x → `wkn (valence Σ 𝔣 i) x ρ)

wkn : ∀ {𝔇 : TCtx → Set₀} Φ
  → TVar ~> 𝔇
  → [ TCtx ▹ TVar ] TVar ⊧ 𝔇 ⇓ 𝔇
  → [ TCtx ▹ TVar ] 𝔇 ⊧ (_⧺ Φ) ↑*· TVar ⇓ (_⧺ Φ) ↑*· 𝔇
wkn ∅ `z `s i ρ = ρ i
wkn (s Φ) `z `s z ρ = `z z
wkn (s Φ) `z `s (s i) ρ = `s (wkn Φ `z `s i ρ) s

`wkr : ∀ Φ → [ TCtx ▹ TVar ] TVar ⊧ (_⧺ Φ) ↑*· TVar ⇓ (_⧺ Φ) ↑*· TVar
`wkr Φ = wkn Φ id (λ x → ¿ x)

ren : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ}
  → [ TCtx ▹ TVar ] TVar ⊧ (Σ *) TVar Ψ ⇓ (Σ *) TVar Ψ
ren = cata ⌞_⌟ #_ op ex `wkr

wks : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ} Φ
  → [ TCtx ▹ TVar ] (Σ *) TVar Ψ ⊧ (_⧺ Φ) ↑*· TVar ⇓ (_⧺ Φ) ↑*· (Σ *) TVar Ψ
wks Φ = wkn Φ ⌞_⌟ ren

sub : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ}
  → [ TCtx ▹ TVar ] (Σ *) TVar Ψ ⊧ (Σ *) TVar Ψ ⇓ (Σ *) TVar Ψ
sub = cata id #_ op ex wks

ret : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ}
  → TVar Γ → (Σ *) TVar Ψ Γ
ret = ⌞_⌟

_≫=_ : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ}
  → (Σ *) TVar Ψ Γ
  → (TVar Γ → (Σ *) TVar Ψ Δ)
  → (Σ *) TVar Ψ Δ
m ≫= σ = sub m σ

_=≪_ : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ}
  → (TVar Γ → (Σ *) TVar Ψ Δ)
  → ((Σ *) TVar Ψ Γ → (Σ *) TVar Ψ Δ)
σ =≪ m = sub m σ

Ren : TCtx → TCtx → Set₀
Ren Γ Δ = TVar Γ → TVar Δ

idnR : ∀ {Γ} → Ren Γ Γ
idnR = id

cmpR : ∀ {Γ Δ Ξ} → Ren Δ Ξ → Ren Γ Δ → Ren Γ Ξ
cmpR = _⋘′_

Sub : ∀ (Σ : Sign) {Ξ} (Ψ : MCtx Σ Ξ)
  → TCtx → TCtx → Set₀
Sub Σ Ψ Γ Δ = TVar Γ → (Σ *) TVar Ψ Δ

idnS : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ} {Γ}
  → Sub Σ Ψ Γ Γ
idnS = ⌞_⌟

cmpS : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ} {Γ Δ Θ}
  → Sub Σ Ψ Δ Θ → Sub Σ Ψ Γ Δ → Sub Σ Ψ Γ Θ
cmpS = λ g f → (λ x → sub x g) ⋘′ f

-- explicit substitutions

Env : TCtx → Set₀ → Set₀
Env Γ A = TVar Γ → A

swk : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ} {Γ} → Env ∅ ((Σ *) TVar Ψ Γ)
swk = λ()

sid : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ} {Γ} → Env Γ ((Σ *) TVar Ψ Γ)
sid = ⌞_⌟

infixr 0 _∷ₑ_
_∷ₑ_ : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ} {Γ A}
  → A → Env Γ A → Env (s Γ) A
_∷ₑ_ fz fs z = fz
_∷ₑ_ fz fs (s m) = fs m

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
    test₀ : (Σ *) TVar (1 ∷ 0 ∷ []) z
    test₀ = ap · λ
      { z → lm · λ
        { z → # z ⟨ ⌞ z ⌟ ∷ [] ⟩
        ; (s ())
        }
      ; (s z) → # s z ⟨ [] ⟩
      ; (s (s ()))
      }

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ M[N[]]
    test₁ : (Σ *) TVar (1 ∷ 0 ∷ []) z
    test₁ = # z ⟨ # s z ⟨ [] ⟩ ∷ [] ⟩
