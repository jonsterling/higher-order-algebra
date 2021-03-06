module Syntax where

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

pattern ∅ = ze

_⧺_ : TCtx → TCtx → TCtx
∅ ⧺ Γ = Γ
(su Φ) ⧺ Γ = su (Φ ⧺ Γ)

wkn : ∀ {𝔇 : TCtx → Set₀} Φ
  → TVar ~> 𝔇
  → [ TCtx ▹ TVar ] TVar ⊧ 𝔇 ⇓ 𝔇
  → [ TCtx ▹ TVar ] 𝔇 ⊧ (Φ ⧺_) ↑*· TVar ⇓ (Φ ⧺_) ↑*· 𝔇
wkn  ∅ `ze `su i ρ =
  ρ i
wkn (su Φ) `ze `su ze ρ =
  `ze ze
wkn (su Φ) `ze `su (su i) ρ =
  `su (wkn Φ `ze `su i ρ) su_

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

data Sp (Σ : Sign) (ϕ : TCtx → Set) (Γ : TCtx) : List TCtx → Set where
  ε : Sp Σ ϕ Γ []
  _·_ : ∀ {Φ Φ*} → ϕ (Φ ⧺ Γ) → Sp Σ ϕ Γ Φ* → Sp Σ ϕ Γ (Φ ∷ Φ*)

⟦_⊧_⟧₀ : (Σ : Sign) (ϕ : TCtx → Set) (Γ : TCtx) → Set
⟦ Σ ⊧ ϕ ⟧₀ Γ = ∐[ 𝔣 ∶ 𝒪 Σ ] Sp Σ ϕ Γ (𝔄 Σ 𝔣)

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

map-sp
  : ∀ {Σ ϕ ϑ Γ Δ Φ*}
  → (f : ∀ Φ → ϕ (Φ ⧺ Γ) → ϑ (Φ ⧺ Δ))
  → Sp Σ ϕ Γ Φ*
  → Sp Σ ϑ Δ Φ*
map-sp f ε = ε
map-sp f (_·_ {Φ = Φ} e sp) = f Φ e · map-sp f sp

{-# TERMINATING #-}
cata
  : ∀ 𝔇 {Σ Ξ} {Ψ : MCtx Σ Ξ} {ϑ ϕ}
  → (`va : ϑ ~> 𝔇)
  → (`me : MVar Σ 𝔇 Ψ ~> 𝔇)
  → (`op : ⟦ Σ ⊧ 𝔇 ⟧₀ ~> 𝔇)
  → (`ex : ([ TCtx ▹ ϕ ] (Σ *) ϕ Ψ ⇉ 𝔇) ~> 𝔇)
  → (`wk : (∀ Φ → [ TCtx ▹ ϕ ] ϑ ⊧ (Φ ⧺_) ↑*· ϕ ⇓ (Φ ⧺_) ↑*· ϑ))
  → [ TCtx ▹ ϕ ] ϑ ⊧ (Σ *) ϕ Ψ ⇓ 𝔇
cata 𝔇 `va `me `op `ex `wkn ⌞ i ⌟ ρ =
  `va ·≪ ρ i
cata 𝔇 `va `me `op `ex `wk (# μ ⟨ xs ⟩) ρ =
  `me (μ ⟨ mapv ((λ e → cata 𝔇 `va `me `op `ex `wk e ρ)) xs ⟩)
cata 𝔇 `va `me `op `ex `wk (ς e [ Φ ⇉ σ ]) ρ =
  `ex ·≪ , e , λ i → cata 𝔇 `va `me `op `ex `wk (σ i) ρ
cata 𝔇 {Σ = Σ} `va `me `op `ex `wk (op (𝔣 , sp)) ρ =
  `op ·≪ 𝔣 ,
    map-sp
      (λ Φ e → cata 𝔇 `va `me `op `ex `wk e (λ x → `wk Φ x ρ))
      sp

ren : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ}
  → [ TCtx ▹ TVar ] TVar ⊧ (Σ *) TVar Ψ ⇓ (Σ *) TVar Ψ
ren = cata _ ⌞_⌟ #_ op ex wkr

wks : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ} Φ
  → [ TCtx ▹ TVar ] (Σ *) TVar Ψ ⊧ (Φ ⧺_) ↑*· TVar ⇓ (Φ ⧺_) ↑*· (Σ *) TVar Ψ
wks Φ = wkn Φ ⌞_⌟ ren

sub : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ}
  → [ TCtx ▹ TVar ] (Σ *) TVar Ψ ⊧ (Σ *) TVar Ψ ⇓ (Σ *) TVar Ψ
sub = cata _ id #_ op ex wks

Ren𝒸 : Category _ _
Ren𝒸 = record
  { obj = Nat
  ; hom = λ Γ Δ → TVar Γ → TVar Δ
  ; idn = λ i → i
  ; cmp = λ ρ₁ ρ₀ i → ρ₁ (ρ₀ i)
  }

Sub𝒸 : {Σ : Sign} {Θ : TCtx} (Ψ : MCtx Σ Θ) → Category _ _
Sub𝒸 {Σ = Σ} Ψ = record
  { obj = TCtx
  ; hom = λ Γ Δ → TVar Γ → (Σ *) TVar Ψ Δ
  ; idn = ⌞_⌟
  ; cmp = λ σ₁ σ₀ i → sub (σ₀ i) σ₁
  }

TVar⇒₀ : Ren𝒸 ⇒₀ Set𝒸 _
TVar⇒₀ = record
  { map₀ = TVar
  ; map₁ = id
  }

Σ*-monad : (Σ : Sign) {Θ : TCtx} (Ψ : MCtx Σ Θ) → RMonad TVar⇒₀
Σ*-monad Σ Ψ = record
  { G = (Σ *) TVar Ψ
  ; ret = ⌞_⌟
  ; ext = λ m σ → sub σ m
  }

ret : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ}
  → TVar Γ → (Σ *) TVar Ψ Γ
ret {Σ = Σ} {Ψ = Ψ} = RMonad.ret (Σ*-monad Σ Ψ)

_=≪_ : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ}
  → (TVar Γ → (Σ *) TVar Ψ Δ)
  → ((Σ *) TVar Ψ Γ → (Σ *) TVar Ψ Δ)
_=≪_ {Σ = Σ} {Ψ = Ψ} = RMonad.ext (Σ*-monad Σ Ψ)

_≫=_ : ∀ {Σ Θ} {Ψ : MCtx Σ Θ} {Γ Δ}
  → (Σ *) TVar Ψ Γ
  → (TVar Γ → (Σ *) TVar Ψ Δ)
  → (Σ *) TVar Ψ Δ
m ≫= σ = σ =≪ m

Env : TCtx → Set₀ → Set₀
Env Γ A = TVar Γ → A

swk : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ} {Γ} → Env ∅ ((Σ *) TVar Ψ Γ)
swk = λ()

sid : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ} {Γ} → Env Γ ((Σ *) TVar Ψ Γ)
sid = ⌞_⌟

infixr 0 _∷ₑ_
_∷ₑ_ : ∀ {Σ : Sign} {Ξ} {Ψ : MCtx Σ Ξ} {Γ A}
  → A → Env Γ A → Env (su Γ) A
_∷ₑ_ fz fs ze = fz
_∷ₑ_ fz fs (su m) = fs m

module Examples where
  module Λ where
    infixr 0 ƛ_
    infixl 1 _⊙_

    data Op : Set where
      <> : Op
      lm : Op
      ap : Op
      def : TCtx → Op
      tel : TCtx → Op

    def-aux : (n : Nat) → List Nat
    def-aux ze = []
    def-aux (su n) = 0 ∷ def-aux n

    tel-aux : (n : Nat) (cur : Nat) → List Nat
    tel-aux ze cur = []
    tel-aux (su n) cur = cur ∷ tel-aux n (su cur)

    Σ : Sign
    Σ = record
      { 𝒪 = Op
      ; 𝔄 = λ
        { <> → []
        ; lm → 1 ∷ []
        ; ap → 0 ∷ 0 ∷ []
        ; (def Φ) → def-aux Φ ++l Φ ∷ []
        ; (tel Φ) → tel-aux Φ ze
        }
      }

    ƛ_ : ∀ {Ξ Γ} {Ψ : MCtx Σ Ξ}
      → Tm Σ Ψ (su Γ) → Tm Σ Ψ Γ
    ƛ_ e = lm ·* ` ze · ε

    _⊙_ : ∀ {Ξ Γ} {Ψ : MCtx Σ Ξ}
      → Tm Σ Ψ Γ → Tm Σ Ψ Γ → Tm Σ Ψ Γ
    e₀ ⊙ e₁ = ap ·* e₀ · e₁ · ε

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ ap(lm(x. M[x]); N[])
    test₀ : Tm Σ (1 ∷ 0 ∷ []) ∅
    test₀ = (ƛ #₁ ze [ ` ze ]) ⊙ #₀ (su ze)

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ M[N[]]
    test₁ : Tm Σ (1 ∷ 0 ∷ []) ∅
    test₁ = #₁ ze [ #₀ (su ze) ]

    test₂ : Tm Σ [] 1
    test₂ = def 3 ·* ` ze · (<> ·* ε) · ` ze · ` su su su ze · ε

    test₃ : Tm Σ [] 1
    test₃ = tel 3 ·* ` ze · ` su ze · ` su su ze · ε

    test₄ : Tm Σ [] ∅
    test₄ = lm ·* ` ze · ε

    test₅ : Tm Σ [] 1
    test₅ = ap ·* ` ze · (lm ·* ` ze · ε) · ε

    test₆ : Tm Σ [] ∅
    test₆ = test₂ ≫= λ
      { ze → test₄
      ; (su ())
      }

    test₇ :
      test₆
      ≡
      op ( def 3
         , op (lm , ⌞ ze ⌟ · ε)
         · op (<> , ε)
         · op (lm , ⌞ ze ⌟ · ε)
         · op (lm , ⌞ ze ⌟ · ε)
         · ε
         )
    test₇ = refl
