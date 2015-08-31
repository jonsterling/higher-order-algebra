module SyntaxTyped where

infix 1 `_
infix 2 #_
infix 3 _⟨_⊣_⟩
infix 3 _⟨_⟩
infix 4 s_
infixl 1 _*_
infixl 1 _·_
infixr 0 ,_
infixr 0 _,_
infixr 0 _⧺_
infixr 1 _+_
infixr 2 _∷_

open import Agda.Primitive

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

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

data List {a} (A : Set a) : Set a where
  [] : List A
  _∷_ : (x : A) (xs : List A) → List A

len : ∀ {a} {A : Set a} → List A → Nat
len [] = z
len (x ∷ xs) = s (len xs)

_⧺_ : ∀ {a} {A : Set a} → List A → List A → List A
[] ⧺ ys = ys
(x ∷ xs) ⧺ ys = x ∷ (xs ⧺ ys)

data Vec {a} (A : Set a) : Nat → Set a where
  [] : Vec A z
  _∷_ : ∀ {n} → (x : A) (xs : Vec A n) → Vec A (s n)

mapToList : ∀ {a b} {A : Set a} {B : Set b} {n} → (A → B) → (Vec A n → List B)
mapToList f [] = []
mapToList f (x ∷ xs) = f x ∷ mapToList f xs

tab : ∀ {a} {A : Set a} {n} → (Fin n → A) → List A
tab {n = z} f = []
tab {n = s n} f = f z ∷ tab λ i → f (s i)

nth : ∀ {a n} {A : Set a} → Vec A n → (Fin n → A)
nth (x ∷ xs) z = x
nth (x ∷ xs) (s i) = nth xs i

Shape : Set → Nat → Set
Shape 𝒯 n = Vec (List 𝒯 × 𝒯) n × 𝒯

record Sign : Set₁ where
  field
    𝒯 : Set₀
    𝒪 : Set₀
    𝔄 : 𝒪 → ∐ Nat (Shape 𝒯)
open Sign public

dom : (Σ : Sign) (𝔣 : 𝒪 Σ) (i : Fin (fst (𝔄 Σ 𝔣))) → List (𝒯 Σ)
dom Σ 𝔣 i = fst (nth (fst (snd (𝔄 Σ 𝔣))) i)

cod : (Σ : Sign) (𝔣 : 𝒪 Σ) → 𝒯 Σ
cod Σ 𝔣 = snd (snd (𝔄 Σ 𝔣))

TCtx : Sign → Set
TCtx Σ = List (𝒯 Σ)

data TVar (Σ : Sign) : (Γ : TCtx Σ) (τ : 𝒯 Σ) → Set where
  z : ∀ {Γ τ} → TVar Σ (τ ∷ Γ) τ
  s_ : ∀ {Γ σ τ} → TVar Σ Γ τ → TVar Σ (σ ∷ Γ) τ

MCtx : Sign → Nat → Set
MCtx Σ = Vec (TCtx Σ × 𝒯 Σ)

Op : Sign → Set
Op Σ = 𝒪 Σ

mutual
  record MVar {n} (Σ : Sign) (Ψ : MCtx Σ n) (Γ : TCtx Σ) : Set where
    inductive
    constructor _⟨_⊣_⟩
    field
      idx : Fin n
      vec : Vec (∐ (𝒯 Σ) (λ ρ → Σ ⊧ Ψ ▸ Γ ⊢ ρ)) (len (fst (nth Ψ idx)))
      coh : mapToList fst vec ≡ fst (nth Ψ idx)

  Sp : ∀ {n} (Σ : Sign) (Ψ : MCtx Σ n) (Γ : TCtx Σ) (𝔣 : Op Σ) → Set
  Sp Σ Ψ Γ 𝔣 =
    ∐ ((i : Fin (fst (𝔄 Σ 𝔣))) →
       ∐ (𝒯 Σ) λ ρ →
       Σ ⊧ Ψ ▸ Γ ⧺ dom Σ 𝔣 i ⊢ ρ)
       λ ts → tab (λ j → fst (ts j)) ≡ mapToList snd (fst (snd (𝔄 Σ 𝔣)))

  data _⊧_▸_⊢_ {n} (Σ : Sign) (Ψ : MCtx Σ n) (Γ : TCtx Σ) : 𝒯 Σ → Set where
    `_ : ∀ {τ} → TVar Σ Γ τ → Σ ⊧ Ψ ▸ Γ ⊢ τ
    #_ : (μ : MVar Σ Ψ Γ) → Σ ⊧ Ψ ▸ Γ ⊢ snd (nth Ψ (MVar.idx μ))
    _*_ : (𝔣 : Op Σ) → Sp Σ Ψ Γ 𝔣 → Σ ⊧ Ψ ▸ Γ ⊢ cod Σ 𝔣

pattern _·_ 𝔣 ts = 𝔣 * (ts , refl)
pattern _⟨_⟩ μ ts = μ ⟨ ts ⊣ refl ⟩

module Examples where
  module Λ where

    data Tp : Set where
      ι : Tp
      _⇒_ : Tp → Tp → Tp

    data Tm : Set where
      lm ap : Tm

    Σ : Tp → Tp → Sign
    Σ σ τ = record
      { 𝒯 = Tp
      ; 𝒪 = Tm
      ; 𝔄 = λ
        { lm → , ((σ ∷ []) , τ) ∷ [] , (σ ⇒ τ)
        ; ap → , ([] , (σ ⇒ τ)) ∷ ([] , σ) ∷ [] , τ
        }
      }

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ ap(lm(x. M[x]); N[])
    test₀ : ∀ {σ τ} → Σ σ τ ⊧ ((σ ∷ []) , τ) ∷ ([] , σ) ∷ [] ▸ [] ⊢ τ
    test₀ = ap · λ
      { z → _ , lm · λ
        { z → , # z ⟨ (, ` z) ∷ [] ⟩
        ; (s ())
        }
      ; (s z) → , # s z ⟨ [] ⟩
      ; (s (s ()))
      }

    -- Λ ⊧ N : [0], M : [1] ▸ ∅ ⊢ M[N[]]
    test₁ : ∀ {σ τ} → Σ σ τ ⊧ ((σ ∷ []) , τ) ∷ ([] , σ) ∷ [] ▸ [] ⊢ τ
    test₁ = # z ⟨ (, # s z ⟨ [] ⟩) ∷ [] ⟩
