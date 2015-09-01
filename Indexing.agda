module Indexing where

open import Agda.Primitive
open import Prelude

--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------

infixr 1 _[_]→_
infixr 2 cmp

data 𝔘 : Set₀ where
  𝔓 : 𝔘
  𝔉 : 𝔘

Ix : 𝔘 → ∀ {i} x → Set i → Set (i ⊔ lsuc x)
Ix 𝔓 x I = I → Set x
Ix 𝔉 x I = Σ[ X ∶ Set x ] (X → I)

_[_]→_ : ∀ {i} → Set i → 𝔘 → Set i → Set (lsuc i)
_[_]→_ {i = i} I 𝔓 O = Ix 𝔓 i I → Ix 𝔓 i O
_[_]→_ {i = i} I 𝔉 O = Ix 𝔉 i I → Ix 𝔉 i O

cmp : ∀ {i} {A B C : Set i} → (𝔲 : 𝔘)
  → (B [ 𝔲 ]→ C)
  → (A [ 𝔲 ]→ B)
  → (A [ 𝔲 ]→ C)
cmp 𝔓 g f = g ⋘ f
cmp 𝔉 g f = g ⋘ f

syntax cmp 𝔲 g f = g ⋘[ 𝔲 ] f

dom : ∀ {e i} {I : Set i} → Ix 𝔓 e (Ix 𝔉 e I)
dom = fst

map : ∀ {e i} {I : Set i} (p : Ix 𝔉 e I) → (dom p → I)
map = snd

inv : ∀ {e i} {I : Set i} {E : Set e} → (E → I) → Ix 𝔓 (i ⊔ e) I
inv {E = E} p i = Σ[ e ∶ E ] i ≡ p e

tot : ∀ {i p} {I : Set i} → Ix 𝔓 (i ⊔ p) (Ix 𝔓 p I)
tot = Σ _

fib : ∀ {i p} {I : Set i} → (φ : Ix 𝔓 p I) → (tot φ → I)
fib φ = fst

fam : ∀ {i} {I : Set i} → (Ix 𝔓 i I → Ix 𝔉 i I)
fam φ = tot φ , fib φ

pow : ∀ {i} {I : Set i} → (Ix 𝔓 i I ← Ix 𝔉 i I)
pow (X , p) = inv p

𝔓~>𝔉 : ∀ {i} {I : Set i} {O : Set i} → I [ 𝔓 ]→ O → I [ 𝔉 ]→ O
𝔓~>𝔉 κ = pow ⋙ κ ⋙ fam

𝔓<~𝔉 : ∀ {i} {I : Set i} {O : Set i} → I [ 𝔓 ]→ O ← I [ 𝔉 ]→ O
𝔓<~𝔉 κ = pow ⋘ κ ⋘ fam

--------------------------------------------------------------------------------
-- Functors
--------------------------------------------------------------------------------

infixr 0 _⋔_
infixr 0 _⊗_
infixl 3 _↓![_]
infixl 3 _↑![_]
infixl 3 _↑*[_]
infixl 3 _↓*[_]

_⋔_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
_⋔_ A B = A → B

_⊗_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
_⊗_ A B = A × B

_↓!𝔓 : ∀ {i} {I : Set i} {O : Set i} → (I → O) → I [ 𝔓 ]→ O
_↓!𝔓 = Lan _≡_ _⊗_

_↑!𝔓 : ∀ {i} {I : Set i} {O : Set i} → (I → O) → O [ 𝔓 ]→ I
_↑!𝔓 f = λ φ → φ ⋘ f

_↑*𝔓 : ∀ {i} {I : Set i} {O : Set i} → (I → O) → O [ 𝔓 ]→ I
_↑*𝔓 = _↑!𝔓

_↓*𝔓 : ∀ {i} {I : Set i} {O : Set i} → (I → O) → I [ 𝔓 ]→ O
_↓*𝔓 = Ran _≡_ _⋔_

_↓![_] : ∀ {i} {I : Set i} {O : Set i} → (I → O) → (𝔲 : 𝔘) → I [ 𝔲 ]→ O
f ↓![ 𝔓 ] = f ↓!𝔓
f ↓![ 𝔉 ] = 𝔓~>𝔉 ⋘ _↓!𝔓 ·≪ f

_↑![_] : ∀ {i} {I : Set i} {O : Set i} → (I → O) → (𝔲 : 𝔘) → O [ 𝔲 ]→ I
f ↑![ 𝔓 ] = f ↑!𝔓
f ↑![ 𝔉 ] = 𝔓~>𝔉 ⋘ _↑!𝔓 ·≪ f

_↑*[_] : ∀ {i} {I : Set i} {O : Set i} → (I → O) → (𝔲 : 𝔘) → O [ 𝔲 ]→ I
f ↑*[ 𝔓 ] = f ↑*𝔓
f ↑*[ 𝔉 ] = 𝔓~>𝔉 ⋘ _↑*𝔓 ·≪ f

_↓*[_] : ∀ {i} {I : Set i} {O : Set i} → (I → O) → (𝔲 : 𝔘) → I [ 𝔲 ]→ O
f ↓*[ 𝔓 ] = f ↓*𝔓
f ↓*[ 𝔉 ] = 𝔓~>𝔉 ⋘ _↓*𝔓 ·≪ f
