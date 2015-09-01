module Prelude where

open import Agda.Primitive

--------------------------------------------------------------------------------
-- Preliminaries
--------------------------------------------------------------------------------

infixl 0 _←_
infix  0 _~>_
infix  0 _<~_
infix  2 Π
infixr 3 _⋘_
infixl 2 _⋙_
infixl 5 _↑*
infixl 5 _↑*·_
infixr 0 _·≪_
infixl 0 _≫·_
infix  4 ¬_
infix  0 !
infix  0 ¿
infix  2 ∐
infixr 4 _,_
infix  4 ,_
infixr 1 _×_
infix  0 ⟨_,_⟩
infix  0 ⟨_×_⟩
infixr 1 _+_
infixr 1 _-_
infix  0 [_,_]
infix  3 _≡_
infix  0 ∫↓
infix  0 ∫↑

_←_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
B ← A = A → B

_~>_ : ∀ {d u v} {𝔡 : Set d} → (𝔡 → Set u) → (𝔡 → Set v) → Set (d ⊔ u ⊔ v)
f ~> g = ∀ {x} → f x → g x

_<~_ : ∀ {d u v} {𝔡 : Set d} → (𝔡 → Set u) → (𝔡 → Set v) → Set (d ⊔ u ⊔ v)
g <~ f = ∀ {x} → f x → g x

Π : ∀ {a b} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
Π A B = (x : A) → B x

syntax Π A (λ x → B) = Π[ x ∶ A ] B

id : ∀ {a} {A : Set a} → A → A
id x = x

! : ∀ {a b} {B : Set b} {A : Set a} → A → B → A
! a b = a

!′ : ∀ {a b} {B : Set b} {A : B → Set a} → (∀ {b} → A b) → (∀ b → A b)
!′ a b = a

_⋘_ : ∀ {a b c}
  → {A : Set a}
  → {B : A → Set b}
  → {C : {x : A} → B x → Set c}
  → (g : (∀ {x} (y : B x) → C y))
  → (f : (x : A) → B x)
  → ((x : A) → C (f x))
g ⋘ f = λ x → g (f x)

_⋘′_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  → (B → C)
  → (A → B)
  → (A → C)
g ⋘′ f = λ x → g (f x)

_⋙_ : ∀ {a b c}
  → {A : Set a}
  → {B : A → Set b}
  → {C : {x : A} → B x → Set c}
  → (f : (x : A) → B x)
  → (g : (∀ {x} (y : B x) → C y))
  → ((x : A) → C (f x))
f ⋙ g = g ⋘ f

_↑* : ∀ {a b c}
  → {A : Set a}
  → {B : A → Set b}
  → {C : {x : A} → B x → Set c}
  → (f : (x : A) → B x)
  → (g : (∀ {x} (y : B x) → C y))
  → ((x : A) → C (f x))
_↑* = _⋙_

_↑*·_ : ∀ {a b c}
  → {A : Set a}
  → {B : A → Set b}
  → {C : {x : A} → B x → Set c}
  → (f : (x : A) → B x)
  → (g : (∀ {x} (y : B x) → C y))
  → ((x : A) → C (f x))
_↑*·_ = _↑*

_⋙′_ : ∀ {a b c}
  → {A : Set a}
  → {B : Set b}
  → {C : Set c}
  → (f : A → B)
  → (g : B → C)
  → (A → C)
f ⋙′ g = f ⋙ g

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  → (A → B → C)
  → (B → A → C)
flip f x y = f y x

Yo : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Yo B = λ A → A → B

oY : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
oY = flip Yo

_·≪_ : ∀ {a b} {A : Set a} {B : A → Set b} → Π A B → Π A B
f ·≪ x = f x

_≫·_ : ∀ {a b} {A : Set a} {B : A → Set b} → Π A ·≪ oY (Π A B) ⋘ B
x ≫· f = f ·≪ x

¿ : ∀ {a b} {A : Set a} {B : A → Set b} → Π A ·≪ oY (Π A B) ⋘ B
¿ x = _≫·_ x

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

data ⊥ : Set₀ where

¬_ : Set₀ → Set₀
¬_ A = A → ⊥

absurd : ∀ {A : Set₀} → ⊥ → A
absurd ()

record ⊤ : Set₀ where
  constructor tt

data Bool {i} : Set i where
  false : Bool
  true  : Bool

pick : ∀ {a} b {P : Bool {b} → Set a} → P false → P true → (∀ x → P x)
pick _ x y false = x
pick _ x y true  = y

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

ᵛ : ∀ {a b c}
  → {A : Set a} {B : A → Set b} {P : ∐ A B → Set c}
  → Π[ x ∶ A ] Π[ y ∶ B x ] P (x , y)
  → (∀ x → P x)
ᵛ p (x , y) = p x y

δ : ∀ {a} {A : Set a} → A → A × A
δ x = (x , x)

⟨_,_⟩ : ∀ {a b x} {X : Set x} {A : X → Set a} {B : ∀ {x} → A x → Set b}
  → (f : Π X A)
  → Π X (B ⋘ f)
  → Π X (∐ ⋘ A ⋙ ¿ B)
⟨ f , g ⟩ x = f x , g x

⟨_×_⟩ : ∀ {a b x₀ x₁} {A : Set a} {B : A → Set b} {X₀ : Set x₀} {X₁ : X₀ → Set x₁}
  → (f : X₀ → A)
  → X₁ ~> (B ⋘ f)
  → (∐ X₀ X₁ → ∐ A B)
⟨_×_⟩ f g (x , y) = f x , g y

↓× : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set (lsuc c)}
  → Π A ·≪ B ⋙ Yo C → (∐ A B → C)
↓× f (x , y) = f x y

↑⇒ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set (lsuc c)}
  → (∐ A B → C) → Π A ·≪ B ⋙ Yo C
↑⇒ f x y = f (x , y)

_+_ : ∀ {i} → (A : Set i) (B : Set i) → Set i
A + B = ∐ Bool ·≪ pick lzero A B

pattern inl a = false , a
pattern inr b = true  , b

_-_ : (X : Set₀) (x : X) → Set₀
X - x = ∐[ y ∶ X ] ¬ (x ≡ y)

Dec : ∀ (A : Set₀) → Set₀
Dec A = ¬ A + A

[_,_] : ∀ {a x} {A : Set a} {B : Set a} {X : Set x}
  → (A → X)
  → (B → X)
  → (A + B → X)
[ f , g ] (inl a) = f a
[ f , g ] (inr b) = g b

data Nat : Set₀ where
  z : Nat
  s : (n : Nat) → Nat
{-# BUILTIN NATURAL Nat #-}

data Fin : Nat → Set₀ where
  z : ∀ {m} → Fin (s m)
  s : ∀ {m} → (i : Fin m) → Fin (s m)

toNat : ∀ {n} → Fin n → Nat
toNat z = z
toNat (s i) = s (toNat i)

∫↓ : ∀ {a b} {X : Set a} → (X → Set b) → Set (a ⊔ b)
∫↓ {X = X} P = ∀ {x} → P x

syntax ∫↓ {X = X} (λ x → P) = ∫↓[ x ∶ X ] P

∫↑ : ∀ {a b} {X : Set a} → (X → Set b) → Set (a ⊔ b)
∫↑ {X = X} P = ∐[ x ∶ X ] P x

syntax ∫↑ {X = X} (λ x → P) = ∫↑[ x ∶ X ] P

Ran
  : ∀ {x c v u p} {𝔵 : Set x} {𝔠 : Set c} {𝔳 : Set v}
  → (𝒸 : 𝔠 → 𝔠 → Set u)
  → (_⋔_ : Set u → 𝔳 → Set p)
  → (G : 𝔵 → 𝔠)
  → (H : 𝔵 → 𝔳)
  → (𝔠 → Set (p ⊔ x))
Ran {𝔵 = 𝔵} 𝒸 _⋔_ G H A = ∫↓[ x ∶ 𝔵 ] ( 𝒸 A (G x) ⋔ H x )

Lan
  : ∀ {x c v u p} {𝔵 : Set x} {𝔠 : Set c} {𝔳 : Set v}
  → (𝒸 : 𝔠 → 𝔠 → Set u)
  → (_⊗_ : 𝔳 → Set u → Set p)
  → (G : 𝔵 → 𝔠)
  → (H : 𝔵 → 𝔳)
  → (𝔠 → Set (p ⊔ x))
Lan {𝔵 = 𝔵} 𝒸 _⊗_ G H A = ∫↑[ x ∶ 𝔵 ] ( H x ⊗ 𝒸 (G x) A )
