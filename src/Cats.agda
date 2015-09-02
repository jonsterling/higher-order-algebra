module Cats where

open import Agda.Primitive

module Types where
  infixl 0 _←_
  infix  0 _~>_
  infix  0 _<~_
  infix  0 Π
  infixr 2 _⋘_
  infixl 2 _⋙_
  infixr 0 _·≪_
  infixl 0 _≫·_
  infixr 8 _,_
  infixr 1 _×_
  infix  0 ⟨_,_⟩
  infix  0 ⟨_×_⟩

  _←_ : ∀ {a b} → Set b → Set a → Set (a ⊔ b)
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
    → (g : (∀ {x} → Π (B x) C))
    → (f : Π A B)
    → ((x : A) → C (f x))
  g ⋘ f = λ x → g (f x)

  _⋙_ : ∀ {a b c}
    → {A : Set a }
    → {B : A → Set b}
    → {C : {x : A} → B x → Set c}
    → (f : Π A B)
    → (g : (∀ {x} → Π (B x) C))
    → ((x : A) → C (f x))
  f ⋙ g = g ⋘ f

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

  record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σ public

  syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

  ᵛ : ∀ {a b c}
    → {A : Set a} {B : A → Set b} {P : Σ A B → Set c}
    → Π[ x ∶ A ] Π[ y ∶ B x ] P (x , y)
    → (∀ x → P x)
  ᵛ p (x , y) = p x y

  _×_ : ∀ {a b} → (A : Set a) (B : Set b) → Set (a ⊔ b)
  A × B = Σ A ·≪ ! B

  ⟨_,_⟩ : ∀ {a b x} {X : Set x} {A : X → Set a} {B : ∀ {x} → A x → Set b}
    → (f : Π X A)
    → Π X (B ⋘ f)
    → ((x : X) → Σ (A x) B)
  ⟨ f , g ⟩ x = f x , g x

  ⟨_×_⟩ : ∀ {a b x₀ x₁} {A : Set a} {B : A → Set b} {X₀ : Set x₀} {X₁ : X₀ → Set x₁}
    → (f : X₀ → A)
    → (X₁ ~> B ⋘ f)
    → (Σ X₀ X₁ → Σ A B)
  ⟨_×_⟩ f g (x , y) = f x , g y

  δ : ∀ {a} {A : Set a} → A → A × A
  δ = ⟨ id , id ⟩

  ↓× : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set (lsuc c)}
    → Π A ·≪ Yo C ⋘ B → (Σ A B → C)
  ↓× f (x , y) = f x y

  ↑⇒ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set (lsuc c)}
    → (Σ A B → C) → Π A ·≪ Yo C ⋘ B
  ↑⇒ f x y = f (x , y)

  record ⊤ i : Set i where
    constructor tt

module Cats where
  module T = Types
  infixr 0 _⇒₀_      -- functor
  infixr 0 _⇏₀_      -- presheaf
  infixr 0 :[_,_]⇒₀_ -- bifunctor
  infixr 0 _:[_]⇏₀_  -- profunctor
  infix  0 id⇒₀      -- functor identity
  infixl 2 _⋘⇒₀_     -- functor composition
  infix  0 _⇊_       -- comma category
  infix  3 _↘_       -- slice category
  infix  3 _↙_       -- coslice category
  infix  3 _↗        -- arrow category
  infix  0 _,:₀_     -- category pairing bifunctor
  infix  0 ⟨-,₀-⟩    -- functor pairing bifunctor
  infix  0 ⟨-×₀-⟩    -- functor pairing bifunctor
  infix  0 ↓×₀       -- functor uncurry
  infix  0 ↑⇒₀       -- functor curry
  infix  0 Hom:₀     -- hom profunctor
  infix  0 !:₀       -- constant profunctor
  infixr 0 _⇒₁_      -- natural transformation
  infixr 0 _:⇏₁_     -- dinatural transformation
  infix  0 id⇒₁      -- natural transformation identity
  infixl 2 _⋘⇒₁_     -- natural transformation composition
  infixr 1 _⇒₀𝒸_     -- functor category
  infixr 2 _×𝒸_      -- product category
  infix  0 Δ:[_]₀    -- wedge
  infix  0 ∇:[_]₀    -- cowedge
  infix  0 ∫↓[_]     -- end
  infix  0 ∫↑[_]     -- coend

  record Category o h : Set (lsuc (o ⊔ h)) where
    field
      {obj} : Set o
      hom : (𝔞 : obj) → (𝔟 : obj) → Set h
      idn : ∀ {𝔞} → hom 𝔞 𝔞
      cmp : ∀ {𝔞 𝔟 𝔠} (g : hom 𝔟 𝔠) (f : hom 𝔞 𝔟) → hom 𝔞 𝔠
  open Category public

  ⊤𝒸 : ∀ o h → Category _ _
  ⊤𝒸 o h = record
    { obj = T.⊤ o
    ; hom = λ _ _ → T.⊤ h
    ; idn = _
    ; cmp = λ _ _ → _
    }

  Set𝒸 : ∀ o → Category _ _
  Set𝒸 o = record
    { obj = Set o
    ; hom = λ A B → A → B
    ; idn = T.id
    ; cmp = λ g f → g T.⋘ f
    }

  Op : ∀ {o h} → Category o h → Category o h
  Op 𝒞 = record
    { obj = obj 𝒞
    ; hom = T.flip (hom 𝒞)
    ; idn = idn 𝒞
    ; cmp = T.flip (cmp 𝒞)
    }

  record _⇒₀_
    {o₀ h₀} {o₁ h₁}
    (𝒞 : Category o₀ h₀)
    (𝒟 : Category o₁ h₁)
    : Set ((o₀ ⊔ h₀) ⊔ (o₁ ⊔ h₁))
    where
      field
        map₀ : (𝔞 : obj 𝒞) → obj 𝒟
        map₁ : ∀ {𝔠₀ 𝔠₁} → (f : hom 𝒞 𝔠₀ 𝔠₁) → hom 𝒟 (map₀ 𝔠₀) (map₀ 𝔠₁)
  open _⇒₀_ public

  _⇏₀_ : ∀ {o₀ h₀} {o₁ h₁}
    → (𝒞 : Category o₀ h₀)
    → (𝒟 : Category o₁ h₁)
    → Set ((o₀ ⊔ h₀) ⊔ (o₁ ⊔ h₁))
  𝒞 ⇏₀ 𝒟 = Op 𝒞 ⇒₀ 𝒟

  record :[_,_]⇒₀_
    {o₀ h₀} {o₁ h₁} {o₂ h₂}
    (𝒞₀ : Category o₀ h₀)
    (𝒞₁ : Category o₁ h₁)
    (𝒟 : Category o₂ h₂)
    : Set ((o₀ ⊔ h₀) ⊔ (o₁ ⊔ h₁) ⊔ (o₂ ⊔ h₂))
    where
      field
        bimap₀ : (𝔞 : obj 𝒞₀) (𝔟 : obj 𝒞₁) → obj 𝒟
        bimap₁ : ∀{𝔠₀₀ 𝔠₀₁ 𝔠₁₀ 𝔠₁₁}
          → (f : hom 𝒞₀ 𝔠₀₀ 𝔠₀₁)
          → (g : hom 𝒞₁ 𝔠₁₀ 𝔠₁₁)
          → hom 𝒟 (bimap₀ 𝔠₀₀ 𝔠₁₀) (bimap₀ 𝔠₀₁ 𝔠₁₁)
  open :[_,_]⇒₀_ public

  _:[_]⇏₀_ : ∀ {o₀ h₀} {o₁ h₁} {o₂ h₂}
    → (𝒞₀ : Category o₀ h₀)
    → (𝒱 : Category o₂ h₂)
    → (𝒟 : Category o₁ h₁)
    → Set ((o₀ ⊔ h₀) ⊔ (o₁ ⊔ h₁) ⊔ (o₂ ⊔ h₂))
  𝒞 :[ 𝒱 ]⇏₀ 𝒟 = :[ Op 𝒟 , 𝒞 ]⇒₀ 𝒱

  record _⇒₁_
    {o₀ h₀} {o₁ h₁}
    {𝒞 : Category o₀ h₀}
    {𝒟 : Category o₁ h₁}
    (F G : 𝒞 ⇒₀ 𝒟)
    : Set ((o₀ ⊔ h₀) ⊔ (o₁ ⊔ h₁))
    where
      field
        com : ∀ {𝔠} → hom 𝒟 (map₀ F 𝔠) (map₀ G 𝔠)
  open _⇒₁_ public

  record _:⇒₁_
    {o₀ h₀} {o₁ h₁}
    {𝒞 : Category o₀ h₀}
    {𝒟 : Category o₁ h₁}
    (F G : :[ 𝒞 , 𝒞 ]⇒₀ 𝒟 )
    : Set ((o₀ ⊔ h₀) ⊔ (o₁ ⊔ h₁))
    where
      field
        bicom : ∀ {𝔠} → hom 𝒟 (bimap₀ F 𝔠 𝔠) (bimap₀ G 𝔠 𝔠)
  open _:⇒₁_ public

  record _:⇏₁_
    {o₀ h₀} {o₁ h₁}
    {𝒞 : Category o₀ h₀}
    {𝒱 : Category o₁ h₁}
    (F G : 𝒞 :[ 𝒱 ]⇏₀ 𝒞)
    : Set ((o₀ ⊔ h₀) ⊔ (o₁ ⊔ h₁))
    where
      field
        dicom : ∀ {𝔠} → hom 𝒱 (bimap₀ F 𝔠 𝔠) (bimap₀ G 𝔠 𝔠)
  open _:⇏₁_ public

  id⇒₀ : ∀ {o h} (𝒞 : Category o h) → 𝒞 ⇒₀ 𝒞
  id⇒₀ 𝒞 = record
    { map₀ = T.id
    ; map₁ = T.id
    }

  _⋘⇒₀_ : ∀ {o₀ h₀} {o₁ h₁} {o₂ h₂}
    → {𝒳 : Category o₀ h₀}
    → {𝒴 : Category o₁ h₁}
    → {𝒵 : Category o₂ h₂}
    → 𝒴 ⇒₀ 𝒵
    → 𝒳 ⇒₀ 𝒴
    → 𝒳 ⇒₀ 𝒵
  G ⋘⇒₀ F = record
    { map₀ = map₀ G T.⋘ map₀ F
    ; map₁ = map₁ G T.⋘ map₁ F
    }

  ! : ∀ {o₀ o₁ h₀ h₁} {𝒞₀ : Category o₀ h₀} {𝒞₁ : Category o₁ h₁}
    → (𝔠 : obj 𝒞₀)
    → 𝒞₁ ⇒₀ 𝒞₀
  ! {𝒞₀ = 𝒞₀} 𝔠 = record
    { map₀ = λ _ → 𝔠
    ; map₁ = λ _ → idn 𝒞₀
    }

  Cat𝒸 : ∀ o h → Category _ _
  Cat𝒸 o h = record
    { obj = Category o h
    ; hom = _⇒₀_
    ; idn = id⇒₀ _
    ; cmp = _⋘⇒₀_
    }

  _⇊_ : ∀ {o₀ o₁ o₂ h₀ h₁ h₂}
    → {𝒞₀ : Category o₀ h₀}
    → {𝒞₁ : Category o₁ h₁}
    → {𝒞₂ : Category o₂ h₂}
    → (F₀ : 𝒞₀ ⇒₀ 𝒞₂)
    → (F₀ : 𝒞₁ ⇒₀ 𝒞₂)
    → Category _ _
  _⇊_ {𝒞₀ = 𝒞₀} {𝒞₁ = 𝒞₁} {𝒞₂ = 𝒞₂} F₀ F₁ = record
    { obj =
        Σ (obj 𝒞₀) λ 𝔞
      → Σ (obj 𝒞₁) λ 𝔟
      → hom 𝒞₂ (map₀ F₀ 𝔞) (map₀ F₁ 𝔟)
    ; hom = λ 𝔞 𝔟
      → hom 𝒞₀ (fst 𝔞) (fst 𝔟)
      × hom 𝒞₁ (fst (snd 𝔞)) (fst (snd 𝔟))
    ; idn = idn 𝒞₀ , idn 𝒞₁
    ; cmp = λ g f → (cmp 𝒞₀ (fst g) (fst f)) , cmp 𝒞₁ (snd g) (snd f)
    } where open Types

  _↘_ : ∀ {o h} (𝒞 : Category o h) (𝔠 : obj 𝒞) → Category _ _
  𝒞 ↘ 𝔠 = id⇒₀ 𝒞 ⇊ ! {𝒞₁ = ⊤𝒸 lzero lzero} 𝔠

  _↙_ : ∀ {o h} (𝒞 : Category o h) (𝔠 : obj 𝒞) → Category _ _
  𝒞 ↙ 𝔠 = ! {𝒞₁ = ⊤𝒸 lzero lzero} 𝔠 ⇊ id⇒₀ 𝒞

  _↗ : ∀ {o h} (𝒞 : Category o h) → _
  𝒞 ↗ = id⇒₀ 𝒞 ⇊ id⇒₀ 𝒞

  id⇒₁ : ∀ {o₀ h₀} {o₁ h₁}
    → {𝒞 : Category o₀ h₀}
    → {𝒟 : Category o₁ h₁}
    → (F : 𝒞 ⇒₀ 𝒟)
    → F ⇒₁ F
  id⇒₁ {𝒟 = 𝒟} F = record { com = idn 𝒟 }

  _⋘⇒₁_ : ∀ {o₀ h₀} {o₁ h₁}
    → {𝒞 : Category o₀ h₀}
    → {𝒟 : Category o₁ h₁}
    → {F : 𝒞 ⇒₀ 𝒟}
    → {G : 𝒞 ⇒₀ 𝒟}
    → {H : 𝒞 ⇒₀ 𝒟}
    → (β : G ⇒₁ H)
    → (α : F ⇒₁ G)
    → F ⇒₁ H
  _⋘⇒₁_ {𝒟 = 𝒟} β α = record { com = cmp 𝒟 (com β) (com α) }

  _⇒₀𝒸_ : ∀ {o₀ h₀} {o₁ h₁}
    → (𝒞 : Category o₀ h₀)
    → (𝒟 : Category o₁ h₁)
    → Category ((o₀ ⊔ h₀) ⊔ ((o₁ ⊔ h₁))) ((o₀ ⊔ h₀) ⊔ ((o₁ ⊔ h₁)))
  𝒞 ⇒₀𝒸 𝒟 = record
    { obj = 𝒞 ⇒₀ 𝒟
    ; hom = _⇒₁_ 
    ; idn = id⇒₁ _
    ; cmp = _⋘⇒₁_
    }

  !⇒₀ : ∀ {o₀ h₀} {o₁ h₁} (𝒞 : Category o₀ h₀) → Cat𝒸 o₁ h₁ ⇒₀ Cat𝒸 o₀ h₀
  !⇒₀ 𝒞 = record { map₀ = T.! 𝒞 ; map₁ = T.! (id⇒₀ 𝒞) }

  _⇏₀𝒸_ : ∀ {o₀ h₀} {o₁ h₁}
    → (𝒞 : Category o₀ h₀)
    → (𝒱 : Category o₁ h₁)
    → Category ((o₀ ⊔ h₀) ⊔ ((o₁ ⊔ h₁))) ((o₀ ⊔ h₀) ⊔ ((o₁ ⊔ h₁)))
  𝒞 ⇏₀𝒸 𝒱 = Op 𝒞 ⇒₀𝒸 𝒱

  Hom:₀ : ∀ {o h} → (𝒞 : Category o h) → 𝒞 :[ Set𝒸 h ]⇏₀ 𝒞
  Hom:₀ 𝒞 = record
    { bimap₀ = hom 𝒞
    ; bimap₁ = λ f g h → cmp 𝒞 g T.·≪ cmp 𝒞 h f
    }

  _×𝒸_ : ∀ {o₀ h₀} {o₁ h₁}
    → Category o₀ h₀
    → Category o₁ h₁
    → Category _ _
  _×𝒸_ 𝒞 𝒟 = record
    { obj = obj 𝒞 T.× obj 𝒟
    ; hom = λ { (𝔞₀ T., 𝔞₁) (𝔟₀ T., 𝔟₁) → hom 𝒞 𝔞₀ 𝔟₀ T.× hom 𝒟 𝔞₁ 𝔟₁ }
    ; idn = idn 𝒞 T., idn 𝒟
    ; cmp = λ { (g₀ T., g₁) (f₀ T., f₁) → cmp 𝒞 g₀ f₀ T., cmp 𝒟 g₁ f₁ }
    }

  fst₀ : ∀ {o₀ h₀} {o₁ h₁}
    → {𝒞₀ : Category o₀ h₀}
    → {𝒞₁ : Category o₁ h₁}
    → (𝒞₀ ×𝒸 𝒞₁) ⇒₀ 𝒞₀
  fst₀ = record
    { map₀ = T.fst
    ; map₁ = T.fst
    }

  snd₀ : ∀ {o₀ h₀} {o₁ h₁}
    → {𝒞₀ : Category o₀ h₀}
    → {𝒞₁ : Category o₁ h₁}
    → 𝒞₀ ×𝒸 𝒞₁ ⇒₀ 𝒞₁
  snd₀ = record
    { map₀ = T.snd
    ; map₁ = T.snd
    }

  _,:₀_ : ∀ {o₀ h₀} {o₁ h₁}
    → (𝒞₀ : Category o₀ h₀)
    → (𝒞₁ : Category o₁ h₁)
    → :[ 𝒞₀ , 𝒞₁ ]⇒₀ 𝒞₀ ×𝒸 𝒞₁
  _,:₀_ 𝒞₀ 𝒞₁ = record
    { bimap₀ = T._,_
    ; bimap₁ = T._,_
    }

  ⟨-,₀-⟩ : ∀ {o₀ h₀} {o₁ h₁} {o₂ h₂}
    → {𝒳 : Category o₀ h₀}
    → {𝒞₀ : Category o₁ h₁}
    → {𝒞₁ : Category o₂ h₂}
    → :[ 𝒳 ⇒₀𝒸 𝒞₀ , 𝒳 ⇒₀𝒸 𝒞₁ ]⇒₀ (𝒳 ⇒₀𝒸 𝒞₀ ×𝒸 𝒞₁)
  ⟨-,₀-⟩ {𝒞₀ = 𝒞₀} = record
    { bimap₀ = λ F G → record
      { map₀ = T.⟨ map₀ F , map₀ G ⟩
      ; map₁ = T.⟨ map₁ F , map₁ G ⟩
      }
    ; bimap₁ = λ β α → record { com = com β T., com α }
    }

  ⟨-×₀-⟩ : ∀ {o₀ h₀} {o₁ h₁} {o₂ h₂} {o₃ h₃}
    → {𝒳₀ : Category o₀ h₀}
    → {𝒳₁ : Category o₁ h₁}
    → {𝒞₀ : Category o₂ h₂}
    → {𝒞₁ : Category o₃ h₃}
    → :[ 𝒳₀ ⇒₀𝒸 𝒞₀ , 𝒳₁ ⇒₀𝒸 𝒞₁ ]⇒₀ (𝒳₀ ×𝒸 𝒳₁) ⇒₀𝒸 (𝒞₀ ×𝒸 𝒞₁)
  ⟨-×₀-⟩ = record
    { bimap₀ = λ F G → bimap₀ ⟨-,₀-⟩ (F ⋘⇒₀ fst₀) (G ⋘⇒₀ snd₀)
    ; bimap₁ = λ β α → record { com = com β T., com α }
    }

  δ₀ : ∀ {o h} → (𝒞 : Category o h) → 𝒞 ⇒₀ 𝒞 ×𝒸 𝒞
  δ₀ 𝒞 = bimap₀ ⟨-,₀-⟩ (id⇒₀ 𝒞) (id⇒₀ 𝒞)

  ↓×₀ : ∀ {o₀ h₀} {o₁ h₁} {o₂ h₂}
    → {𝒞₀ : Category o₀ h₀}
    → {𝒞₁ : Category o₁ h₁}
    → {𝒟 : Category o₂ h₂}
    → (𝒞₀ ×𝒸 𝒞₁ ⇒₀𝒸 𝒟) ⇒₀ (𝒞₀ ⇒₀𝒸 𝒞₁ ⇒₀𝒸 𝒟)
  ↓×₀ {𝒞₀ = 𝒞₀} {𝒞₁ = 𝒞₁} = record
    { map₀ = λ F → record
      { map₀ = λ 𝔵 → record
        { map₀ = λ 𝔶 → map₀ F T.·≪ 𝔵 T., 𝔶
        ; map₁ = λ f → map₁ F T.·≪ idn 𝒞₀ T., f }
      ; map₁ = λ f → record { com = map₁ F T.·≪ f T., idn 𝒞₁ } }
    ; map₁ = λ f → record { com = record { com = com f } }
    }

  ↑⇒₀ : ∀ {o₀ h₀} {o₁ h₁} {o₂ h₂}
    → {𝒞₀ : Category o₀ h₀}
    → {𝒞₁ : Category o₁ h₁}
    → {𝒟 : Category o₂ h₂}
    → 𝒞₀ ⇒₀𝒸 (𝒞₁ ⇒₀𝒸 𝒟) ⇒₀ (𝒞₀ ×𝒸 𝒞₁ ⇒₀𝒸 𝒟)
  ↑⇒₀ {𝒞₀ = 𝒞₀} {𝒞₁ = 𝒞₁} {𝒟 = 𝒟} = record
    { map₀ = λ F → record
      { map₀ = λ { (𝔞 T., 𝔟) → map₀ (map₀ F 𝔞) 𝔟 }
      ; map₁ = λ { (f T., g) → cmp 𝒟 (map₁ (map₀ F _) g) (com T.·≪ map₁ F f) } }
    ; map₁ = λ f → record { com = com T.·≪ com f }
    }

  !:₀ : ∀ {o₀ h₀} {o₁ h₁}
    → {𝒞 : Category o₀ h₀}
    → (𝒱 : Category o₁ h₁)
    → (𝔡 : obj 𝒱)
    → 𝒞 :[ 𝒱 ]⇏₀ 𝒞
  !:₀ 𝒱 𝔡 = record
    { bimap₀ = λ _ _ → 𝔡
    ; bimap₁ = λ _ _ → idn 𝒱 {𝔡}
    }

  Δ:[_]₀ : ∀ {o₀ h₀} {o₁ h₁}
    → {𝒞 : Category o₀ h₀}
    → (𝒱 : Category o₁ h₁)
    → (P : 𝒞 :[ 𝒱 ]⇏₀ 𝒞)
    → (𝔡 : obj 𝒱)
    → Set ((o₀ ⊔ h₀) ⊔ (o₁ ⊔ h₁))
  Δ:[ 𝒱 ]₀ P 𝔡 = (!:₀ 𝒱 𝔡) :⇏₁ P

  record EndV {o₀ h₀} {o₁ h₁}
    {𝒞 : Category o₀ h₀}
    {𝒱 : Category o₁ h₁}
    (P : 𝒞 :[ 𝒱 ]⇏₀ 𝒞)
    : Set ((o₀ ⊔ h₀) ⊔ (o₁ ⊔ h₁))
    where
      field
        end : obj 𝒱
        end-η : Δ:[ 𝒱 ]₀ P end

  ∫↓[_] : ∀ {o₀ h₀ o₁}
    → (𝒞 : Category o₀ h₀)
    → (P : 𝒞 :[ Set𝒸 (o₀ ⊔ o₁) ]⇏₀ 𝒞)
    → EndV P
  ∫↓[ 𝒞 ] P = record
    { end = T.Π[ 𝔠 ∶ obj 𝒞 ] bimap₀ P 𝔠 𝔠
    ; end-η = record { dicom = λ {𝔠} f → f 𝔠 }
    }

  ∇:[_]₀ : ∀ {o₀ h₀} {o₁ h₁}
    → {𝒞 : Category o₀ h₀}
    → (𝒱 : Category o₁ h₁)
    → (P : 𝒞 :[ 𝒱 ]⇏₀ 𝒞)
    → (𝔡 : obj 𝒱)
    → Set ((o₀ ⊔ h₀) ⊔ (o₁ ⊔ h₁))
  ∇:[ 𝒱 ]₀ P 𝔡 = P :⇏₁ (!:₀ 𝒱 𝔡)

  record CoendV {o₀ h₀} {o₁ h₁}
    {𝒞 : Category o₀ h₀}
    {𝒱 : Category o₁ h₁}
    (P : 𝒞 :[ 𝒱 ]⇏₀ 𝒞)
    : Set ((o₀ ⊔ h₀) ⊔ (o₁ ⊔ h₁))
    where
      field
        coend : obj 𝒱
        coend-η : ∇:[ 𝒱 ]₀ P coend

  ∫↑[_] : ∀ {o₀ h₀ o₁}
    → (𝒞 : Category o₀ h₀)
    → (P : 𝒞 :[ Set𝒸 (o₀ ⊔ o₁) ]⇏₀ 𝒞)
    → CoendV P
  ∫↑[ 𝒞 ] P = record
    { coend = T.Σ[ 𝔠 ∶ obj 𝒞 ] bimap₀ P 𝔠 𝔠
    ; coend-η = record { dicom = λ {𝔠} f → 𝔠 T., f }
    }

  id:⇏₀ : ∀ {o h} (𝒞 : Category o h) → 𝒞 :[ Set𝒸 h ]⇏₀ 𝒞
  id:⇏₀ 𝒞 = record
    { bimap₀ = hom 𝒞
    ; bimap₁ = λ f g h → cmp 𝒞 (cmp 𝒞 g h) f
    }

  _⋘:⇏₀_ : ∀ {o}
    → {𝒳 𝒴 𝒵 : Category o o}
    → 𝒴 :[ Set𝒸 o ]⇏₀ 𝒵
    → 𝒳 :[ Set𝒸 o ]⇏₀ 𝒴
    → 𝒳 :[ Set𝒸 o ]⇏₀ 𝒵
  _⋘:⇏₀_ {𝒴 = 𝒴} G F = record
    { bimap₀ = λ 𝔞 𝔟 → T.Σ (obj 𝒴) λ 𝔡 → bimap₀ F 𝔡 𝔟 T.× bimap₀ G 𝔞 𝔡
    ; bimap₁ = λ g f
        → λ { (𝔡 T., 𝔩 T., 𝔯)
        → 𝔡
        T., bimap₁ F (idn 𝒴) f 𝔩
        T., bimap₁ G g (idn 𝒴) 𝔯 }
    }

  Yo⇏₀ : ∀ {o h} (𝒞 : Category o h) → 𝒞 ⇒₀ (𝒞 ⇏₀𝒸 Set𝒸 h)
  Yo⇏₀ 𝒞 = record
    { map₀ = λ 𝔟 → record
      { map₀ = hom (Op 𝒞) 𝔟
      ; map₁ = cmp (Op 𝒞)
      }
    ; map₁ = λ g → record { com = cmp 𝒞 g }
    }

  oY⇏₀ : ∀ {o h} (𝒞 : Category o h) → 𝒞 ⇏₀ (𝒞 ⇒₀𝒸 Set𝒸 h)
  oY⇏₀ 𝒞 = record
    { map₀ = λ 𝔞 → record
      { map₀ = hom 𝒞 𝔞
      ; map₁ = cmp 𝒞
      }
    ; map₁ = λ f → record { com = cmp (Op 𝒞) f }
    }

  Yo:⇏₀ : ∀ {o₀ h₀} {o₁ h₁}
    → {𝒞 : Category o₀ h₀} {𝒟 : Category o₁ h₁}
    → (F : 𝒞 ⇒₀ 𝒟) → 𝒞 :[ Set𝒸 h₁ ]⇏₀ 𝒟
  Yo:⇏₀ {𝒟 = 𝒟} F = record
    { bimap₀ = λ 𝔡 𝔠 → hom 𝒟 𝔡 (map₀ F 𝔠)
    ; bimap₁ = λ f g h → cmp 𝒟 (cmp 𝒟 (map₁ F g) h) f
    }

  Yo:⇍₀ : ∀ {o₀ h₀} {o₁ h₁}
    → {𝒞 : Category o₀ h₀} {𝒟 : Category o₁ h₁}
    → (F : 𝒞 ⇒₀ 𝒟) → 𝒟 :[ Set𝒸 h₁ ]⇏₀ 𝒞
  Yo:⇍₀ {𝒟 = 𝒟} F = record
    { bimap₀ = λ 𝔠 𝔡 → hom 𝒟 (map₀ F 𝔠) 𝔡
    ; bimap₁ = λ f g h → cmp 𝒟 g (cmp 𝒟 h (map₁ F f))
    }

  Profunctor𝒸 : ∀ o → Category _ _
  Profunctor𝒸 o = record
    { obj = Category o o
    ; hom = λ 𝒞 𝒟 → 𝒞 :[ Set𝒸 o ]⇏₀ 𝒟
    ; idn = id:⇏₀ _
    ; cmp = λ {_} {𝒟} G F → G ⋘:⇏₀ F
    }

  ⟨_:[_]₀_⟩ : ∀ {o₀ h₀} {o₁ h₁} {o₂ h₂}
    → {𝒞 : Category o₀ h₀}
    → {𝒟 : Category o₁ h₁}
    → {𝒱 : Category o₂ h₂}
    → (F : 𝒞 ⇒₀ 𝒱)
    → (⊗ : :[ 𝒱  , 𝒱 ]⇒₀ 𝒱)
    → (P : 𝒟 ⇏₀ 𝒱)
    → 𝒞 :[ 𝒱 ]⇏₀ 𝒟
  ⟨ F :[ ⊗ ]₀ P ⟩ = record
    { bimap₀ = λ 𝔡 𝔠 → bimap₀ ⊗ (map₀ P 𝔡) (map₀ F 𝔠)
    ; bimap₁ = λ f g → bimap₁ ⊗ (map₁ P f) (map₁ F g)
    }

  _·⟨_⊗-⟩ : ∀ {o₀ h₀} {o₁ h₁} {o₂ h₂}
    → {𝒞 : Category o₀ h₀}
    → {𝒟 : Category o₁ h₁}
    → {𝒱 : Category o₂ h₂}
    → (P : 𝒞 :[ 𝒱 ]⇏₀ 𝒟) → (𝔞 : obj (Op 𝒟)) → (𝒞 ⇒₀ 𝒱)
  _·⟨_⊗-⟩ {𝒟 = 𝒟} P 𝔞 = record
    { map₀ = bimap₀ P 𝔞
    ; map₁ = bimap₁ P (idn 𝒟)
    }

  _·⟨-⊗_⟩ : ∀ {o₀ h₀} {o₁ h₁} {o₂ h₂}
    → {𝒞 : Category o₀ h₀}
    → {𝒟 : Category o₁ h₁}
    → {𝒱 : Category o₂ h₂}
    → (P : 𝒞 :[ 𝒱 ]⇏₀ 𝒟) → (𝔟 : obj 𝒞) → (𝒟 ⇏₀ 𝒱)
  _·⟨-⊗_⟩ {𝒞 = 𝒞} P 𝔟 = record
    { map₀ = T.flip (bimap₀ P) 𝔟
    ; map₁ = T.flip (bimap₁ P) (idn 𝒞)
    }

  record Closed {o h} (𝒞 : Category o h) : Set (o ⊔ h) where
    field
      ⊸ : 𝒞 :[ 𝒞 ]⇏₀ 𝒞
      ⊸⊤ : obj 𝒞

    lazy : 𝒞 ⇒₀ 𝒞
    lazy = ⊸ ·⟨ ⊸⊤ ⊗-⟩

    dual : 𝒞 ⇏₀ 𝒞
    dual = ⊸ ·⟨-⊗ ⊸⊤ ⟩

    field
      ⊸! : (id⇒₀ 𝒞) ⇒₁ lazy
      ⊸¿ : lazy ⇒₁ (id⇒₀ 𝒞)
      ⊸idn : (!:₀ 𝒞 ⊸⊤) :⇏₁ ⊸

  ClosedSet𝒸 : ∀ {o} → Closed (Set𝒸 o)
  ClosedSet𝒸 {o = o} = record
    { ⊸ = record
      { bimap₀ = λ A B → A → B
      ; bimap₁ = λ f g h x → g (h (f x)) }
    ; ⊸⊤ = T.⊤ o
    ; ⊸! = record { com = T.! }
    ; ⊸¿ = record { com = T.¿ T.tt }
    ; ⊸idn = record { dicom = T.! T.id }
    }

  _↓! : ∀ {o₀ o₁ h₀ h₁ s}
    → {I : Category o₀ h₀}
    → {J : Category o₁ h₁}
    → I ⇒₀ J
    → (I ⇏₀𝒸 Set𝒸 s) ⇒₀ (J ⇏₀𝒸 Set𝒸 _)
  _↓! {I = I} {J = J} f = record
    { map₀ = λ ϕ → record
      { map₀ = λ 𝔧 → Σ[ 𝔦 ∶ obj (Op I) ] (hom (Op J) (map₀ f 𝔦) 𝔧 × map₀ ϕ 𝔦)
      ; map₁ = λ { ρ (𝔦 , mf , ϕ𝔦) → 𝔦 , cmp (Op J) ρ mf , ϕ𝔦 }
      }
    ; map₁ = λ mf₀ → record { com = λ { (𝔦 , mf₁ , ϕ) → 𝔦 , mf₁ , com mf₀ ϕ } }
    } where open Types

  _↑* : ∀ {o₀ o₁ h₀ h₁ s}
    → {I : Category o₀ h₀}
    → {J : Category o₁ h₁}
    → Op J ⇒₀ Op I
    → (I ⇏₀𝒸 Set𝒸 s) ⇒₀ (J ⇏₀𝒸 Set𝒸 _)
  _↑* {I = I} {J = J} f = record
    { map₀ = _⋘⇒₀ f
    ; map₁ = λ mf → record { com = com mf }
    }

  _↓* : ∀ {o₀ o₁ h₀ h₁ s}
    → {I : Category o₀ h₀}
    → {J : Category o₁ h₁}
    → I ⇒₀ J
    → (I ⇏₀𝒸 Set𝒸 s) ⇒₀ (J ⇏₀𝒸 Set𝒸 _)
  _↓* {I = I} {J = J} f = record
    { map₀ = λ ϕ → record
      { map₀ = λ 𝔧 → Π[ 𝔦 ∶ obj (Op I) ] (hom (Op J) 𝔧 (map₀ f 𝔦) → map₀ ϕ 𝔦)
      ; map₁ = λ ρ κ 𝔦 mf → κ 𝔦 (cmp (Op J) mf ρ)
      }
    ; map₁ = λ mf₀ → record { com = λ κ 𝔦 ϕ → com mf₀ (κ 𝔦 ϕ) }
    } where open Types

  ⨕ : ∀ {o h s}
    → {𝒞 : Category o h}
    → (ϕ : 𝒞 ⇏₀ Set𝒸 s)
    → Category _ _
  ⨕ ϕ = Op (! {𝒞₁ = Set𝒸 lzero} (Types.⊤ _) ⇊ ϕ)

  π : ∀ {o h s}
    → {𝒞 : Category o h}
    → (ϕ : 𝒞 ⇏₀ Set𝒸 s)
    → ⨕ ϕ ⇒₀ 𝒞
  π = λ ϕ → record
    { map₀ = T.fst T.⋘ T.snd
    ; map₁ = T.snd
    }

  record RMonad {o₀ o₁ h₀ h₁}
    {𝒞 : Category o₀ h₀}
    {𝒟 : Category o₁ h₁}
    (J : 𝒞 ⇒₀ 𝒟)
    : Set (o₀ ⊔ o₁ ⊔ h₁) where
    field
      G : obj 𝒞 → obj 𝒟
      ret : ∀ {𝔞} → hom 𝒟 (map₀ J 𝔞) (G 𝔞)
      ext : ∀ {𝔞 𝔟} → hom 𝒟 (map₀ J 𝔞) (G 𝔟) → hom 𝒟 (G 𝔞) (G 𝔟)
  open RMonad

  Monad : ∀ {o h} (𝒞 : Category o h) → Set _
  Monad 𝒞 = RMonad (id⇒₀ 𝒞)
