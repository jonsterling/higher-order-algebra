module Polynomials where

open import Agda.Primitive
import Containers
module C = Containers
open import Prelude
open import Indexing

infix 0 ⟪_⟫

--------------------------------------------------------------------------------
-- Dependent Polynomials
--------------------------------------------------------------------------------

record Pol {i} (I O : Set i) : Set (lsuc i) where
  field
    {Shp} : Set i
    shp : Shp → O
    bun : Ix 𝔉 i Shp
  Pos = dom bun
  pos = map bun
  field
    nxt : Pos → I
open Pol public

-- extension functors

⟦_⟧ : ∀ {i} {I O : Set i} → Pol I O → (𝔲 : 𝔘) → I [ 𝔲 ]→ O
⟦ 𝔭 ⟧ 𝔲 =
  shp 𝔭 ↓![ 𝔲 ]
  ⋘[ 𝔲 ] pos 𝔭 ↓*[ 𝔲 ]
  ⋘[ 𝔲 ] nxt 𝔭 ↑*[ 𝔲 ]

-- trees

data ⟪_⟫ {i} {O : Set i} (𝔭 : Pol O O) (o : O) : Set i where
  into : ⟦ 𝔭 ⟧ 𝔓 ⟪ 𝔭 ⟫ o → ⟪ 𝔭 ⟫ o

pattern pat p = ._ , p
pattern · = refl
pattern _▹𝔓_ shp d = shp , d , ·
pattern _▹𝔉_ shp d = _ , _ , ((shp , d) , ·) , ·
pattern ret v = (_ , v , ·) , ·

-- conversion between polynomials and containers

P~>C : ∀ {i} → {I O : Set i} → Pol I O → I C.▹ O
P~>C 𝔭 = record
  { shp = inv (shp 𝔭)
  ; pos = inv (pos 𝔭) ⋘ fst ⋘ snd
  ; nxt =      nxt 𝔭  ⋘ fst ⋘ snd
  }

C~>P : ∀ {i} → {I O : Set i} → I C.▹ O → Pol I O
C~>P 𝔠 = record
  { shp = fst
  ; bun = fam (C.pos 𝔠)
  ; nxt = C.nxt 𝔠
  }
