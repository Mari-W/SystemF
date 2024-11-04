module StratF.TypeSubstitution where

open import Level
open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; [] ; _∷_)
open import Function using (_∘_; id; flip; _$_)

open import StratF.TypeEnvironments
open import StratF.Types

--! Sub >

-- renaming on types

-- functional representation

-- MW: this is our original definition
TREN : (Δ₁ Δ₂ : TEnv) → Set
TREN Δ₁ Δ₂ = ∀ {l} → l ∈ᵗ Δ₁ → l ∈ᵗ Δ₂

-- equivalent to 'closure' form

module _ (ρ : TREN (l ∷ Δ₁) Δ₂) where

  popᵣ : TREN Δ₁ Δ₂
  popᵣ = ρ ∘ there

  topᵣ : l ∈ᵗ Δ₂
  topᵣ = ρ here

-- MW: there is an isomorphism between functional and list representation
tabulateᵣ : TREN Δ₁ Δ₂ → All (_∈ᵗ Δ₂) Δ₁
tabulateᵣ {Δ₁ = []}    _ = []
tabulateᵣ {Δ₁ = _ ∷ _} ρ = topᵣ ρ ∷ tabulateᵣ (popᵣ ρ)

lookupᵣ : All (_∈ᵗ Δ₂) Δ₁ → TREN Δ₁ Δ₂
lookupᵣ (α ∷ ρ) = λ where here → α ; (there x) → lookupᵣ ρ x

-- MW: abstract interface for renamings
-- allows to switch between representations easily
--! DefTRen
record TRen (Δ₁ Δ₂ : TEnv) : Set where
  constructor mkTRen
  field
    tren : TREN Δ₁ Δ₂

  TR-level : Level
  TR-level = (Δ-level Δ₁) ⊔ (Δ-level Δ₂)

-- make TREN definitions into manifest fields

  wkᵣ : TREN Δ₁ (l ∷ Δ₂)
  wkᵣ = there ∘ tren

  liftᵣ : TREN (l ∷ Δ₁) (l ∷ Δ₂)
  liftᵣ here      = here
  liftᵣ (there α) = there $ tren α


open TRen public using (tren)

-- then instantiate those definitions at top-level

module _ (ρ : TRen Δ₁ Δ₂) where

  open TRen ρ

  Twkᵣ : TRen Δ₁ (l ∷ Δ₂)
  tren Twkᵣ = wkᵣ

  Tliftᵣ : TRen (l ∷ Δ₁) (l ∷ Δ₂)
  tren Tliftᵣ = liftᵣ


variable
  ρ* ρ*₁ ρ*₂ : TRen Δ₁ Δ₂

--! DefTidR
Tidᵣ : TRen Δ Δ
tren Tidᵣ = id

Tskipᵣ : TRen Δ (l ∷ Δ)
tren Tskipᵣ = there

Tpopᵣ : TRen (l ∷ Δ₁) Δ₂ → TRen Δ₁ Δ₂
tren (Tpopᵣ ρ*) = popᵣ $ tren ρ*

Ttopᵣ : TRen (l ∷ Δ₁) Δ₂ → l ∈ᵗ Δ₂
Ttopᵣ ρ* = topᵣ $ tren ρ*

--! DefTren

Tren : TRen Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
Tren ρ* (‵ α)      = ‵ tren ρ* α
Tren ρ* (T₁ ‵⇒ T₂) = Tren ρ* T₁ ‵⇒ Tren ρ* T₂
Tren ρ* ‵∀[ T ]    = ‵∀[ Tren (Tliftᵣ ρ*) T ]
Tren ρ* ‵ℕ         = ‵ℕ

-- MW: in a sense applying a renaming to a type is also fits some abstract definition of semtantics, 
-- i.e. traversing the type and going under binders, etc.
-- this termonolgy stems from the universe paper and is explained there in more detail
⟦_⟧Tᵣ_ : Type Δ₁ l → TRen Δ₁ Δ₂ → Type Δ₂ l
⟦_⟧Tᵣ_ = flip Tren

Twk : Type Δ l′ → Type (l ∷ Δ) l′
Twk = Tren Tskipᵣ

-- substitution on types

TSUB : (Δ₁ Δ₂ : TEnv) → Set
TSUB Δ₁ Δ₂ = ∀ {l} → l ∈ᵗ Δ₁ → Type Δ₂ l

module _ (σ : TSUB (l ∷ Δ₁) Δ₂) where

  popₛ : TSUB Δ₁ Δ₂
  popₛ = σ ∘ there

  topₛ : Type Δ₂ l
  topₛ = σ here

tabulateₛ : TSUB Δ₁ Δ₂ → All (Type Δ₂) Δ₁
tabulateₛ {Δ₁ = []}    _ = []
tabulateₛ {Δ₁ = _ ∷ _} σ = topₛ σ ∷ tabulateₛ (popₛ σ)

lookupₛ : All (Type Δ₂) Δ₁ → TSUB Δ₁ Δ₂
lookupₛ (α ∷ σ) = λ where here → α ; (there x) → lookupₛ σ x

--! DefTSub
record TSub (Δ₁ Δ₂ : TEnv) : Set where
  constructor mkTSub
  field
    tsub : TSUB Δ₁ Δ₂

  TS-level : Level
  TS-level = (Δ-level Δ₁) ⊔ (Δ-level Δ₂)

-- make TSUB definitions into manifest fields

  wkₛ : TSUB Δ₁ (l ∷ Δ₂)
  wkₛ = Twk ∘ tsub

  liftₛ : TSUB (l ∷ Δ₁) (l ∷ Δ₂)
  liftₛ here      = ‵ here
  liftₛ (there α) = Twk $ tsub α

  extₛ : Type Δ₂ l → TSUB (l ∷ Δ₁) Δ₂
  extₛ T here      = T
  extₛ T (there α) = tsub α


open TSub public using (tsub)

-- then instantiate those definitions at top-level

module _ (σ* : TSub Δ₁ Δ₂) where

  open TSub σ*

  Twkₛ : TSub Δ₁ (l ∷ Δ₂)
  tsub Twkₛ = wkₛ

  Tliftₛ : TSub (l ∷ Δ₁) (l ∷ Δ₂)
  tsub Tliftₛ = liftₛ

  Textₛ : Type Δ₂ l → TSub (l ∷ Δ₁) Δ₂
  tsub (Textₛ T) = extₛ T


variable
  σ* σ*₁ σ*₂ : TSub Δ₁ Δ₂
  τ* τ*₁ τ*₂ : TSub Δ Δ₀

--! DefTidS
Tidₛ : TSub Δ Δ

tsub Tidₛ = ‵_

Tpopₛ : TSub (l ∷ Δ₁) Δ₂ → TSub Δ₁ Δ₂
tsub (Tpopₛ σ*) = popₛ $ tsub σ*

Ttopₛ : TSub (l ∷ Δ₁) Δ₂ → Type Δ₂ l
Ttopₛ σ* = topₛ $ tsub σ*

--! DefTsub

Tsub : TSub Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
Tsub σ* (‵ α)      = tsub σ* α
Tsub σ* (T₁ ‵⇒ T₂) = Tsub σ* T₁ ‵⇒ Tsub σ* T₂
Tsub σ* ‵∀[ T ]    = ‵∀[ Tsub (Tliftₛ σ*) T ]
Tsub σ* ‵ℕ         = ‵ℕ

⟦_⟧Tₛ_ : Type Δ₁ l → TSub Δ₁ Δ₂ → Type Δ₂ l
⟦_⟧Tₛ_ = flip Tsub

infixr 5 _∷Tₛ_

_∷Tₛ_ : Type Δ₂ l → TSub Δ₁ Δ₂ → TSub (l ∷ Δ₁) Δ₂
T ∷Tₛ σ = Textₛ σ T

-- a single type gives rise to a substitution

[_]T : Type Δ l → TSub (l ∷ Δ) Δ
[ T ]T = T ∷Tₛ Tidₛ

-- which can then be packaged as binary operation

_[_]Tₛ : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
_[_]Tₛ T T' = ⟦ T ⟧Tₛ [ T' ]T

-- renamings give rise to substitutions

TR⇒TS : TRen Δ₁ Δ₂ → TSub Δ₁ Δ₂
tsub (TR⇒TS ρ) = ‵_ ∘ tren ρ

-- composition of renamings and substitutions

--! DefTCompositionRR
_∘ᵣᵣ_ : TRen Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TRen Δ₁ Δ₃
tren (ρ₁ ∘ᵣᵣ ρ₂) = tren ρ₂ ∘ tren ρ₁

--! DefTCompositionRS
_∘ᵣₛ_ : TRen Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
tsub (ρ ∘ᵣₛ σ) = tsub σ ∘ tren ρ

--! DefTCompositionSR
_∘ₛᵣ_ : TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
tsub (σ ∘ₛᵣ ρ) = ⟦_⟧Tᵣ ρ ∘ tsub σ

--! DefTCompositionSS
_∘ₛₛ_ : TSub Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
tsub (σ₁ ∘ₛₛ σ₂) = ⟦_⟧Tₛ σ₂ ∘ tsub σ₁

