module StratF.Types where

open import Level
open import Data.List.Base using (_∷_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl)

open import StratF.TypeEnvironments

-- level-stratified types, relative to a type environment Δ

-- types

-- MW: the defintion of types remains the same as before 
data Type Δ : Level → Set where
  ‵ℕ     : Type Δ zero
  ‵_     : l ∈ᵗ Δ → Type Δ l
  _‵⇒_   : Type Δ l → Type Δ l′ → Type Δ (l ⊔ l′)
  ‵∀[_]  : Type (l ∷ Δ) l′ → Type Δ (suc l ⊔ l′)

pattern ‵∀_⇒_ l {l′ = l′} T = ‵∀[_] {l = l} {l′ = l′} T

variable T T′ T₁ T₂ : Type Δ l

-- level of type according to Leivant'91
T-level : Type Δ l → Level
T-level {l = l} _ = l

-- the meaning of a stratified type in terms of Agda universes

-- helper function (because `_→_` isn't a first-class function name!)

_⟦⇒⟧_ : Set l → Set l′ → Set (l ⊔ l′)
A ⟦⇒⟧ B = A → B

-- MW: the semantic interpretation of types also remains the same but 
-- the semtantic environment does not live in ω
--! TSem
⟦_⟧T_ : (T : Type Δ l) → ⟦ Δ ⟧TE → Set l
⟦ ‵ℕ       ⟧T η = ℕ
⟦ ‵ α      ⟧T η = ⟦‵ α ⟧T η
⟦ T₁ ‵⇒ T₂ ⟧T η = ⟦ T₁ ⟧T η → ⟦ T₂ ⟧T η
⟦ ‵∀[ T ]  ⟧T η = ∀ ⟦α⟧ → ⟦ T ⟧T (⟦α⟧ ∷η η) -- `Set l` is inferrable

-- the interpretation function is stable wrt _∼_

⟦_⟧T∼_ : (T : Type Δ l) {η₁ η₂ : ⟦ Δ ⟧TE} → η₁ ∼ η₂ → ⟦ T ⟧T η₁ ≡ ⟦ T ⟧T η₂
⟦ T ⟧T∼ η₁∼η₂ with refl ← ∼⇒≡ η₁∼η₂ = refl

