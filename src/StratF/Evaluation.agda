module StratF.Evaluation where

open import Level using (Level)
open import Data.Nat.Base using (suc)

open import StratF.ExpSubstitution
open import StratF.Expressions
open import StratF.ExpEnvironments
open import StratF.Types
open import StratF.TypeEnvironments

--! BigStep >

-- big step call by value semantics (analogous to Benton et al)

Type₀ : Level → Set
Type₀ = Type Δ₀

variable T₀ : Type₀ l

⟦_⟧T₀ : (T : Type₀ l) → Set l
⟦ T₀ ⟧T₀ = ⟦ T₀ ⟧T η₀

--! Val₀ Exp₀
Val₀ Exp₀ : Type₀ l → Set
Val₀ T = Val Γ₀ T
Exp₀ T = Exp Γ₀ T

variable
  v₀ w₀ : Val₀ T₀
  e₀ f₀ : Exp₀ T₀

record EvalAPI : Set₁ where
  infix 15 _↓_
  field
    _↓_ : Exp₀ T₀ → Val₀ T₀ → Set
    ↓-s : e₀ ↓ # n → ‵suc e₀ ↓ # suc n
    ↓-· : f₀ ↓ ƛ e → e₀ ↓ v₀ → e [ ‵val v₀ ]Eₛ ↓ w₀ → f₀ · e₀ ↓ w₀
    ↓-∙ : {e : Exp [ l ] T} → e₀ ↓ Λ l ⇒ e → e [ T₀ ]ETₛ ↓ v₀ → e₀ ∙[ T ] T₀ ↓ v₀
    ↓-v : ‵val v₀ ↓ v₀

