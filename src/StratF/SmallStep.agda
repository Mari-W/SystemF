module StratF.SmallStep where

open import Data.List.Base using (_∷_)
open import Data.Nat.Base using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.Evaluation
open import StratF.ExpSubstitution
open import StratF.Expressions
open import StratF.ExpEnvironments
open import StratF.TypeSubstProperties
open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.TypeEnvironments
open import StratF.Util.Extensionality

-- small step call by value semantics

--! SmallStep >

-- big step semantics
infix 15 _↪_

--! SingleReduction
data _↪_ : Exp {Δ} Γ T → Exp Γ T → Set where

-- β rules

  β-ƛ  : ∀ {v : Val {Δ} Γ T} → let e′ = ‵val v in
         (‵ƛ e) · e′ ↪ e [ e′ ]Eₛ
  β-Λ  : ∀ {T : Type Δ l} {T′ : Type (l ∷ Δ) l′} {e : Exp ([ l ]∷ Γ) T′} →
         (‵Λ l ⇒ e) ∙ T ↪ e [ T ]ETₛ
  β-s  :
         ‵suc {Γ = Γ} (‵# n) ↪ ‵# (suc n)

-- congruence rules

  ξ-·ₗ :
         f ↪ f′ →
         f · e ↪ f′ · e
  ξ-·ᵣ :
         e ↪ e′ → ‵val v · e ↪ ‵val v · e′
  ξ-∙  : ∀ {T′ : Type Δ l′} {T : Type (l′ ∷ Δ) l} {e e′ : Exp Γ ‵∀[ T ]} →
         e ↪ e′ →
         e ∙ T′ ↪ e′ ∙ T′
  ξ-s  :
         e ↪ e′ →
         ‵suc e ↪ ‵suc e′

--! Reduction
infix 15 _—↠_

data _—↠_ : Exp {Δ} Γ T → Exp Γ T → Set where

  —↠-refl :
    e —↠ e
  —↠-step :
    e₁ ↪ e₂ →
    e₂ —↠ e₃ →
    e₁ —↠ e₃

--! Trans
—↠-trans : e₁ —↠ e₂ → e₂ —↠ e₃ → e₁ —↠ e₃
—↠-trans —↠-refl e₂—↠e₃ = e₂—↠e₃
—↠-trans (—↠-step e₁↪e₂ e₁—↠e₂) e₂—↠e₃ = —↠-step e₁↪e₂ (—↠-trans e₁—↠e₂ e₂—↠e₃)

--! SmallStep >

-- Congruence rules lifted over multi-step reduction

‵ξ-s : e₁ —↠ e₂ → ‵suc e₁ —↠ ‵suc e₂
‵ξ-s —↠-refl              = —↠-refl
‵ξ-s (—↠-step e₁↪e e—↠e₂) = —↠-step (ξ-s e₁↪e) (‵ξ-s e—↠e₂)

‵ξ-∙ : e₁ —↠ e₂ → (e₁ ∙ T) —↠ (e₂ ∙ T)
‵ξ-∙ —↠-refl              = —↠-refl
‵ξ-∙ (—↠-step e₁↪e e—↠e₂) = —↠-step (ξ-∙ e₁↪e) (‵ξ-∙ e—↠e₂)

‵β-Λ : e₁ —↠ (‵Λ l ⇒ e) → (e₁ ∙ T) —↠ e [ T ]ETₛ
‵β-Λ —↠-refl                = —↠-step β-Λ —↠-refl
‵β-Λ (—↠-step e₁↪e′ e′—↠Λe) = —↠-step (ξ-∙ e₁↪e′) (‵β-Λ e′—↠Λe)

‵ξ-·ₗ : e₁ —↠ e₂ → (e₁ · e) —↠ (e₂ · e)
‵ξ-·ₗ —↠-refl              = —↠-refl
‵ξ-·ₗ (—↠-step e₁↪e e—↠e₂) = —↠-step (ξ-·ₗ e₁↪e) (‵ξ-·ₗ e—↠e₂)

‵ξ-·ᵣ : e₁ —↠ e₂ → (‵val v · e₁) —↠ (‵val v · e₂)
‵ξ-·ᵣ —↠-refl              = —↠-refl
‵ξ-·ᵣ (—↠-step e₁↪e e—↠e₂) = —↠-step (ξ-·ᵣ e₁↪e) (‵ξ-·ᵣ e—↠e₂)

-- MultiStep API

infix 15 _↓_
--! MultiAPI
_↓_ : Exp₀ T₀ → Val₀ T₀ → Set
e ↓ v = e —↠ ‵val v

--! MultiAPIFunctions
↓-v : ‵val v ↓ v
↓-s : e₀ ↓ # n → ‵suc e₀ ↓ # suc n
↓-· : f₀ ↓ ƛ e → e₀ ↓ v₀ → e [ ‵val v₀ ]Eₛ ↓ w₀ → (f₀ · e₀) ↓ w₀
↓-∙ : e₀ ↓ Λ l ⇒ e → e [ T₀ ]ETₛ ↓ v₀ → (e₀ ∙ T₀) ↓ v₀

--! MultiV
↓-v = —↠-refl

--! MultiS
↓-s —↠-refl             = —↠-step β-s  —↠-refl
↓-s (—↠-step e₁↪e₂ e↓n) = —↠-step (ξ-s e₁↪e₂) (↓-s e↓n)

--! MultiApp
↓-· f₀↓ƛe e₀↓v₀ e[v₀]↓w₀ =
  —↠-trans (‵ξ-·ₗ f₀↓ƛe) (—↠-trans (‵ξ-·ᵣ e₀↓v₀) (—↠-step β-ƛ e[v₀]↓w₀))

--! MultiAPP
↓-∙ e₀↓Λe e[T₀]↓v₀ = —↠-trans (‵β-Λ e₀↓Λe) e[T₀]↓v₀


----------------------------------------------------------------------

evalSmall : EvalAPI
evalSmall = record
            { _↓_ = _↓_
            ; ↓-v = ↓-v
            ; ↓-s = ↓-s
            ; ↓-· = ↓-·
            ; ↓-∙ = ↓-∙
            }
