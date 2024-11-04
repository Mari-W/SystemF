-- This file proves that a big step reduction is equivalent to
-- a multi-small-step reduction to a value.

module StratF.BigEqSmall where

open import StratF.Evaluation
open import StratF.BigStep
open import StratF.SmallStep

----------------------------------------------------------------------

--! BigToSmall
⇓to↓ : e₀ ⇓ v₀ → e₀ ↓ v₀
⇓to↓ ⇓-v                        = ↓-v
⇓to↓ (⇓-s e⇓#n)                 = ↓-s (⇓to↓ e⇓#n)
⇓to↓ (⇓-· f₀⇓ƛe e₀⇓v₀ e[v₀]⇓w₀) = ↓-· (⇓to↓ f₀⇓ƛe) (⇓to↓  e₀⇓v₀) (⇓to↓ e[v₀]⇓w₀)
⇓to↓ (⇓-∙ e₀⇓Λe e[T₀]⇓v₀)       = ↓-∙ (⇓to↓ e₀⇓Λe) (⇓to↓ e[T₀]⇓v₀)

--! SmallToBig

-- closure under small-step *expansion*

-- MW: this also shows the backwards direction which we didnt show

-- β small steps correspond to instance of big-step with trivial ⇓-v steps
↪∘⇓⇒⇓ : e₀ ↪ f₀ → f₀ ⇓ v₀ → e₀ ⇓ v₀
↪∘⇓⇒⇓ β-ƛ = ⇓-· ⇓-v ⇓-v
↪∘⇓⇒⇓ β-Λ = ⇓-∙ ⇓-v
↪∘⇓⇒⇓ β-s ⇓-v = ⇓-s ⇓-v

-- ξ small steps correspond one-for-one by inversion of the corresponding ξ big step
↪∘⇓⇒⇓ (ξ-·ₗ p) (⇓-· q q₁ q₂) = ⇓-· (↪∘⇓⇒⇓ p q) q₁ q₂
↪∘⇓⇒⇓ (ξ-·ᵣ p) (⇓-· q q₁ q₂) = ⇓-· q (↪∘⇓⇒⇓ p q₁) q₂
↪∘⇓⇒⇓ (ξ-∙ p)  (⇓-∙ q q₁)    = ⇓-∙ (↪∘⇓⇒⇓ p q) q₁
↪∘⇓⇒⇓ (ξ-s p)  (⇓-s q)       = ⇓-s (↪∘⇓⇒⇓ p q)

↓to⇓ : e₀ ↓ v₀ → e₀ ⇓ v₀
↓to⇓ —↠-refl               = ⇓-v
↓to⇓ (—↠-step e₀↪e₁ e₁⇓v₀) = ↪∘⇓⇒⇓ e₀↪e₁ (↓to⇓ e₁⇓v₀)

