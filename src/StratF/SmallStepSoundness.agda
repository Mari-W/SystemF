module StratF.SmallStepSoundness where

open import Data.Nat.Base using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong-app)

open import StratF.ExpSubstPropertiesSem
open import StratF.ExpSubstitution
open import StratF.Expressions
open import StratF.ExpEnvironments
open import StratF.SmallStep
open import StratF.TypeSubstProperties
open import StratF.TypeSubstPropertiesSem
open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.TypeEnvironments

--! SmallStep >

--! Soundness

soundness : ∀ {T : Type Δ l} {e₁ e₂ : Exp {Δ} Γ T} → e₁ ↪ e₂ →
            (γ : VEnv {Δ} Γ η) → ⟦ e₁ ⟧E γ ≡ ⟦ e₂ ⟧E γ

--! SoundnessProofExcerpt

soundness (β-ƛ {e = e} {v = v}) γ = ⟦ e βƛ ‵val v ⟧E γ
soundness (β-Λ {T = T} {e = e}) γ = ⟦ e βΛ T ⟧E γ
soundness {η = η} (ξ-∙ {T′ = T′} {T = T} e↪e′) γ
  rewrite ⟦ T [ T′ ]Tₛ⟧T η = cong-app (soundness e↪e′ γ) (⟦ T′ ⟧T η)

-- ...

soundness β-s                   γ = refl
soundness (ξ-s e↪e′)            γ = cong suc (soundness e↪e′ γ)
soundness (ξ-·ₗ {e = e} f↪f′)   γ = cong-app (soundness f↪f′ γ) (⟦ e ⟧E γ)
soundness (ξ-·ᵣ {v = v} e↪e′)   γ = cong (⟦ ‵val v ⟧E γ) (soundness e↪e′ γ)

--! MultiStep >

--! Soundness

soundness* : ∀ {T : Type Δ l} {e₁ e₂ : Exp {Δ} Γ T} → e₁ —↠ e₂ →
            (γ : VEnv {Δ} Γ η) → ⟦ e₁ ⟧E γ ≡ ⟦ e₂ ⟧E γ

soundness* —↠-refl              γ = refl
soundness* (—↠-step e₁↪e e—↠e₂) γ = trans (soundness e₁↪e γ) (soundness* e—↠e₂ γ)
