-- This file proves that the big-step semantics is sound wrt. the
-- denotational semantics, going via the small-step soundness proof

module StratF.BigStepSoundness where

open import Data.Nat.Base using (suc)
open import Relation.Binary.PropositionalEquality
  -- using (_≡_; refl; cong; cong-app; module ≡-Reasoning)
  using (_≡_)

open import StratF.Evaluation
open import StratF.BigStep
--open import StratF.SmallStep
open import StratF.SmallStepSoundness using (soundness*)
open import StratF.BigEqSmall
--open import StratF.ExpSubstPropertiesSem
open import StratF.ExpSubstitution
open import StratF.Expressions
open import StratF.ExpEnvironments

--! BigStep >

--! SoundnessType
soundness : e₀ ⇓ v₀ → ⟦ e₀ ⟧E γ₀ ≡ ⟦ v₀ ⟧V γ₀

--! Soundness

soundness e₀⇓v₀ = soundness* (⇓to↓ e₀⇓v₀) γ₀

{- -- redundant! -- -}
{-
soundness ⇓-v                        = refl
soundness (⇓-s e⇓v)                  = cong suc (soundness e⇓v)
soundness {e₀ = f₀ · e₀} {v₀ = w₀} (⇓-· {e = e} {v₀ = v₀} f₀⇓ƛe e₀⇓v₀ e[v₀]⇓w₀) =
  begin
    ⟦ f₀ ⟧E γ₀ (⟦ e₀ ⟧E γ₀)
  ≡⟨ cong-app (soundness f₀⇓ƛe) (⟦ e₀ ⟧E γ₀) ⟩
    ⟦ ƛ e ⟧V γ₀ (⟦ e₀ ⟧E γ₀)
  ≡⟨ cong (⟦ ƛ e ⟧V γ₀) (soundness e₀⇓v₀) ⟩
    ⟦ ƛ e ⟧V γ₀ (⟦ v₀ ⟧V γ₀)
  ≡⟨ ⟦ e βƛ ‵val v₀ ⟧E γ₀ ⟩
    ⟦ e [ ‵val v₀ ]Eₛ ⟧E γ₀
  ≡⟨ soundness e[v₀]⇓w₀ ⟩
    ⟦ w₀ ⟧V γ₀
  ∎ where open ≡-Reasoning
soundness {e₀ = _∙_ {l = l} e₀ T₀} (⇓-∙ {e = e} {v₀ = v₀} e₀⇓Λe e[T₀]⇓v₀) =
  begin
    ⟦ e₀ ∙ T₀ ⟧E γ₀
  ≡⟨ soundness* (‵ξ-∙ (⇓to↓ e₀⇓Λe)) γ₀ ⟩
    ⟦ (‵Λ l ⇒ e) ∙ T₀ ⟧E γ₀
  ≡⟨ (⟦ e βΛ T₀ ⟧E γ₀) ⟩
    ⟦ e [ T₀ ]ETₛ ⟧E γ₀
  ≡⟨ soundness e[T₀]⇓v₀ ⟩
    ⟦ v₀ ⟧V γ₀
  ∎ where open ≡-Reasoning
-}
