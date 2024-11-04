-- This file contains definitions and lemmas about semantic renamings
-- and substitutions of types.

module StratF.TypeSubstPropertiesSem where

open import Level
open import Data.List using (List; []; _∷_)
open import Data.Product.Base using (_,_; proj₂)
open import Function.Base using (_∘_; _$_; flip)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.TypeEnvironments
open import StratF.Types
open import StratF.TypeSubstitution
open import StratF.TypeSubstProperties
open import StratF.Util.Extensionality

private variable
  ρ ρ₁ ρ₂ ρ′ : TRen Δ₁ Δ₂
  σ σ₁ σ₂ σ′ : TSub Δ₁ Δ₂

--! TF >

-- the (functorial!) action of type renaming on semantic type environments

-- MW: this differs to our approach in the paper.
-- instead of relating two environments using equalities between its contents under a renaming (TRen*),
-- we apply the renaming to the semantic environment similar to what we do in the paper for substiution.
-- note to myself: i do the same thing in my latest implementation that uses REWRITE: 
-- https://github.com/Mari-W/IntrinsicTypes/blob/ba6d74ef3cd8170aec528dc4aa47d4b574e5d04c/Rewrite/SystemF.agda#L482C1-L482C2
⟦_⟧TETᵣ_ : (η : ⟦ Δ₂ ⟧TE) (ρ : TRen Δ₁ Δ₂) → ⟦ Δ₁ ⟧TE
⟦ η ⟧TETᵣ ρ = ⟦ ⟦ η ⟧TE⇒TEω ∘ tren ρ ⟧TEω⇒TE

TRen* : (ρ : TRen Δ₁ Δ₂) (η : ⟦ Δ₂ ⟧TE) → ⟦ Δ₁ ⟧TE
TRen* ρ η = ⟦ η ⟧TETᵣ ρ

-- for which the following equational properties are provable

wkᵣ∈Ren* : (η : ⟦ Δ ⟧TE) (⟦α⟧ : Set l) → ⟦ ⟦α⟧ ∷η η ⟧TETᵣ Tskipᵣ ≡ η
wkᵣ∈Ren* η ⟦α⟧ = ⟦ η ⟧TE⇒TEω∘TEω⇒TE≗id

Tren*-id : (η : ⟦ Δ ⟧TE) → ⟦ η ⟧TETᵣ Tidᵣ ≡ η
Tren*-id η = ⟦ η ⟧TE⇒TEω∘TEω⇒TE≗id

Tren*-pop : (ρ : TRen (l ∷ Δ₁) Δ₂) (η : ⟦ Δ₂ ⟧TE) →
            ⟦ η ⟧TETᵣ Tpopᵣ ρ ≡ proj₂ (⟦ η ⟧TETᵣ ρ)
Tren*-pop ρ η = ⟦ (λ _ → refl) ⟧TEω⇒TE-ext

Tren*-lift : ∀ {ρ : TRen Δ₁ Δ₂} {η : ⟦ Δ₂ ⟧TE} (⟦α⟧ : Set l) →
             ⟦ ⟦α⟧ ∷η η ⟧TETᵣ Tliftᵣ ρ ≡ ⟦α⟧ ∷η ⟦ η ⟧TETᵣ ρ
Tren*-lift _ = refl

--! RenPreservesSemanticsType
Tren*-preserves-⟦‵_⟧T : {ρ : TRen Δ₁ Δ₂} {η : ⟦ Δ₂ ⟧TE} (α : l ∈ᵗ Δ₁) →
                        ⟦‵ tren ρ α ⟧T η ≡ ⟦‵ α ⟧T ⟦ η ⟧TETᵣ ρ
Tren*-preserves-⟦‵ α ⟧T = sym (⟦ α ⟧TEω⇒TE∘TE⇒TEω≗id)

Tren*-preserves-⟦_⟧T : {ρ : TRen Δ₁ Δ₂} {η : ⟦ Δ₂ ⟧TE} (T : Type Δ₁ l) →
                          ⟦ ⟦ T ⟧Tᵣ ρ ⟧T η ≡ ⟦ T ⟧T ⟦ η ⟧TETᵣ ρ
Tren*-preserves-⟦ ‵ℕ      ⟧T  = refl
Tren*-preserves-⟦ ‵ α     ⟧T  = sym (⟦ α ⟧TEω⇒TE∘TE⇒TEω≗id)
Tren*-preserves-⟦ T₁ ‵⇒ T₂ ⟧T = cong₂ _⟦⇒⟧_ (Tren*-preserves-⟦ T₁ ⟧T) (Tren*-preserves-⟦ T₂ ⟧T)
Tren*-preserves-⟦ ‵∀[ T ] ⟧T  = dep-ext λ ⟦α⟧ → Tren*-preserves-⟦ T ⟧T

Tpop-σ≡Twk∘σ : (σ* : TSub (l ∷ Δ₁) Δ₂) → Tpopₛ σ* ≡ Tskipᵣ ∘ᵣₛ σ*
Tpop-σ≡Twk∘σ σ* = cong mkTSub $ fun-ext₂ λ _ → refl

⟦Twk_⟧T_  : (T : Type Δ l) (⟦α⟧ : Set l′) {η : ⟦ Δ ⟧TE} →
            ⟦ Twk T ⟧T (⟦α⟧ ∷η η) ≡ ⟦ T ⟧T η
⟦Twk_⟧T_ T ⟦α⟧ {η = η} = begin
  ⟦ Twk T ⟧T (⟦α⟧ ∷η η)            ≡⟨ Tren*-preserves-⟦ T ⟧T ⟩
  ⟦ T ⟧T (TRen* Tskipᵣ (⟦α⟧ ∷η η)) ≡⟨ cong ⟦ T ⟧T_ ⟦ η ⟧TE⇒TEω∘TEω⇒TE≗id ⟩
  ⟦ T ⟧T η                         ∎

-- the functorial action of substitution on semantic environments

-- MW: analogously to renamings (and like we did it in the paper)

--! substToEnv
⟦_⟧TETₛ_ : ⟦ Δ₂ ⟧TE → TSub Δ₁ Δ₂ → ⟦ Δ₁ ⟧TE
⟦ η ⟧TETₛ σ = ⟦ ⟦_⟧T η ∘ tsub σ ⟧TEω⇒TE

subst-to-env* : TSub Δ₁ Δ₂ → ⟦ Δ₂ ⟧TE → ⟦ Δ₁ ⟧TE
subst-to-env* = flip ⟦_⟧TETₛ_

--! substVarPreservesType
subst-var-preserves : (σ : TSub Δ₁ Δ₂) (η : ⟦ Δ₂ ⟧TE) (α : l ∈ᵗ Δ₁) →
                      ⟦‵ α ⟧T (⟦ η ⟧TETₛ σ) ≡ ⟦ tsub σ α ⟧T η
subst-var-preserves _ _ α = ⟦ α ⟧TEω⇒TE∘TE⇒TEω≗id

apply-env-var : ∀ (σ₀ : TSub Δ []) (α : l ∈ᵗ Δ) →
                ⟦‵ α ⟧T (⟦ η₀ ⟧TETₛ σ₀) ≡ ⟦ tsub σ₀ α ⟧T η₀
apply-env-var σ₀ = subst-var-preserves σ₀ η₀

τ*∈Ren* : (ρ : TRen Δ₁ Δ₂) (σ₀ : TSub Δ₂ []) →
          ⟦ ⟦ η₀ ⟧TETₛ σ₀ ⟧TETᵣ ρ ≡ ⟦ η₀ ⟧TETₛ (ρ ∘ᵣₛ σ₀)
τ*∈Ren* ρ σ₀ = ⟦ subst-var-preserves σ₀ η₀ ∘ tren ρ ⟧TEω⇒TE-ext

subst-to-env*-wk : (σ : TSub Δ₁ Δ₂) (⟦α⟧ : Set l) {η : ⟦ Δ₂ ⟧TE} →
                   ⟦ ⟦α⟧ ∷η η ⟧TETₛ Twkₛ σ ≡ ⟦ η ⟧TETₛ σ
subst-to-env*-wk σ ⟦α⟧ = ⟦ ⟦Twk_⟧T ⟦α⟧ ∘ tsub σ ⟧TEω⇒TE-ext

subst-to-env*-id : (η : ⟦ Δ ⟧TE) → subst-to-env* Tidₛ η ≡ η
subst-to-env*-id η = Tren*-id η

subst-preserves : (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l) →
                  ⟦ ⟦ T ⟧Tₛ σ ⟧T η ≡ ⟦ T ⟧T ⟦ η ⟧TETₛ σ
subst-preserves σ ‵ℕ         = refl
subst-preserves σ (‵ α)      = sym (subst-var-preserves σ _ α)
subst-preserves σ (T₁ ‵⇒ T₂) = cong₂ _⟦⇒⟧_ (subst-preserves σ T₁) (subst-preserves σ T₂)
subst-preserves σ ‵∀[ T ]    = dep-ext λ ⟦α⟧ → begin
  ⟦ Tsub (Tliftₛ σ) T ⟧T (⟦α⟧ ∷η _) ≡⟨ subst-preserves (Tliftₛ σ) T ⟩
  ⟦ T ⟧T ⟦ ⟦α⟧ ∷η _ ⟧TETₛ Tliftₛ σ  ≡⟨ cong (⟦ T ⟧T_ ∘ (⟦α⟧ ∷η_)) (subst-to-env*-wk σ ⟦α⟧) ⟩
  ⟦ T ⟧T (⟦α⟧ ∷η (⟦ _ ⟧TETₛ σ))     ∎

subst-to-env*-comp : (σ : TSub Δ₁ Δ₂) (τ : TSub Δ₂ Δ₃) {η : ⟦ Δ₃ ⟧TE} →
                     ⟦ ⟦ η ⟧TETₛ τ ⟧TETₛ σ ≡ ⟦ η ⟧TETₛ (σ ∘ₛₛ τ)
subst-to-env*-comp σ τ = ⟦ sym ∘ subst-preserves τ ∘ tsub σ ⟧TEω⇒TE-ext

--! SingleSubstPreserves
⟦_[_]Tₛ⟧T_ : (T : Type (l ∷ Δ) l′) (T′ : Type Δ l) (η : ⟦ Δ ⟧TE) →
             ⟦ T [ T′ ]Tₛ ⟧T η ≡ ⟦ T ⟧T (⟦ T′ ⟧T η ∷η η)

⟦ T [ T′ ]Tₛ⟧T η = trans
  (subst-preserves [ T′ ]T T)
  (cong (⟦ T ⟧T_ ∘ (⟦ T′ ⟧T η ∷η_)) ⟦ η ⟧TE⇒TEω∘TEω⇒TE≗id)
