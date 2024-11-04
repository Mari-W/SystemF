module StratF.TypeSubstProperties where

open import Level
open import Data.List.Base using (List; []; _∷_)
open import Function.Base using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; _≗_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.TypeEnvironments
open import StratF.Util.Extensionality

private variable
  ρ ρ₁ ρ₂ ρ′ : TRen Δ₁ Δ₂
  σ σ₁ σ₂ σ′ : TSub Δ₁ Δ₂

-- MW: nothing really changed here we prove fusion and corolloraries following from fusion as usual

--! TF >

-- fusion lemmas: interaction of renamings and substitutions

-- ren-ren

-- postulated

ren↑-dist-∘ᵣᵣ : (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
                Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂) {l = l} ≡ Tliftᵣ ρ₁ ∘ᵣᵣ Tliftᵣ ρ₂
ren↑-dist-∘ᵣᵣ ρ₁ ρ₂ = cong mkTRen $ fun-ext₂ λ where here → refl ; (there _) → refl

-- derived: mutual recursion between the main function and its `Lift`ed version

fusionᵣᵣ : (T : Type Δ₁ l) (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
           ⟦ ⟦ T ⟧Tᵣ ρ₁ ⟧Tᵣ ρ₂ ≡ ⟦ T ⟧Tᵣ (ρ₁ ∘ᵣᵣ ρ₂)

fusionᵣᵣ↑ : (T : Type (l ∷ Δ₁) l′) (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
            ⟦ ⟦ T ⟧Tᵣ Tliftᵣ ρ₁ ⟧Tᵣ Tliftᵣ ρ₂ ≡ ⟦ T ⟧Tᵣ Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂)
fusionᵣᵣ↑ T ρ₁ ρ₂ = begin
    ⟦ ⟦ T ⟧Tᵣ Tliftᵣ ρ₁ ⟧Tᵣ Tliftᵣ ρ₂
  ≡⟨ fusionᵣᵣ T (Tliftᵣ ρ₁) (Tliftᵣ ρ₂) ⟩
    ⟦ T ⟧Tᵣ (Tliftᵣ ρ₁ ∘ᵣᵣ Tliftᵣ ρ₂)
  ≡⟨ cong ⟦ T ⟧Tᵣ_ (ren↑-dist-∘ᵣᵣ ρ₁ ρ₂) ⟨
    ⟦ T ⟧Tᵣ Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂)
  ∎

--! FusionRenRen

fusionᵣᵣ ‵ℕ         ρ₁ ρ₂ = refl
fusionᵣᵣ (‵ _)      ρ₁ ρ₂ = refl
fusionᵣᵣ (T₁ ‵⇒ T₂) ρ₁ ρ₂ = cong₂ _‵⇒_ (fusionᵣᵣ T₁ ρ₁ ρ₂) (fusionᵣᵣ T₂ ρ₁ ρ₂)
fusionᵣᵣ ‵∀[ T ]    ρ₁ ρ₂ = cong ‵∀[_] (fusionᵣᵣ↑ T ρ₁ ρ₂)

--! SwapTrenTwk
swap-Tren-Twk : (ρ : TRen Δ₁ Δ₂) (T : Type Δ₁ l′) →
                ⟦ Twk T ⟧Tᵣ Tliftᵣ ρ ≡ Twk {l = l} (⟦ T ⟧Tᵣ ρ)

swap-Tren-Twk ρ T = begin
    ⟦ Twk T ⟧Tᵣ Tliftᵣ ρ
  ≡⟨ fusionᵣᵣ T Tskipᵣ (Tliftᵣ ρ) ⟩
    ⟦ T ⟧Tᵣ (Tskipᵣ ∘ᵣᵣ Tliftᵣ ρ)
  ≡⟨ fusionᵣᵣ T ρ Tskipᵣ ⟨
    Twk (⟦ T ⟧Tᵣ ρ)
  ∎

-- sub-ren

-- postulated

sub↑-dist-∘ᵣₛ : (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
                Tliftₛ (ρ ∘ᵣₛ σ) {l = l} ≡ Tliftᵣ ρ ∘ᵣₛ Tliftₛ σ
sub↑-dist-∘ᵣₛ ρ σ = cong mkTSub $ fun-ext₂ λ where here → refl ; (there _) → refl

-- derived

fusionᵣₛ : (T : Type Δ₁ l) (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
           ⟦ ⟦ T ⟧Tᵣ ρ ⟧Tₛ σ ≡ ⟦ T ⟧Tₛ (ρ ∘ᵣₛ σ)

fusionᵣₛ↑ : (T : Type (l ∷ Δ₁) l′) (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
            ⟦ ⟦ T ⟧Tᵣ Tliftᵣ ρ ⟧Tₛ Tliftₛ σ ≡ ⟦ T ⟧Tₛ Tliftₛ (ρ ∘ᵣₛ σ)

--! FusionSubRen

fusionᵣₛ ‵ℕ         ρ σ = refl
fusionᵣₛ (‵ _)      ρ σ = refl
fusionᵣₛ (T₁ ‵⇒ T₂) ρ σ = cong₂ _‵⇒_ (fusionᵣₛ T₁ ρ σ) (fusionᵣₛ T₂ ρ σ)
fusionᵣₛ ‵∀[ T ]    ρ σ = cong ‵∀[_] (fusionᵣₛ↑ T ρ σ)

fusionᵣₛ↑ T ρ σ = begin
    ⟦ ⟦ T ⟧Tᵣ Tliftᵣ ρ ⟧Tₛ Tliftₛ σ
  ≡⟨ fusionᵣₛ T (Tliftᵣ ρ) (Tliftₛ σ) ⟩
    ⟦ T ⟧Tₛ (Tliftᵣ ρ ∘ᵣₛ Tliftₛ σ)
  ≡⟨ cong ⟦ T ⟧Tₛ_ (sub↑-dist-∘ᵣₛ ρ σ) ⟨
    ⟦ T ⟧Tₛ Tliftₛ (ρ ∘ᵣₛ σ)
  ∎

-- ren-sub

-- postulated

ren↑-dist-∘ₛᵣ : (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
  Tliftₛ (σ ∘ₛᵣ ρ) {l = l} ≡ Tliftₛ σ ∘ₛᵣ Tliftᵣ ρ
ren↑-dist-∘ₛᵣ {l = l} σ ρ = cong mkTSub $ fun-ext₂ λ where
  here → refl
  (there x) → sym (swap-Tren-Twk ρ (tsub σ x))

-- derived

fusionₛᵣ : (T : Type Δ₁ l) (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
           ⟦ ⟦ T ⟧Tₛ σ ⟧Tᵣ ρ ≡ ⟦ T ⟧Tₛ (σ ∘ₛᵣ ρ)

fusionₛᵣ↑ : (T : Type (l ∷ Δ₁) l′) (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
            ⟦ ⟦ T ⟧Tₛ Tliftₛ σ ⟧Tᵣ Tliftᵣ ρ ≡ ⟦ T ⟧Tₛ Tliftₛ (σ ∘ₛᵣ ρ)

fusionₛᵣ↑ T σ ρ = begin
    ⟦ ⟦ T ⟧Tₛ Tliftₛ σ ⟧Tᵣ Tliftᵣ ρ
  ≡⟨ fusionₛᵣ T (Tliftₛ σ) (Tliftᵣ ρ) ⟩
    ⟦ T ⟧Tₛ (Tliftₛ σ ∘ₛᵣ Tliftᵣ ρ)
  ≡⟨ cong ⟦ T ⟧Tₛ_ (ren↑-dist-∘ₛᵣ σ ρ) ⟨
    ⟦ T ⟧Tₛ Tliftₛ (σ ∘ₛᵣ ρ)
  ∎

--! FusionRenSub
fusionₛᵣ ‵ℕ         ρ σ = refl
fusionₛᵣ (‵ _)      ρ σ = refl
fusionₛᵣ (T₁ ‵⇒ T₂) ρ σ = cong₂ _‵⇒_ (fusionₛᵣ T₁ ρ σ) (fusionₛᵣ T₂ ρ σ)
fusionₛᵣ ‵∀[ T ]    ρ σ = cong ‵∀[_] (fusionₛᵣ↑ T ρ σ)

--! SwapTsubTwk
swap-Tsub-Twk : (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l′) →
                ⟦ Twk T ⟧Tₛ Tliftₛ σ ≡ Twk {l = l} (⟦ T ⟧Tₛ σ)

swap-Tsub-Twk σ T =
  begin
    ⟦ Twk T ⟧Tₛ Tliftₛ σ
  ≡⟨ fusionᵣₛ T Tskipᵣ (Tliftₛ σ) ⟩
    ⟦ T ⟧Tₛ (σ ∘ₛᵣ Tskipᵣ)
  ≡⟨ fusionₛᵣ T σ Tskipᵣ ⟨
    Twk (⟦ T ⟧Tₛ σ)
  ∎

-- sub-sub

-- postulated

sub↑-dist-∘ₛₛ : (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
  Tliftₛ (σ₁ ∘ₛₛ σ₂) {l = l} ≡ Tliftₛ σ₁ ∘ₛₛ Tliftₛ σ₂
sub↑-dist-∘ₛₛ σ₁ σ₂ = cong mkTSub $ fun-ext₂ λ where
  here → refl
  (there x) → sym (swap-Tsub-Twk σ₂ (tsub σ₁ x))

-- derived

--! FusionSubSub
fusionₛₛ : (T : Type Δ₁ l) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
           ⟦ ⟦ T ⟧Tₛ σ₁ ⟧Tₛ σ₂ ≡ ⟦ T ⟧Tₛ (σ₁ ∘ₛₛ σ₂)

fusionₛₛ↑ : ∀ (T : Type (l ∷ Δ₁) l′) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
            ⟦ ⟦ T ⟧Tₛ Tliftₛ σ₁ ⟧Tₛ Tliftₛ σ₂ ≡ ⟦ T ⟧Tₛ Tliftₛ (σ₁ ∘ₛₛ σ₂)
fusionₛₛ↑ {l = l} T σ₁ σ₂ = begin
    ⟦ ⟦ T ⟧Tₛ Tliftₛ σ₁ ⟧Tₛ Tliftₛ σ₂
  ≡⟨ fusionₛₛ T (Tliftₛ σ₁) (Tliftₛ σ₂) ⟩
    ⟦ T ⟧Tₛ (Tliftₛ σ₁ ∘ₛₛ Tliftₛ σ₂)
  ≡⟨ cong ⟦ T ⟧Tₛ_ (sub↑-dist-∘ₛₛ σ₁ σ₂) ⟨
    ⟦ T ⟧Tₛ Tliftₛ (σ₁ ∘ₛₛ σ₂)
  ∎

fusionₛₛ ‵ℕ         σ₁ σ₂ = refl
fusionₛₛ (‵ _)      σ₁ σ₂ = refl
fusionₛₛ (T₁ ‵⇒ T₂) σ₁ σ₂ = cong₂ _‵⇒_ (fusionₛₛ T₁ σ₁ σ₂) (fusionₛₛ T₂ σ₁ σ₂)
fusionₛₛ ‵∀[ T ]    σ₁ σ₂ = cong ‵∀[_] (fusionₛₛ↑ T σ₁ σ₂)

-- other lemmas

TliftᵣTidᵣ≡Tidᵣ : Tliftᵣ {Δ₁ = Δ} Tidᵣ {l = l} ≡ Tidᵣ
TliftᵣTidᵣ≡Tidᵣ = cong mkTRen $ fun-ext₂ λ { here → refl ; (there _) → refl }

--! TidRNeutral
⟦_⟧Tidᵣ≗id : (T : Type Δ l) → ⟦ T ⟧Tᵣ Tidᵣ ≡ T
⟦ ‵ℕ       ⟧Tidᵣ≗id  = refl
⟦ ‵ _      ⟧Tidᵣ≗id  = refl
⟦ T₁ ‵⇒ T₂ ⟧Tidᵣ≗id  = cong₂ _‵⇒_ ⟦ T₁ ⟧Tidᵣ≗id ⟦ T₂ ⟧Tidᵣ≗id
⟦ ‵∀[ T ]  ⟧Tidᵣ≗id  = cong ‵∀[_] (trans (cong (⟦ T ⟧Tᵣ_) TliftᵣTidᵣ≡Tidᵣ) ⟦ T ⟧Tidᵣ≗id)

ρ[T]≡[ρT]ρ↑ : (T : Type Δ₁ l) (ρ : TRen Δ₁ Δ₂) →
              [ T ]T ∘ₛᵣ ρ ≡ (Tliftᵣ ρ) ∘ᵣₛ [ ⟦ T ⟧Tᵣ ρ ]T
ρ[T]≡[ρT]ρ↑ T ρ = cong mkTSub $ fun-ext₂ λ { here → refl ; (there _) → refl }

--! SwapTrenSingle
swap-Tren-[] : (ρ : TRen Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
               ⟦ T [ T′ ]Tₛ ⟧Tᵣ ρ ≡ (⟦ T ⟧Tᵣ Tliftᵣ ρ) [ ⟦ T′ ⟧Tᵣ ρ ]Tₛ

swap-Tren-[] ρ T T′ = begin
    ⟦ T [ T′ ]Tₛ ⟧Tᵣ ρ
  ≡⟨ fusionₛᵣ T [ T′ ]T ρ ⟩
    ⟦ T ⟧Tₛ ([ T′ ]T ∘ₛᵣ ρ)
  ≡⟨ cong (⟦ T ⟧Tₛ_) (ρ[T]≡[ρT]ρ↑ T′ ρ) ⟩
    ⟦ T ⟧Tₛ (Tliftᵣ ρ ∘ᵣₛ [ ⟦ T′ ⟧Tᵣ ρ ]T)
  ≡⟨ fusionᵣₛ T (Tliftᵣ ρ) [ ⟦ T′ ⟧Tᵣ ρ ]T ⟨
    (⟦ T ⟧Tᵣ Tliftᵣ ρ) [ ⟦ T′ ⟧Tᵣ ρ ]Tₛ
  ∎

TliftₛTidₛ≡Tidₛ : Tliftₛ {Δ₁ = Δ} Tidₛ {l = l} ≡ Tidₛ
TliftₛTidₛ≡Tidₛ = cong mkTSub $ fun-ext₂ λ where here → refl ; (there _) → refl

--! TidSNeutral
⟦_⟧Tidₛ≗id : (T : Type Δ l) → ⟦ T ⟧Tₛ Tidₛ ≡ T
⟦ ‵ℕ       ⟧Tidₛ≗id  = refl
⟦ ‵ _      ⟧Tidₛ≗id  = refl
⟦ T₁ ‵⇒ T₂ ⟧Tidₛ≗id  = cong₂ _‵⇒_ ⟦ T₁ ⟧Tidₛ≗id ⟦ T₂ ⟧Tidₛ≗id
⟦ ‵∀[ T ]  ⟧Tidₛ≗id  = cong ‵∀[_] (trans (cong (⟦ T ⟧Tₛ_) TliftₛTidₛ≡Tidₛ) ⟦ T ⟧Tidₛ≗id)


σ[T]≡[σT]σ↑ : (T : Type Δ₁ l) (σ : TSub Δ₁ Δ₂) →
              [ T ]T ∘ₛₛ σ ≡ Tliftₛ σ ∘ₛₛ [ ⟦ T ⟧Tₛ σ ]T
σ[T]≡[σT]σ↑ T σ = cong mkTSub $ fun-ext₂ λ where
  here → refl
  (there x) → sym (trans (fusionᵣₛ (tsub σ x) Tskipᵣ [ ⟦ T ⟧Tₛ σ ]T) ⟦ _ ⟧Tidₛ≗id)

∘ᵣₛ-neutralˡ : (σ : TSub Δ₁ Δ₂) → Tidᵣ ∘ᵣₛ σ ≡ σ
∘ᵣₛ-neutralˡ σ = refl

∘ₛᵣ-neutralʳ : (σ : TSub Δ₁ Δ₂) → σ ∘ₛᵣ Tidᵣ ≡ σ
∘ₛᵣ-neutralʳ σ = cong mkTSub $ fun-ext₂ λ α → ⟦ tsub σ α ⟧Tidᵣ≗id

∘ₛₛ-neutralˡ :  (σ* : TSub Δ₁ Δ₂) → Tidₛ ∘ₛₛ σ* ≡ σ*
∘ₛₛ-neutralˡ σ* = refl

∘ₛₛ-neutralʳ : (σ* : TSub Δ₁ Δ₂) → σ* ∘ₛₛ Tidₛ ≡ σ*
∘ₛₛ-neutralʳ σ* = cong mkTSub $ fun-ext₂ λ α → ⟦ tsub σ* α ⟧Tidₛ≗id

--! SwapTsubSingle
swap-Tsub-[] : (σ : TSub Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
               ⟦ T [ T′ ]Tₛ ⟧Tₛ σ ≡ (⟦ T ⟧Tₛ Tliftₛ σ) [ ⟦ T′ ⟧Tₛ σ ]Tₛ

swap-Tsub-[] σ T T′ = begin
    ⟦ T [ T′ ]Tₛ ⟧Tₛ σ
  ≡⟨ fusionₛₛ T [ T′ ]T σ ⟩
    ⟦ T ⟧Tₛ ([ T′ ]T ∘ₛₛ σ)
  ≡⟨ cong ⟦ T ⟧Tₛ_ (σ[T]≡[σT]σ↑ T′ σ) ⟩
    ⟦ T ⟧Tₛ (Tliftₛ σ ∘ₛₛ [ ⟦ T′ ⟧Tₛ σ ]T)
  ≡⟨ fusionₛₛ T (Tliftₛ σ) [ ⟦ T′ ⟧Tₛ σ ]T ⟨
    (⟦ T ⟧Tₛ Tliftₛ σ) [ ⟦ T′ ⟧Tₛ σ ]Tₛ
  ∎

Tskipᵣ∘Textₛ : {T : Type Δ₂ l} (σ : TSub Δ₁ Δ₂) → Tskipᵣ ∘ᵣₛ (T ∷Tₛ σ) ≡ σ
Tskipᵣ∘Textₛ _ = refl

σT≡TextₛσTwkT : {T′ : Type Δ₂ l′} (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l) →
                ⟦ Twk T ⟧Tₛ (T′ ∷Tₛ σ) ≡ ⟦ T ⟧Tₛ σ
σT≡TextₛσTwkT {T′ = T′} σ T = fusionᵣₛ T Tskipᵣ (T′ ∷Tₛ σ)

lemmaT : (T′ : Type Δ l′) (T : Type Δ l) → ⟦ Twk T ⟧Tₛ [ T′ ]T ≡ T
lemmaT T′ T = trans (σT≡TextₛσTwkT {T′ = T′} Tidₛ T) ⟦ T ⟧Tidₛ≗id

Tliftₛ∘Textₛ : (τ* : TSub Δ []) (T′ : Type [] l) →
               Tliftₛ τ* ∘ₛₛ [ T′ ]T ≡ Textₛ τ* T′
Tliftₛ∘Textₛ τ* T′ = cong mkTSub $ fun-ext₂ λ where
  here → refl
  (there x) → lemmaT T′ (tsub τ* x)


T[T′]T≡Tidₛ↑T[T′]T : (T : Type (l′ ∷ Δ) l) (T′ : Type Δ l′) →
                     T [ T′ ]Tₛ ≡ (⟦ T ⟧Tₛ Tliftₛ Tidₛ) [ T′ ]Tₛ
T[T′]T≡Tidₛ↑T[T′]T T T′ = begin
    T [ T′ ]Tₛ
  ≡⟨ cong _[ T′ ]Tₛ ⟦ T ⟧Tidₛ≗id  ⟨
    (⟦ T ⟧Tₛ Tidₛ) [ T′ ]Tₛ
  ≡⟨ cong _[ T′ ]Tₛ ((cong (⟦ T ⟧Tₛ_)) TliftₛTidₛ≡Tidₛ) ⟨
    (⟦ T ⟧Tₛ Tliftₛ Tidₛ) [ T′ ]Tₛ
  ∎

Text-sub-sub : (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l) →
               ⟦ T ⟧Tₛ σ ∷Tₛ σ ≡ ([ T ]T ∘ₛₛ σ)
Text-sub-sub σ T = cong mkTSub $ fun-ext₂ λ { here → refl ; (there _) → refl }

[_]∘ₛₛ_ : (T : Type Δ₁ l) (σ* : TSub Δ₁ Δ₂) →
          ⟦ T ⟧Tₛ σ* ∷Tₛ σ* ≡ ([ T ]T ∘ₛₛ σ*)
[ T ]∘ₛₛ σ = cong mkTSub $ fun-ext₂ λ { here → refl ; (there _) → refl }
