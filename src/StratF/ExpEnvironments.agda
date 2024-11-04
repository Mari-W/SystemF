--{-# OPTIONS --allow-unsolved-metas #-}
module StratF.ExpEnvironments where

open import Level using (Level; zero; _⊔_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_; _×_; ∃-syntax; map₂)
open import Data.Unit.Base using (⊤)
open import Function.Base using (_∘_; id; flip)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; dcong; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.TypeSubstPropertiesSem
open import StratF.TypeSubstProperties
open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.TypeEnvironments

-- MW: in contrast to the original work we do not use the 
-- tskip constructor approach but rather the one hannes explored where we map 
-- a renaming over the whole context Γ 

-- typed term variable environments

data Env (Δ : TEnv) : Set where
  []   : Env Δ
  _∷_  : Type Δ l → Env Δ → Env Δ

Γ-level : Env Δ → Level
Γ-level {Δ = Δ} []      = zero -- Δ-level Δ
Γ-level         (T ∷ Γ) = T-level T ⊔ Γ-level Γ

Γ₀ : Env []
Γ₀ = []

-- functorial action of renamings on environments

ΓRen : (ρ : TRen Δ₁ Δ₂) → Env Δ₁ → Env Δ₂
ΓRen ρ []      = []
ΓRen ρ (T ∷ Γ) = Tren ρ T ∷ ΓRen ρ Γ

⟦_⟧EEᵣ_ : Env Δ₁ → TRen Δ₁ Δ₂ → Env Δ₂
⟦_⟧EEᵣ_ = flip ΓRen

⟦_⟧Γidᵣ≗id : (Γ : Env Δ) → ⟦ Γ ⟧EEᵣ Tidᵣ ≡ Γ
⟦ []    ⟧Γidᵣ≗id = refl
⟦ T ∷ Γ ⟧Γidᵣ≗id = cong₂ _∷_ ⟦ T ⟧Tidᵣ≗id ⟦ Γ ⟧Γidᵣ≗id

Γskipᵣ : Env Δ → Env (l ∷ Δ)
Γskipᵣ = ΓRen Tskipᵣ

syntax Γskipᵣ {l = l} Γ = [ l ]∷ Γ

[_] : ∀ l → Env (l ∷ [])
[ l ] = [ l ]∷ []

variable Γ Γ₁ Γ₂ Γ₂₁ Γ₂₂ : Env Δ

--! inn
data _∈_ : Type Δ l → Env Δ → Set where
  here   : T ∈ (T ∷ Γ)
  there  : T ∈ Γ → T ∈ (T′ ∷ Γ)

-- properties of ⟦_⟧EEᵣ_ wrt _∈_

module _ {Δ₁ Δ₂} (ρ : TRen Δ₁ Δ₂) where

  ΓRen-∈ : T ∈ Γ → (⟦ T ⟧Tᵣ ρ) ∈ (⟦ Γ ⟧EEᵣ ρ)
  ΓRen-∈ here      = here
  ΓRen-∈ (there x) = there (ΓRen-∈ x)

  ΓRen-∈⁻¹ : T′ ∈ (⟦ Γ ⟧EEᵣ ρ) → ∃[ T ] T′ ≡ ⟦ T ⟧Tᵣ ρ × T ∈ Γ
  ΓRen-∈⁻¹ {Γ = T ∷ _} here      = T , refl , here
  ΓRen-∈⁻¹ {Γ = _ ∷ _} (there y) = let T , eq , x = ΓRen-∈⁻¹ y in T , eq , there x

  ΓRen-∈⁻¹∘ΓRen-∈≗id : (T∈Γ : T ∈ Γ) → ΓRen-∈⁻¹ (ΓRen-∈ T∈Γ) ≡ (_ , refl , T∈Γ)
  ΓRen-∈⁻¹∘ΓRen-∈≗id here = refl
  ΓRen-∈⁻¹∘ΓRen-∈≗id (there x) = cong (map₂ (map₂ there)) (ΓRen-∈⁻¹∘ΓRen-∈≗id x)
{-
  ΓRen-∈∘ΓRen-∈⁻¹≗id : (T∈⟦Γ⟧ρ : T′ ∈ (⟦ Γ ⟧EEᵣ ρ)) →
                       let T , eq , T∈Γ = ΓRen-∈⁻¹ T∈⟦Γ⟧ρ in
                       subst (_∈ (⟦ Γ ⟧EEᵣ ρ)) eq T∈⟦Γ⟧ρ ≡ ΓRen-∈ T∈Γ
  ΓRen-∈∘ΓRen-∈⁻¹≗id {Γ = T ∷ _} here      = refl
  ΓRen-∈∘ΓRen-∈⁻¹≗id {Γ = _ ∷ _} (there y)
    -- with T , eq , x ← ΓRen-∈⁻¹ y
    {- rewrite eq -} = dcong there (ΓRen-∈∘ΓRen-∈⁻¹≗id y)
-}

  Γliftᵣ : ∀ l Γ → ΓRen (Tliftᵣ ρ) ([ l ]∷ Γ) ≡ ([ l ]∷ ⟦ Γ ⟧EEᵣ ρ)
  Γliftᵣ l []      = refl
  Γliftᵣ l (T ∷ Γ) = cong₂ _∷_ (swap-Tren-Twk ρ T) (Γliftᵣ l Γ)

⟦_⟧∈-wk : T ∈ Γ → Twk T ∈ ([ l ]∷ Γ)
⟦_⟧∈-wk = ΓRen-∈ Tskipᵣ

⟦_⟧∈-wk⁻¹ : T′ ∈ ([ l ]∷ Γ) → ∃[ T ] T′ ≡ Twk T × T ∈ Γ
⟦_⟧∈-wk⁻¹ = ΓRen-∈⁻¹ Tskipᵣ

-- functorial action of substitutions on environments

ΓSub : (σ : TSub Δ₁ Δ₂) → Env Δ₁ → Env Δ₂
ΓSub σ []      = []
ΓSub σ (T ∷ Γ) = Tsub σ T ∷ ΓSub σ Γ

⟦_⟧EEₛ_ : Env Δ₁ → TSub Δ₁ Δ₂ → Env Δ₂
⟦_⟧EEₛ_ = flip ΓSub

--! DefEidS
⟦_⟧Γidₛ≗id : (Γ : Env Δ) → ⟦ Γ ⟧EEₛ Tidₛ ≡ Γ
⟦ []    ⟧Γidₛ≗id = refl
⟦ T ∷ Γ ⟧Γidₛ≗id = cong₂ _∷_ ⟦ T ⟧Tidₛ≗id ⟦ Γ ⟧Γidₛ≗id

module _ {Δ₁ Δ₂} (σ : TSub Δ₁ Δ₂) where

  ΓSub-∈ : T ∈ Γ → (⟦ T ⟧Tₛ σ) ∈ (⟦ Γ ⟧EEₛ σ)
  ΓSub-∈ here      = here
  ΓSub-∈ (there x) = there (ΓSub-∈ x)

  ΓSub-∈⁻¹ : T′ ∈ (⟦ Γ ⟧EEₛ σ) → ∃[ T ] T′ ≡ ⟦ T ⟧Tₛ σ × T ∈ Γ
  ΓSub-∈⁻¹ {Γ = _ ∷ _} here      = _ , refl , here
  ΓSub-∈⁻¹ {Γ = _ ∷ _} (there y) = let _ , eq , x = ΓSub-∈⁻¹ y in _ , eq , there x

  ΓSub-∈-id : (T∈Γ : T ∈ Γ) → ΓSub-∈⁻¹ (ΓSub-∈ T∈Γ) ≡ (_ , refl , T∈Γ)
  ΓSub-∈-id here      = refl
  ΓSub-∈-id (there x) = cong (map₂ (map₂ there)) (ΓSub-∈-id x)

  Γliftₛ : ∀ l Γ → ⟦ [ l ]∷ Γ ⟧EEₛ Tliftₛ σ ≡ [ l ]∷ ⟦ Γ ⟧EEₛ σ
  Γliftₛ l []      = refl
  Γliftₛ l (T ∷ Γ) = cong₂ _∷_ (swap-Tsub-Twk σ T) (Γliftₛ l Γ)

lemmaΓ : (T : Type Δ l) (Γ : Env Δ) → ΓSub ([ T ]T) ([ l ]∷ Γ) ≡ Γ
lemmaΓ T []       = refl
lemmaΓ T (T′ ∷ Γ) = cong₂ _∷_ (lemmaT T T′) (lemmaΓ T Γ)

-- semantic environments

-- MW: we switch from our functional environment to again heterogenous lists 
-- so we do not need to live in Setω
VEnv ⟦_⟧EE_ : (Γ : Env Δ) (η : ⟦ Δ ⟧TE) → Set (Γ-level Γ)
⟦ []    ⟧EE η = ⊤
⟦ T ∷ Γ ⟧EE η = ⟦ T ⟧T η × ⟦ Γ ⟧EE η

VEnv {Δ} Γ η = ⟦ Γ ⟧EE η

γ₀ : ⟦ Γ₀ ⟧EE η₀
γ₀ = _

variable
  γ γ₁ γ₂ : VEnv {Δ} Γ η

extend-val : {η : ⟦ Δ ⟧TE} {Γ : Env Δ} {T : Type Δ l} →
             ⟦ T ⟧T η → ⟦ Γ ⟧EE η → ⟦ T ∷ Γ ⟧EE η
extend-val v γ = v , γ

syntax extend-val {T = T} v γ = v ∷⟦ T ⟧ γ

-- MW: since we do not have tskip we need to map a weakening over Γ
-- when consing a semtantic type to η
-- similar to our extend-tskip method we the need transfer lemma 
-- that we can either extend the context or weaken the type
extend-typ :  (⟦α⟧ : Set l) → VEnv {Δ} Γ η → ⟦ [ l ]∷ Γ ⟧EE (⟦α⟧ ∷η η)
extend-typ {Γ = []}    {η = _} _   _           = _
extend-typ {Γ = T ∷ _} {η = η} ⟦α⟧ (v∈⟦T⟧ , γ)
  rewrite sym (⟦Twk_⟧T_ T ⟦α⟧ {η = η})
  = v∈⟦T⟧ ∷⟦ Twk T ⟧ extend-typ ⟦α⟧ γ

syntax extend-typ {l = l} T γ = T ∷[ l ] γ

-- lemmas about this?

-- MW: lifting subst-preserves to contexts.
-- note to myself: this cannot be an equality but only an ismorphism since the type is actually different 
-- ⟦ ⟦ Γ ⟧EEₛ σ ⟧EE η has type Set (Γ-level (ΓSub σ Γ))
-- and ⟦ Γ ⟧EE (⟦ η ⟧TETₛ σ) has type Set (Γ-level Γ)
-- which are not necessarily the same.

reindexₛ : (σ : TSub Δ₁ Δ₂) → ⟦ ⟦ Γ ⟧EEₛ σ ⟧EE η → ⟦ Γ ⟧EE (⟦ η ⟧TETₛ σ)
reindexₛ {Γ = Γ} {η = η} σ = go Γ where
  go : ∀ Γ → ⟦ ⟦ Γ ⟧EEₛ σ ⟧EE η → ⟦ Γ ⟧EE ⟦ η ⟧TETₛ σ
  go []      _                                           = _
  go (T ∷ Γ) (v , γ) rewrite subst-preserves {η = η} σ T = v , go Γ γ
  {- v ∷⟦ T ⟧ go Γ γ -- extend at type T -}

reindexₛ⁻¹ : (σ : TSub Δ₁ Δ₂) → ⟦ Γ ⟧EE (⟦ η ⟧TETₛ σ) → ⟦ ⟦ Γ ⟧EEₛ σ ⟧EE η
reindexₛ⁻¹ {Γ = Γ} {η = η} σ = go Γ where
  go : ∀ Γ → ⟦ Γ ⟧EE ⟦ η ⟧TETₛ σ → ⟦ ⟦ Γ ⟧EEₛ σ ⟧EE η
  go []      _                                                 = _
  go (T ∷ Γ) (v , γ) rewrite sym (subst-preserves {η = η} σ T) = v , go Γ γ
  {- v ∷⟦ ⟦ T ⟧Tₛ σ ⟧ go Γ γ -- extend at type ⟦ T ⟧Tₛ σ -}
