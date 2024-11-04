--{-# OPTIONS --allow-unsolved-metas #-}
-- This file contains lemmas about expression substitution

module StratF.ExpSubstProperties where

open import Level
open import Data.List.Base using (List; []; _∷_; [_])
open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_; id; _$_)
open import Relation.Binary.Core
  using (REL)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; dcong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-subst; subst-sym-subst; sym-cong;
        module ≡-Reasoning)

subst₂′ : ∀ {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ) {x y u v} →
          x ≡ y → u ≡ v → x ∼ u → y ∼ v
subst₂′ R {x = x} refl = subst (R x)
{-
subst₂′-cong : ∀ {a b c ℓ} {A : Set a} {B : Set b} {C : Set c} (_∼_ : REL A C ℓ) →
               ∀ {x y w z} (f : B → C) →
               x ≡ y → w ≡ z → x ∼ f w → y ∼ f z
subst₂′-cong R = ?
-}

open import StratF.ExpSubstitution
open import StratF.Expressions
open import StratF.ExpEnvironments
open import StratF.TypeSubstProperties
open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.TypeEnvironments
open import StratF.Util.Extensionality
-- open import StratF.Util.SubstProperties

-- ⟦_⟧Eₛ Eidₛ is the identity substitution on expressions/values

postulate -- eliminable via yet more appeals to extensionality?
  EliftₛEidₛ≡Eidₛ : Eliftₛ {Γ₁ = Γ} Eidₛ {T = T} ≡ Eidₛ
  EskipₛEidₛ≡Eidₛ : Eskipₛ {Γ₁ = Γ} Eidₛ {l = l} ≡ Eidₛ

--EliftₛEidₛ≡Eidₛ = {!cong mkEsub $ {!fun-ext₂ λ where here → refl ; (there _) → refl!}!}
--EskipₛEidₛ≡Eidₛ = {!cong mkEsub $ {!fun-ext₂ λ where here → refl ; (there _) → refl!}!}

⟦_⟧Vidₛ≗‵val : (v : Val {Δ} Γ {l} T) → ⟦ v ⟧Vₛ Eidₛ ≡ ‵val v
⟦_⟧Eidₛ≗idE : (e : Exp {Δ} Γ {l} T) → ⟦ e ⟧Eₛ Eidₛ ≡ e

⟦ ‵ x ⟧Vidₛ≗‵val = refl
⟦ # n ⟧Vidₛ≗‵val = refl
⟦ ƛ e ⟧Vidₛ≗‵val = cong ‵ƛ $ begin
  ⟦ e ⟧Eₛ Eliftₛ Eidₛ ≡⟨ cong ⟦ e ⟧Eₛ_ EliftₛEidₛ≡Eidₛ ⟩
  ⟦ e ⟧Eₛ Eidₛ        ≡⟨ ⟦ e ⟧Eidₛ≗idE ⟩
  e                   ∎
  where open ≡-Reasoning
⟦ Λ l ⇒ e ⟧Vidₛ≗‵val = cong ‵Λ l ⇒_ $ begin
  ⟦ e ⟧Eₛ Eskipₛ Eidₛ ≡⟨ cong ⟦ e ⟧Eₛ_ EskipₛEidₛ≡Eidₛ ⟩
  ⟦ e ⟧Eₛ Eidₛ        ≡⟨ ⟦ e ⟧Eidₛ≗idE ⟩
  e                   ∎
  where open ≡-Reasoning

⟦ ‵val v ⟧Eidₛ≗idE = ⟦ v ⟧Vidₛ≗‵val
⟦ ‵suc e ⟧Eidₛ≗idE = cong ‵suc ⟦ e ⟧Eidₛ≗idE
⟦ f · e  ⟧Eidₛ≗idE = cong₂ _·_ ⟦ f ⟧Eidₛ≗idE ⟦ e ⟧Eidₛ≗idE
⟦ e ∙ T′ ⟧Eidₛ≗idE = cong (_∙ T′) ⟦ e ⟧Eidₛ≗idE


-- ⟦_⟧ETₛ Tidₛ is the identity substitution on expressions/values
-- is it that *these* lemmas take us to `subst` hell!?

{-
⟦_⟧VTidₛ≡v : (v : Val {Δ} Γ {l} T) →
             subst₂′ (λ Γ → Val Γ) ⟦ Γ ⟧Γidₛ≡Γ ⟦ T ⟧Tidₛ≡T (⟦ v ⟧VTₛ Tidₛ) ≡ v
⟦_⟧ETidₛ≗idE : (e : Exp {Δ} Γ {l} T) →
             subst₂′ (λ Γ → Exp Γ) ⟦ Γ ⟧Γidₛ≡Γ ⟦ T ⟧Tidₛ≡T (⟦ e ⟧ETₛ Tidₛ) ≡ e

⟦_⟧VTidₛ≡v {Γ = Γ} {T = T} (‵ x) = {!!}ü
⟦_⟧VTidₛ≡v {Γ = Γ} {T = T} (# n) = {!!}
⟦_⟧VTidₛ≡v {Γ = Γ} {T = T} (ƛ x) = {!!}
⟦_⟧VTidₛ≡v {Γ = Γ} {T = ‵∀[ T ]} (Λ l ⇒ e) = {!!}

⟦_⟧ETidₛ≗idE {Γ = Γ} {T = T} (‵val v)
  with eqV ← ⟦ v ⟧VTidₛ≡v = {! !} -- 
⟦_⟧ETidₛ≗idE {Γ = Γ} {T = T} (‵suc e) = {!!}
⟦_⟧ETidₛ≗idE {Γ = Γ} {T = T} (f · e) = {!!}
⟦_⟧ETidₛ≗idE {Γ = Γ} {T = T} (e ∙ T′) = {!!}
  where
  eqΓ = ⟦ Γ ⟧Γidₛ≡Γ
  eqT = ⟦ T ⟧Tidₛ≡T
-}

-- MW: yes! more specifically, we need to additionally prove all fusion lemmas, which is even more annoying.
-- if i remember correctly we use these in the logical relation part (i dont remember where exactly, peter should though):
Γfusionₛₛ : ∀ Γ (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) → (⟦ ⟦ Γ ⟧EEₛ σ₁ ⟧EEₛ σ₂) ≡ (⟦ Γ ⟧EEₛ (σ₁ ∘ₛₛ σ₂)) 
Γfusionₛₛ [] σ₁ σ₂ = refl
Γfusionₛₛ (T ∷ Γ) σ₁ σ₂ = cong₂ _∷_ (fusionₛₛ T σ₁ σ₂) (Γfusionₛₛ Γ σ₁ σ₂)

postulate
  ⟦_⟧VTσ≡v : (v : Val {Δ₁} Γ {l} T) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
               let subst = subst₂′ (λ Γ → Val Γ) (Γfusionₛₛ Γ σ₁ σ₂) (fusionₛₛ T σ₁ σ₂) in
               subst (⟦ ⟦ v ⟧VTₛ σ₁ ⟧VTₛ σ₂) ≡ (⟦ v ⟧VTₛ (σ₁ ∘ₛₛ σ₂))
  ⟦_⟧ETσ≗idE : (e : Exp {Δ₁} Γ {l} T) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
               let subst = subst₂′ (λ Γ → Exp Γ) (Γfusionₛₛ Γ σ₁ σ₂) (fusionₛₛ T σ₁ σ₂) in
               subst (⟦ ⟦ e ⟧ETₛ σ₁ ⟧ETₛ σ₂) ≡ (⟦ e ⟧ETₛ (σ₁ ∘ₛₛ σ₂))
-- obviously this repeats for ᵣᵣ ᵣₛ ₛᵣ .. with according the lifting lemmas

-- general substitution is iterated substitution

lemmaVar* : (σ* : TSub Δ₁ Δ₂) (σ : ESub (⟦ Γ₁  ⟧EEₛ σ*) Γ₂) →
            {T : Type Δ₁ l} (x : T ∈ Γ₁) →
            Vsub* σ* σ (‵ x) ≡ ⟦ ⟦ ‵var x ⟧ETₛ σ* ⟧Eₛ σ
lemmaVar* σ* σ here = refl
lemmaVar* σ* σ (there x) = lemmaVar* σ* (Epopₛ σ) x

lemmaV* : (σ* : TSub Δ₁ Δ₂) (σ : ESub (⟦ Γ₁  ⟧EEₛ σ*) Γ₂) →
          {T : Type Δ₁ l} (v : Val {Δ₁} Γ₁ T) →
          Vsub* σ* σ v ≡ ⟦ ⟦ ‵val v ⟧ETₛ σ* ⟧Eₛ σ

lemmaE* : (σ* : TSub Δ₁ Δ₂) (σ : ESub (⟦ Γ₁  ⟧EEₛ σ*) Γ₂) →
          {T : Type Δ₁ l} (e : Exp {Δ₁} Γ₁ T) →
          Esub* σ* σ e ≡ ⟦ ⟦ e ⟧ETₛ σ* ⟧Eₛ σ

lemmaV* σ* σ (‵ x) = lemmaVar* σ* σ x
lemmaV* σ* σ (# n) = refl
lemmaV* σ* σ (ƛ e) = cong ‵ƛ (lemmaE* σ* (Eliftₛ σ) e)
lemmaV* {Γ₁ = Γ₁} σ* σ (Λ l ⇒ e)
  with ih ← lemmaE* (Tliftₛ σ*) (Egskipₛ σ* σ) e
  with lhs ← Esub* (Tliftₛ σ*) (Egskipₛ σ* σ) e
  with rhs ← ⟦ e ⟧ETₛ Tliftₛ σ*
  rewrite Γliftₛ σ* l Γ₁
  = cong (‵Λ l ⇒_) ih

lemmaE* σ* σ (‵val v) = lemmaV* σ* σ v
lemmaE* σ* σ (‵suc e) = cong ‵suc (lemmaE* σ* σ e)
lemmaE* σ* σ (f · e)  = cong₂ _·_ (lemmaE* σ* σ f) (lemmaE* σ* σ e)
lemmaE* σ* σ (e ∙[ T ] T′) 
  rewrite swap-Tsub-[] σ* T T′
  = cong (_∙ (⟦ T′ ⟧Tₛ σ*)) (lemmaE* σ* σ e)

-- Esub* Tidₛ σ simulates substitution ⟦_⟧Eₛ σ on expressions/values
-- 'up to ⟦_⟧ETₛ Tidₛ

⟦_⟧Esub*Tidₛ≗Eₛ_ : (e : Exp {Δ} Γ₁ {l} T) (σ : ESub (⟦ Γ₁  ⟧EEₛ Tidₛ) Γ₂) →
                   Esub* Tidₛ σ e ≡ ⟦ ⟦ e ⟧ETₛ Tidₛ ⟧Eₛ σ
⟦ e ⟧Esub*Tidₛ≗Eₛ σ = lemmaE* Tidₛ σ e

-- Esub* Tidₛ Eidₛ is the identity type substitution on expressions/values

⟦_⟧Esub*TidₛEidₛ≗idE : (e : Exp {Δ} Γ {l} T) → Esub* Tidₛ Eidₛ e ≡ ⟦ e ⟧ETₛ Tidₛ
⟦ e ⟧Esub*TidₛEidₛ≗idE = begin
  Esub* Tidₛ Eidₛ e   ≡⟨ ⟦ e ⟧Esub*Tidₛ≗Eₛ Eidₛ ⟩
  ⟦ ⟦e⟧ETidₛ ⟧Eₛ Eidₛ ≡⟨ ⟦ ⟦e⟧ETidₛ ⟧Eidₛ≗idE ⟩
  ⟦e⟧ETidₛ            ∎
  where
  open ≡-Reasoning
  ⟦e⟧ETidₛ = ⟦ e ⟧ETₛ Tidₛ

-- identity substitution does nothing...

⟦_⟧ETidₛ : (e : Exp {Δ} Γ {l} T) → Exp {Δ} Γ {l} T
⟦_⟧ETidₛ {Γ = Γ} {T = T} e
  with e′ ← ⟦ e ⟧ETₛ Tidₛ
  rewrite ⟦ Γ ⟧Γidₛ≗id
  rewrite ⟦ T ⟧Tidₛ≗id
  = e′
{-
⟦_⟧ETidₛ≗idE : (e : Exp {Δ} Γ {l} T) → ⟦ e ⟧ETidₛ ≡ e
⟦_⟧ETidₛ≗idE {Γ = Γ} {T = T} e
  rewrite ⟦ Γ ⟧Γidₛ≗id
  rewrite ⟦ T ⟧Tidₛ≗id
  --with ⟦ e ⟧ETidₛ in eq
   = {!eq!}
-}
 