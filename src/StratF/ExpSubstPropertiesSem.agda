{-# OPTIONS --allow-unsolved-metas #-}
-- This file contains definitions and lemmas about semantic renamings
-- and substitutions of expressions.

module StratF.ExpSubstPropertiesSem where

open import Level
open import Data.List.Base using (_∷_)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_; id; _$_; flip)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; dcong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-subst; subst-sym-subst; sym-cong;
        module ≡-Reasoning)
open ≡-Reasoning

open import StratF.ExpSubstProperties
open import StratF.ExpSubstitution
open import StratF.Expressions
open import StratF.ExpEnvironments
open import StratF.TypeSubstProperties
open import StratF.TypeSubstPropertiesSem
open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.TypeEnvironments
open import StratF.Util.Extensionality

-- semantic substitutions on expressions: Frobenius commutations
-- coherence wrt type-and-term substitution via Esub*/Esub
-- is this where the authors' 'scourge' starts to bite!?

lemmaV : (σ* : TSub Δ₁ Δ₂) (σ : ESub (⟦ Γ₁  ⟧EEₛ σ*) Γ₂) →
         {T : Type Δ₁ l} (v : Val {Δ₁} Γ₁ T) →
         {η₂ : ⟦ Δ₂ ⟧TE} (γ₂ : VEnv {Δ₂} Γ₂ η₂) →
         ⟦ Vsub* σ* σ v ⟧E γ₂ ≡ ⟦ ⟦ ⟦ ‵val v ⟧ETₛ σ* ⟧Eₛ σ ⟧E γ₂

lemmaE : (σ* : TSub Δ₁ Δ₂) (σ : ESub (⟦ Γ₁  ⟧EEₛ σ*) Γ₂) →
         {T : Type Δ₁ l} (e : Exp {Δ₁} Γ₁ T) →
         {η₂ : ⟦ Δ₂ ⟧TE} (γ₂ : VEnv {Δ₂} Γ₂ η₂) →
         ⟦ Esub* σ* σ e ⟧E γ₂ ≡ ⟦ ⟦ ⟦ e ⟧ETₛ σ* ⟧Eₛ σ ⟧E γ₂

lemmaV σ* σ v γ = cong (λ e → ⟦ e ⟧E γ) (lemmaV* σ* σ v)
lemmaE σ* σ v γ = cong (λ e → ⟦ e ⟧E γ) (lemmaE* σ* σ v)




--! EEsingleSubstPreserves
⟦_βƛ_⟧E_ : -- equation holds at type ⟦ T′ ⟧T η
           ∀ {T : Type Δ l} {T′ : Type Δ l′} →
           (e₁ : Exp (T ∷ Γ) T′) (e₂ : Exp {Δ} Γ T) →
           (γ : VEnv {Δ} Γ η) → ⟦ (‵ƛ e₁) · e₂ ⟧E γ ≡ ⟦ e₁ [ e₂ ]Eₛ ⟧E γ
{-
Esubst-preserves : ∀ {T : Type Δ₁ l} {η₂ : Env* Δ₂} {γ₂ : Env Δ₂ Γ₂ η₂} {σ* : TSub Δ₁ Δ₂}
  → (σ : ESub σ* Γ₁ Γ₂) (e : Expr Δ₁ Γ₁ T)
  → E⟦ Esub σ* σ e ⟧ η₂ γ₂ ≡ subst id (sym (subst-preserves σ* T)) (E⟦ e ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂))

-}
⟦_βƛ_⟧E_ {Δ = Δ} {l = l} {l′ = l′} {Γ = Γ} {η = η} {T = T} {T′ = T′} e₁ e₂ γ = {!!}

{-
⟦_βƛ_⟧E_ {Δ = Δ} {l = l} {l′ = l′} {Γ = Γ} {η = η} {T = T} {T′ = T′} (‵val v) e₂ γ = {!!}
⟦_βƛ_⟧E_ {Δ = Δ} {l = l} {l′ = l′} {Γ = Γ} {η = η} {T = T} {T′ = T′} (‵suc e₁) e₂ γ = {!!}
⟦_βƛ_⟧E_ {Δ = Δ} {l = l} {l′ = l′} {Γ = Γ} {η = η} {T = T} {T′ = T′} (e₁ · e₃) e₂ γ = {!!}
⟦_βƛ_⟧E_ {Δ = Δ} {l = l} {l′ = l′} {Γ = Γ} {η = η} {T = T} {T′ = T′} (e₁ ∙ T′₁) e₂ γ = {!!}
-}
{-
  equation at type : ⟦ T′ ⟧T η
  LHS = ⟦ e₁ ⟧E (⟦ e₂ ⟧E γ ∷⟦ T ⟧ γ)
  RHS = ⟦
(StratF.ExpSubstitution.-invert758 e₁ (Eextₛ Eidₛ e₂)
 (Esub* Tidₛ (EΓsub* (Eextₛ Eidₛ e₂) Tidₛ) e₁)
 | ΓSub Tidₛ Γ | ⟦ Γ ⟧Γidₛ≡Γ)
⟧E
γ


  where
  ⟦γ⟧idₛ : VEnv (⟦ Γ ⟧EEₛ Tidₛ) η
  ⟦γ⟧idₛ rewrite ⟦ Γ ⟧Γidₛ≡Γ = γ
  eq = lemmaE Tidₛ {η₂ = η} {γ₂ = ⟦γ⟧idₛ} (e₂ ∷Eₛ Eidₛ) e₁
  ⟦T⟧ : Set l
  ⟦T⟧ = ⟦ T ⟧T η
  ⟦T′⟧ : Set l′
  ⟦T′⟧ = ⟦ T′ ⟧T η
  ⟦e₂⟧ : ⟦T⟧
  ⟦e₂⟧ = ⟦ e₂ ⟧E γ


  ⟦ (‵ƛ e₁) ⟧E γ : ⟦T⟧ → ⟦T′⟧
  ⟦ (‵ƛ e₁) ⟧E γ = λ v → ⟦ e₁ ⟧E (v ∷⟦ ⟦T⟧ ⟧ γ)
-}


--! ETsingleSubstPreserves
{-
lemmaΛV : (σ* : TSub Δ₁ Δ₂) (v : Val {Δ₁} Γ {l} T) (η : ⟦ Δ₂ ⟧TE) →
          (γ : VEnv {Δ₂} (⟦ Γ ⟧EEₛ σ*) η) →
          ⟦ v ⟧V (reindexₛ σ* γ) ≡ subst id (subst-preserves σ* T) (⟦ ⟦ v ⟧VTₛ σ* ⟧V γ)
lemmaΛE : (σ* : TSub Δ₁ Δ₂) (e : Exp {Δ₁} Γ {l} T) (η : ⟦ Δ₂ ⟧TE) →
          (γ : VEnv {Δ₂} (⟦ Γ ⟧EEₛ σ*) η) →
          ⟦ e ⟧E (reindexₛ σ* γ) ≡ subst id (subst-preserves σ* T) (⟦ ⟦ e ⟧ETₛ σ* ⟧E γ)
lemmaΛV {Γ = Γ} {l = l} {T = T} σ* (‵ here) η γ rewrite subst-preserves {η = η} σ* T = refl
lemmaΛV {Γ = Γ} {l = l} {T = T} σ* (‵ there x) η γ = {!!}
lemmaΛV {Γ = Γ} {l = l} {T = T} σ* (# n) η γ = refl
lemmaΛV {Γ = Γ} {l = l} {T = T₁ ‵⇒ T₂} σ* (ƛ e) η γ = {!!}
lemmaΛV {Γ = Γ} {l = l} {T = ‵∀[ T ]} σ* (Λ l₁ ⇒ e) η γ = {!!}

lemmaΛE {Γ = Γ} {l = l} {T = T} σ* (‵val v) η γ = lemmaΛV {Γ = Γ} {l = l} {T = T} σ* v η γ
lemmaΛE {Γ = Γ} {l = l} {T = ‵ℕ} σ* (‵suc e) η γ = cong ℕ.suc (lemmaΛE σ* e η γ)
lemmaΛE {Γ = Γ} {l = l} {T = T₂} σ* (f · e) η γ = {!!}
lemmaΛE {Γ = Γ} {l = l} σ* (e ∙ T′) η γ = {!!}
{-
lhs : ⟦ T ⟧T (⟦ η ⟧TETₛ σ*)
rhs : ⟦ ⟦ T ⟧Tₛ σ* ⟧T η -- ⟦ ⟦ e ⟧ETₛ σ* ⟧E γ
-}
-}

-- MW: here the scourge also bites! this is exactly where we need to prove, that in general:
postulate 
  ⟦⟧E-pres-Tsub : ∀ {η₂ : ⟦ Δ₂ ⟧TE}  {T : Type Δ₁ l} 
    (e : Exp {Δ₁} Γ₁ T) (σ : TSub Δ₁ Δ₂) → 
    (γ₂ : VEnv (ΓSub σ Γ₁) η₂) →
    let subst = subst id (sym (subst-preserves σ T)) in
    (⟦_⟧E (⟦ e ⟧ETₛ σ) {η = η₂} γ₂) ≡ subst (⟦_⟧E e {η = ⟦ η₂ ⟧TETₛ σ} (reindexₛ σ γ₂)) 
-- maybe there is a smarter way for this! (thinking about arrows)
-- the hole below follows from a specialisation of this lemma.

⟦_βΛ_⟧E_ : -- equation holds at ⟦ T′ [ T ]Tₛ ⟧T η
           ∀ {T : Type (l ∷ Δ) l′} (e : Exp ([ l ]∷ Γ) T) (T′ : Type Δ l) →
           (γ : VEnv {Δ} Γ η) → ⟦_⟧E ((‵Λ l ⇒ e) ∙ T′) γ ≡ ⟦ e [ T′ ]ETₛ ⟧E γ

⟦_βΛ_⟧E_ {l = l} {Δ = Δ} {l′ = l′} {Γ = Γ} {η = η} {T = T} e T′ γ
  with eqη ← ⟦ T [ T′ ]Tₛ⟧T η
  with lhs ← ⟦ e ⟧E ((⟦ T′ ⟧T η) ∷[ l ] γ)
  with rhs ← ⟦ e [ T′ ]ETₛ ⟧E γ
  rewrite lemmaΓ T′ Γ
  rewrite eqη
  = {!  !} {- lhs ≡ rhs -}
{-
  lhs = ⟦ e ⟧E ((⟦ T′ ⟧T η) ∷[ l ] γ)
  rhs = ⟦ e [ T′ ]ETₛ ⟧E γ

-- so the equation is a commutation between:
-- * semantic substitution at a type on the LHS
-- * syntactic substitution at the corresponding type on the RHS
-}
