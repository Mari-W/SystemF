module StratF.Expressions where

open import Level using (Level; _⊔_)
open import Data.List.Base using (_∷_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_,_)

open import StratF.ExpEnvironments
open import StratF.TypeSubstPropertiesSem
open import StratF.TypeSubstProperties
open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.TypeEnvironments

-- MW: we use mutual recursive definition of expressions and values 
-- instead of Val as a predicate on expressions

-- intrinsically typed stratified System F
-- separated out into values and expressions
-- anticipating the operational/denotational semantics etc.

data Val {Δ} (Γ : Env Δ) : Type Δ l → Set

data Exp {Δ} (Γ : Env Δ) : Type Δ l → Set

data Val {Δ} Γ where
  ‵_    : T ∈ Γ → Val Γ T
  #_    : (n : ℕ) → Val Γ ‵ℕ
  ƛ_    : Exp (T ∷ Γ) T′ → Val Γ (T ‵⇒ T′)
  Λ_⇒_  : ∀ l {T : Type (l ∷ Δ) l′} → Exp ([ l ]∷ Γ) T → Val Γ ‵∀[ T ]

pattern ƛ[_]_ T e      = ƛ_ {T = T} e
pattern Λ[_∈_]⇒_ T l e = Λ_⇒_ l {T = T} e

data Exp {Δ} Γ where
  ‵val : (v : Val Γ T) → Exp Γ T
  ‵suc : Exp Γ ‵ℕ → Exp Γ ‵ℕ
  _·_  : (f : Exp Γ (T ‵⇒ T′)) → (e : Exp Γ T) → Exp Γ T′
  _∙_  : Exp Γ ‵∀[ T ] → (T′ : Type Δ l) → Exp Γ (T [ T′ ]Tₛ)

pattern ‵var x  = ‵val (‵ x)
pattern ‵# n = ‵val (# n)
pattern ‵ƛ e = ‵val (ƛ e)
pattern ‵Λ_⇒_ l e = ‵val (Λ l ⇒ e)
pattern _∙[_]_ e T T′  = _∙_ {T = T} e T′

variable v v′ w w′ v₁ v₂ v₃ : Val {Δ} Γ {l} T
variable e e′ f f′ e₁ e₂ e₃ : Exp {Δ} Γ {l} T
variable n : ℕ

-- (semantic) level of an expression/value

V-level : Val {Δ} Γ T → Level
V-level {Δ = Δ} {Γ = Γ} {T = T} v = T-level T ⊔ Γ-level Γ ⊔ Δ-level Δ

E-level : Exp {Δ} Γ T → Level
E-level {Δ = Δ} {Γ = Γ} {T = T} e = T-level T ⊔ Γ-level Γ ⊔ Δ-level Δ

-- closure under type renaming


⟦‵_⟧VTᵣ_ : {Γ : Env Δ₁} (x : T ∈ Γ) (ρ : TRen Δ₁ Δ₂) → (⟦ T ⟧Tᵣ ρ) ∈ (⟦ Γ ⟧EEᵣ ρ)
⟦‵ here    ⟧VTᵣ ρ = here
⟦‵ there x ⟧VTᵣ ρ = there (⟦‵ x ⟧VTᵣ ρ)
-- MW: applying a type renaming/ type substitution changes the  
-- type index and now also all elements in Γ.
⟦_⟧VTᵣ_ : (v : Val {Δ₁} Γ T) (ρ : TRen Δ₁ Δ₂) → Val {Δ₂} (⟦ Γ ⟧EEᵣ ρ) (⟦ T ⟧Tᵣ ρ)
⟦_⟧ETᵣ_ : (e : Exp {Δ₁} Γ T) (ρ : TRen Δ₁ Δ₂) → Exp {Δ₂} (⟦ Γ ⟧EEᵣ ρ) (⟦ T ⟧Tᵣ ρ)

⟦ # n     ⟧VTᵣ ρ = # n
⟦ ‵ x     ⟧VTᵣ ρ = ‵ (⟦‵ x ⟧VTᵣ ρ)
⟦ ƛ e     ⟧VTᵣ ρ = ƛ ⟦ e ⟧ETᵣ ρ
⟦_⟧VTᵣ_ {Γ = Γ} (Λ l ⇒ e) ρ
  with e′ ← ⟦ e ⟧ETᵣ Tliftᵣ ρ
  rewrite Γliftᵣ ρ l Γ
  = Λ l ⇒ e′

⟦ ‵val v  ⟧ETᵣ ρ = ‵val (⟦ v ⟧VTᵣ ρ)
⟦ ‵suc e  ⟧ETᵣ ρ = ‵suc (⟦ e ⟧ETᵣ ρ)
⟦ f · e   ⟧ETᵣ ρ = (⟦ f ⟧ETᵣ ρ) · (⟦ e ⟧ETᵣ ρ)
⟦ e ∙[ T ] T′  ⟧ETᵣ ρ
  with e′ ← ⟦ e ⟧ETᵣ ρ
  rewrite swap-Tren-[] ρ T T′
  = e′ ∙[ ⟦ T ⟧Tᵣ Tliftᵣ ρ ] (⟦ T′ ⟧Tᵣ ρ)

-- closure under type substitution

⟦‵_⟧VTₛ_ : {Γ : Env Δ₁} (x : T ∈ Γ) (σ : TSub Δ₁ Δ₂) → (⟦ T ⟧Tₛ σ) ∈ (⟦ Γ ⟧EEₛ σ)
⟦‵ here    ⟧VTₛ σ = here
⟦‵ there x ⟧VTₛ σ = there (⟦‵ x ⟧VTₛ σ)

⟦_⟧VTₛ_ : (e : Val {Δ₁} Γ T) (σ : TSub Δ₁ Δ₂) → Val {Δ₂} (⟦ Γ ⟧EEₛ σ) (⟦ T ⟧Tₛ σ)
⟦_⟧ETₛ_ : (e : Exp {Δ₁} Γ T) (σ : TSub Δ₁ Δ₂) → Exp {Δ₂} (⟦ Γ ⟧EEₛ σ) (⟦ T ⟧Tₛ σ)

⟦ # n    ⟧VTₛ σ = # n
⟦ ‵ x    ⟧VTₛ σ = ‵ (⟦‵ x ⟧VTₛ σ)
⟦ ƛ e    ⟧VTₛ σ = ƛ ⟦ e ⟧ETₛ σ
⟦_⟧VTₛ_ {Γ = Γ} (Λ l ⇒ e) σ
  with e′ ← ⟦ e ⟧ETₛ Tliftₛ σ
  rewrite Γliftₛ σ l Γ
  = Λ l ⇒ e′

⟦ ‵val v ⟧ETₛ σ = ‵val (⟦ v ⟧VTₛ σ)
⟦ ‵suc e ⟧ETₛ σ = ‵suc (⟦ e ⟧ETₛ σ)
⟦ f · e  ⟧ETₛ σ = (⟦ f ⟧ETₛ σ) · (⟦ e ⟧ETₛ σ)
⟦ e ∙[ T ] T′ ⟧ETₛ σ
  with e′ ← ⟦ e ⟧ETₛ σ
  rewrite swap-Tsub-[] σ T T′
  = e′ ∙[ ⟦ T ⟧Tₛ Tliftₛ σ ] (⟦ T′ ⟧Tₛ σ)

_[_]ETₛ : Exp {l ∷ Δ} ([ l ]∷ Γ) T → (T′ : Type Δ l) → Exp Γ (T [ T′ ]Tₛ)
_[_]ETₛ {l = l} {Γ = Γ} e T′
  with e′ ← ⟦ e ⟧ETₛ [ T′ ]T rewrite lemmaΓ T′ Γ = e′

-- semantics, again at a *bounded* level

infix 10 ⟦_⊢_⟧

-- MW: the type of our denotational semantics function given some type T.
-- this now does not need to live in Setω! 
⟦_⊢_⟧ : ∀ {Δ l} (Γ : Env Δ) (T : Type Δ l) → Set (T-level T ⊔ Γ-level Γ ⊔ Δ-level Δ)
⟦_⊢_⟧ {Δ = Δ} Γ T = {η : ⟦ Δ ⟧TE} → ⟦ Γ ⟧EE η → ⟦ T ⟧T η


-- semantics of variables in an environment

⟦‵_⟧V_ : {T : Type Δ l} {Γ : Env Δ} → T ∈ Γ → ⟦ Γ ⊢ T ⟧
⟦‵ here    ⟧V (v , _) = v
⟦‵ there x ⟧V (_ , γ) = ⟦‵ x ⟧V γ

-- value and expression semantics

⟦_⟧V : Val {Δ} Γ T → ⟦ Γ ⊢ T ⟧
⟦_⟧E : Exp {Δ} Γ T → ⟦ Γ ⊢ T ⟧

⟦ # n         ⟧V γ = n
⟦ ‵ x         ⟧V γ = ⟦‵ x ⟧V γ
⟦ ƛ[ T ] e    ⟧V γ = λ v → ⟦ e ⟧E (v ∷⟦ T ⟧ γ)
⟦ Λ l ⇒ e     ⟧V γ = λ ⟦α⟧ → ⟦ e ⟧E (⟦α⟧ ∷[ l ] γ)

⟦ ‵val e      ⟧E γ = ⟦ e ⟧V γ
⟦ ‵suc e      ⟧E γ = suc (⟦ e ⟧E γ)
⟦ f · e       ⟧E γ = ⟦ f ⟧E γ (⟦ e ⟧E γ)
⟦ e ∙[ T ] T′ ⟧E {η = η} γ
  rewrite ⟦ T [ T′ ]Tₛ⟧T η = ⟦ e ⟧E γ (⟦ T′ ⟧T η)
-- MW: this (as expected) still uses rewrite at the same position as our definition
