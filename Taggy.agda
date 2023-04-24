{-# OPTIONS --rewriting #-}

module Taggy where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Level
open import Data.Fin
open import Data.Nat
open import Data.String
open import Data.List
open import Data.Vec

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

-- syntax

Ident = String

variable n : ℕ
variable l : Level

lof : ℕ → Level
lof ℕ.zero = Level.zero
lof (ℕ.suc n) = Level.suc (lof n)

open import Data.Unit

-- level environments
LEnv = List Level
variable Δ Δ₁ Δ₂ : LEnv

data _∈_ : Level → LEnv → Set where
  here  : ∀ {l ls} → l ∈ (l ∷ ls)
  there : ∀ {l l′ ls} → l ∈ ls → l ∈ (l′ ∷ ls)

data Type (Δ : LEnv) : Set where
  `_ : ∀ {l} → l ∈ Δ → Type Δ
  _⇒_ : Type Δ → Type Δ → Type Δ
  `∀α_,_ : (lev : Level) → Type (lev ∷ Δ) → Type Δ
  𝟙 : Type Δ

-- level of type according to Leivant'91
level : Type Δ → Level
level (`_ {lev} x) = lev
level (T₁ ⇒ T₂) = level T₁ Level.⊔ level T₂
level (`∀α q , T) = Level.suc q Level.⊔ level T
level 𝟙 = Level.zero

Env* : LEnv → Setω
Env* Δ = ∀ {l} → l ∈ Δ → Set l

-- extend must be a named function so that the definition of evaluation goes through
extend-η : ∀ {l} {Δ : LEnv} → Set l → Env* Δ → Env* (l ∷ Δ)
extend-η α η here = α
extend-η α η (there x) = η x

-- the meaning of a stratified type in terms of Agda universes
⟦_⟧ : (T : Type Δ) → Env* Δ → Set (level T)
⟦ ` x ⟧ η = η x
⟦ T₁ ⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
⟦ `∀α lev , T ⟧ η = (α : Set lev) → ⟦ T ⟧ (extend-η α η)
⟦ 𝟙 ⟧ η = ⊤

-- renaming on types
Ren : LEnv → LEnv → Set
Ren Δ₁ Δ₂ = ∀ n → n ∈ Δ₁ → n ∈ Δ₂

wkᵣ : Ren Δ (l ∷ Δ)
wkᵣ _ = there

extᵣ : Ren Δ₁ Δ₂ → ∀ l → Ren (l ∷ Δ₁) (l ∷ Δ₂)
extᵣ ρ _ _ here = here
extᵣ ρ _ _ (there x) = there (ρ _ x)

renT : Ren Δ₁ Δ₂ → (Type Δ₁ → Type Δ₂)
renT ρ (`_ {n} x) = ` ρ n x
renT ρ (T₁ ⇒ T₂) = renT ρ T₁ ⇒ renT ρ T₂
renT ρ (`∀α lev , T) = `∀α lev , renT (extᵣ ρ lev) T
renT ρ 𝟙 = 𝟙 

wkT : Type Δ → Type (l ∷ Δ)
wkT = renT wkᵣ 

level-ren : (ρ : Ren Δ₁ Δ₂) → (T : Type Δ₁) → level T ≡ level (renT ρ T)
level-ren ρ (` x) = refl
level-ren ρ (T₁ ⇒ T₂) = cong₂ Level._⊔_ (level-ren ρ T₁) (level-ren ρ T₂)
level-ren ρ (`∀α lev , T) = cong (Level.suc lev Level.⊔_) (level-ren (extᵣ ρ lev) T)
level-ren ρ 𝟙 = refl

-- substitution on types
Sub : LEnv → LEnv → Set
Sub Δ₁ Δ₂ = ∀ n → n ∈ Δ₁ → Type Δ₂

idₛ : Sub Δ Δ
idₛ _ = `_

wkₛ : Ren Δ (l ∷ Δ)
wkₛ _ = there

extₛ : Sub Δ₁ Δ₂ → ∀ l → Sub (l ∷ Δ₁) (l ∷ Δ₂)
extₛ σ _ _ here = ` here
extₛ σ _ _ (there x) = wkT (σ _ x)

subT : Sub Δ₁ Δ₂ → (Type Δ₁ → Type Δ₂)
subT σ (`_ {n} x) = σ n x
subT σ (T₁ ⇒ T₂) = subT σ T₁ ⇒ subT σ T₂
subT σ (`∀α lev , T) = `∀α lev , subT (extₛ σ lev) T
subT σ 𝟙 = 𝟙 

singleₛ : Sub Δ₁ Δ₂ → Type Δ₂ → ∀ l → Sub (l ∷ Δ₁) Δ₂
singleₛ σ T' _ _ here = T'
singleₛ σ T' _ _ (there x) = σ _ x

_[_]T : Type (l ∷ Δ) → Type Δ → Type Δ
_[_]T {n} T T' = subT (singleₛ idₛ T' n) T

-- type environments
data TEnv : LEnv → Set where
  ∅    : TEnv []
  _◁_  : Type Δ → TEnv Δ → TEnv Δ
  _◁*_ : (l : Level) → TEnv Δ → TEnv (l ∷ Δ)

data inn : ∀ {Δ} → Type Δ → TEnv Δ → Set where
  here  : ∀ {T Γ} → inn {Δ} T (T ◁ Γ)
  there : ∀ {T T′ Γ} → inn {Δ} T Γ → inn {Δ} T (T′ ◁ Γ)
  tskip : ∀ {T l Γ} → inn {Δ} T Γ → inn (wkT T) (l ◁* Γ)

data Expr : (Δ : LEnv) → TEnv Δ → Type Δ → Set where
  `_   : ∀ {T : Type Δ}{Γ : TEnv Δ} → inn T Γ → Expr Δ Γ T
  ƛ_   : ∀ {T T′ : Type Δ}{Γ : TEnv Δ} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
  _·_  : ∀ {T T′ : Type Δ}{Γ : TEnv Δ} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
  Λα_⇒_ : ∀ {Γ : TEnv Δ} → (l : Level) → {T : Type (l ∷ Δ)} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
  _∙_  : ∀ {l}{T : Type (l ∷ Δ)}{Γ : TEnv Δ} → Expr Δ Γ (`∀α l , T) → (T′ : Type Δ) → level T′ ≡ l → Expr Δ Γ (T [ T′ ]T)

Env : (Δ : LEnv) → TEnv Δ → Env* Δ → Setω
Env Δ Γ η = ∀ {T : Type Δ} → (x : inn T Γ) → ⟦ T ⟧ η

extend : ∀ {T : Type Δ}{Γ : TEnv Δ}{η : Env* Δ} → Env Δ Γ η → ⟦ T ⟧ η → Env Δ (T ◁ Γ) η
extend γ v here = v
extend γ v (there x) = γ x

level-weak : ∀ {T : Type Δ} → level T ≡ level (wkT{l = l} T)
level-weak {l = l} {T = T} = level-ren (wkᵣ{l = l}) T

-- not accepted: {-# REWRITE level-weak #-}
-- because level-weak  is not a legal rewrite rule, since the following variables are not bound by the left hand side:  l

weak-extend-η-sig : Setω
weak-extend-η-sig = ∀ {Δ}{l} (T : Type Δ) (⟦α⟧ : Set l) (η : Env* Δ)
  → ⟦ wkT T ⟧ (extend-η ⟦α⟧ η) ≡ {!⟦ T ⟧ η!}

weak-extend-η : ∀ (T : Type Δ) (⟦α⟧ : Set l) (η : Env* Δ)
  → ⟦ wkT T ⟧ (extend-η ⟦α⟧ η) ≡ {!⟦ T ⟧ η!}
weak-extend-η T ⟦α⟧ η = {!!}

extend-tskip : ∀ {Δ : LEnv}{Γ : TEnv Δ}{η : Env* Δ}{⟦α⟧ : Set l}
  → Env Δ Γ η → Env (l ∷ Δ) (l ◁* Γ) (extend-η ⟦α⟧ η)
extend-tskip γ (tskip{T = T} x) = {!!}

E⟦_⟧ : ∀ {T : Type Δ}{Γ : TEnv Δ} → Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → ⟦ T ⟧ η
E⟦ ` x ⟧ η γ = γ x
E⟦ ƛ_ e ⟧ η γ = λ v → E⟦ e ⟧ η (extend γ v)
E⟦ e₁ · e₂ ⟧ η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
E⟦_⟧ {Δ}{`∀α l , T} (Λα l ⇒ e) η γ = λ ⟦α⟧ → E⟦ e ⟧ (extend-η ⟦α⟧ η) (extend-tskip γ)
E⟦ (e ∙ T′) lev-eq ⟧ η γ with ⟦ T′ ⟧ η
... | S rewrite lev-eq with E⟦ e ⟧ η γ S
... | v = {! !}
