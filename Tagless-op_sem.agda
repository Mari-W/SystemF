module Tagless-op_sem where

open import Level
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

variable l l′ l₁ l₂ : Level

----------------------------------------------------------------------

postulate
  dependent-extensionality :
    ∀ {a b}{A : Set a}{F G : (α : A) → Set b}
    → (∀ (α : A) → F α ≡ G α)
    → ((α : A) → F α) ≡ ((α : A) → G α)

-- equality for Setω

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  refl : x ≡ω x

congωl : ∀ {b} {A : Setω} {B : Set b} (f : A → B) {x y : A} → x ≡ω y → f x ≡ f y
congωl f refl = refl

conglω : ∀ {a} {A : Set a} {B : Setω} (f : A → B) {x y : A} → x ≡ y → f x ≡ω f y
conglω f refl = refl

congωω : ∀ {A : Setω} {B : Setω} (f : A → B) {x y : A} → x ≡ω y → f x ≡ω f y
congωω f refl = refl

transω : ∀ {A : Setω} {x y z : A} → x ≡ω y → y ≡ω z → x ≡ω z
transω refl refl = refl

----------------------------------------------------------------------

-- level environments

LEnv = List Level
variable Δ Δ₁ Δ₂ : LEnv

-- type variables

data _∈_ : Level → LEnv → Set where
  here  : l ∈ (l ∷ Δ)
  there : l ∈ Δ → l ∈ (l′ ∷ Δ)

-- types

data Type Δ : Level → Set where
  `_     : l ∈ Δ → Type Δ l
  _⇒_    : Type Δ l → Type Δ l′ → Type Δ (l ⊔ l′)
  `∀α_,_ : ∀ l → Type (l ∷ Δ) l′ → Type Δ (suc l ⊔ l′)
  𝟙      : Type Δ zero

variable T T₁ T₂ : Type Δ l


-- level of type according to Leivant'91
level : Type Δ l → Level
level {l = l} T = l

-- semantic environments (mapping level l to an element of Set l)

data Env* : LEnv → Setω where
  []  : Env* []
  _∷_ : Set l → Env* Δ → Env* (l ∷ Δ)

apply-env : Env* Δ → l ∈ Δ → Set l
apply-env [] ()
apply-env (x ∷ _) here = x
apply-env (_ ∷ η) (there x) = apply-env η x

-- the meaning of a stratified type in terms of Agda universes

⟦_⟧ : (T : Type Δ l) → Env* Δ → Set l
⟦ ` x ⟧ η = apply-env η x
⟦ T₁ ⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
⟦ `∀α l , T ⟧ η = (α : Set l) → ⟦ T ⟧ (α ∷ η)
⟦ 𝟙 ⟧ η = ⊤

-- renaming on types

Ren : LEnv → LEnv → Set
Ren Δ₁ Δ₂ = ∀ {l} → l ∈ Δ₁ → l ∈ Δ₂

wkᵣ : Ren Δ (l ∷ Δ)
wkᵣ = there

extᵣ : Ren Δ₁ Δ₂ → Ren (l ∷ Δ₁) (l ∷ Δ₂)
extᵣ ρ here = here
extᵣ ρ (there x) = there (ρ x)

renT : Ren Δ₁ Δ₂ → (Type Δ₁ l → Type Δ₂ l)
renT ρ (` x) = ` ρ x
renT ρ (T₁ ⇒ T₂) = renT ρ T₁ ⇒ renT ρ T₂
renT ρ (`∀α lev , T) = `∀α lev , renT (extᵣ ρ) T
renT ρ 𝟙 = 𝟙 

wkT : Type Δ l′ → Type (l ∷ Δ) l′
wkT = renT wkᵣ

-- the action of renaming on semantic environments

Ren* : (ρ : Ren Δ₁ Δ₂) → (η₁ : Env* Δ₁) → (η₂ : Env* Δ₂) → Setω
Ren* {Δ₁} ρ η₁ η₂ = ∀ {l : Level} → (x : l ∈ Δ₁) → apply-env η₂ (ρ x) ≡ apply-env η₁ x

wkᵣ∈Ren* : ∀ (η : Env* Δ) (⟦α⟧ : Set l) → Ren* (wkᵣ{Δ}{l}) η (⟦α⟧ ∷ η)
wkᵣ∈Ren* η ⟦α⟧ x = refl

ren*-id : (η : Env* Δ) → Ren* (λ x → x) η η
ren*-id η x = refl

ren*-pop : (ρ : Ren (l ∷ Δ₁) Δ₂) (α : Set l) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → Ren* ρ (α ∷ η₁) η₂ → Ren* (ρ ∘ there) η₁ η₂
ren*-pop ρ α η₁ η₂ ren* x = ren* (there x)

ren*-ext : ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂} (α : Set l)
  → Ren* ρ η₁ η₂ → Ren* (extᵣ ρ) (α ∷ η₁) (α ∷ η₂)
ren*-ext α ren* here = refl
ren*-ext α ren* (there x) = ren* x

ren*-preserves-semantics : ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂}
  → (ren* : Ren* ρ η₁ η₂) → (T : Type Δ₁ l) →  ⟦ renT ρ T ⟧ η₂ ≡ ⟦ T ⟧ η₁
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (` x) = ren* x
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (T₁ ⇒ T₂)
  rewrite ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₁
  | ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₂
  = refl
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (`∀α l , T) =
  dependent-extensionality (λ α →
    ren*-preserves-semantics{ρ = extᵣ ρ}{α ∷ η₁}{α ∷ η₂} (ren*-ext{ρ = ρ} α ren*) T)
ren*-preserves-semantics ren* 𝟙 = refl

-- substitution on types

data Sub : LEnv → LEnv → Set where
  []  : Sub [] Δ₂
  _∷_ : Type Δ₂ l → Sub Δ₁ Δ₂ → Sub (l ∷ Δ₁) Δ₂

apply-sub : l ∈ Δ₁ → Sub Δ₁ Δ₂ → Type Δ₂ l
apply-sub here (T ∷ _) = T
apply-sub (there x) (_ ∷ σ) = apply-sub x σ

build-id : (Δ₁ : LEnv) → Ren Δ₁ Δ → Sub Δ₁ Δ
build-id [] ρ = []
build-id (l ∷ Δ₁) ρ = (` ρ here) ∷ build-id Δ₁ (ρ ∘ there)

idₛ : Sub Δ Δ
idₛ {Δ} = build-id Δ (λ x → x)

wkₛ : Sub Δ₁ Δ₂ → Sub Δ₁ (l ∷ Δ₂)
wkₛ [] = []
wkₛ (T ∷ σ) = wkT T ∷ wkₛ σ

extₛ : Sub Δ₁ Δ₂ → ∀ {l} → Sub (l ∷ Δ₁) (l ∷ Δ₂)
extₛ σ = ` here ∷ wkₛ σ

subT : Sub Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
subT σ (` x) = apply-sub x σ
subT σ (T₁ ⇒ T₂) = subT σ T₁ ⇒ subT σ T₂
subT σ (`∀α l , T) = `∀α l , subT (extₛ σ) T
subT σ 𝟙 = 𝟙

singleₛ : Sub Δ₁ Δ₂ → ∀ {l} → Type Δ₂ l → Sub (l ∷ Δ₁) Δ₂
singleₛ σ T' = T' ∷ σ

_[_]T : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
_[_]T T T' = subT (singleₛ idₛ T') T

-- type environments

data TEnv : LEnv → Set where
  ∅    : TEnv []
  _◁_  : Type Δ l → TEnv Δ → TEnv Δ
  _◁*_ : (l : Level) → TEnv Δ → TEnv (l ∷ Δ)

variable Γ Γ₁ Γ₂ : TEnv Δ

data inn : Type Δ l → TEnv Δ → Set where
  here  : ∀ {T Γ} → inn {Δ}{l} T (T ◁ Γ)
  there : ∀ {T : Type Δ l}{T′ : Type Δ l′}{Γ} → inn {Δ}{l} T Γ → inn {Δ} T (T′ ◁ Γ)
  tskip : ∀ {T l Γ} → inn {Δ}{l′} T Γ → inn (wkT T) (l ◁* Γ)

data Expr (Δ : LEnv) (Γ : TEnv Δ) : Type Δ l → Set where
  `_   : ∀ {T : Type Δ l} → inn T Γ → Expr Δ Γ T
  ƛ_   : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
  _·_  : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
  Λ_⇒_ : ∀ (l : Level) → {T : Type (l ∷ Δ) l′} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
  _∙_  : ∀ {T : Type (l ∷ Δ) l′} → Expr Δ Γ (`∀α l , T) → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)

variable e e₁ e₂ : Expr Δ Γ T

-- value environments

Env : (Δ : LEnv) → TEnv Δ → Env* Δ → Setω
Env Δ Γ η = ∀ {l}{T : Type Δ l} → (x : inn T Γ) → ⟦ T ⟧ η

extend : ∀ {T : Type Δ l}{Γ : TEnv Δ}{η : Env* Δ}
  → Env Δ Γ η → ⟦ T ⟧ η → Env Δ (T ◁ Γ) η
extend γ v here = v
extend γ v (there x) = γ x

extend-tskip : ∀ {Δ : LEnv}{Γ : TEnv Δ}{η : Env* Δ}{⟦α⟧ : Set l}
  → Env Δ Γ η → Env (l ∷ Δ) (l ◁* Γ) (⟦α⟧ ∷ η)
extend-tskip {η = η} {⟦α⟧ = ⟦α⟧} γ (tskip{T = T} x)
  rewrite ren*-preserves-semantics {ρ = wkᵣ}{η}{⟦α⟧ ∷ η} (wkᵣ∈Ren* η ⟦α⟧) T
  = γ x

subst-to-env* : (σ : Sub Δ₁ Δ₂) → (η₂ : Env* Δ₂) → Env* Δ₁
subst-to-env* [] η₂ = []
subst-to-env* (T ∷ σ) η₂ = ⟦ T ⟧ η₂ ∷ subst-to-env* σ η₂

subst-var-preserves : (x  : l ∈ Δ₁) (σ  : Sub Δ₁ Δ₂) (η₂ : Env* Δ₂) → ⟦ apply-sub x σ ⟧ η₂ ≡ apply-env (subst-to-env* σ η₂) x
subst-var-preserves here (T ∷ σ) η₂ = refl
subst-var-preserves (there x) (_ ∷ σ) η₂ = subst-var-preserves x σ η₂

subst-to-env*-wk : (σ  : Sub Δ₁ Δ₂) → (α  : Set l) → (η₂ : Env* Δ₂) → subst-to-env* (wkₛ σ) (α ∷ η₂) ≡ω subst-to-env* σ η₂
subst-to-env*-wk [] α η₂ = refl
subst-to-env*-wk (T ∷ σ) α η₂
  rewrite ren*-preserves-semantics {ρ = wkᵣ}{η₂}{α ∷ η₂} (wkᵣ∈Ren* η₂ α) T
  = congωω (⟦ T ⟧ η₂ ∷_) (subst-to-env*-wk σ α η₂)

subst-to-env*-build : ∀ (ρ : Ren Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → Ren* ρ η₁ η₂
  → subst-to-env* (build-id Δ₁ ρ) η₂ ≡ω η₁
subst-to-env*-build ρ [] η₂ ren* = refl
subst-to-env*-build {Δ₁ = _ ∷ Δ₁} ρ (α ∷ η₁) η₂ ren* = 
  transω (congωω (λ H → apply-env η₂ (ρ here) ∷ H) (subst-to-env*-build (ρ ∘ there) η₁ η₂ (ren*-pop ρ α η₁ η₂ ren*)))
         (conglω (_∷ η₁) (ren* here))

subst-to-env*-id : (η : Env* Δ) → subst-to-env* idₛ η ≡ω η
subst-to-env*-id {Δ} η = subst-to-env*-build {Δ₁ = Δ} (λ x → x) η η (ren*-id η)

subst-preserves-type : Setω
subst-preserves-type =
  ∀ {Δ₁ Δ₂}{l}{η₂ : Env* Δ₂}
  → (σ : Sub Δ₁ Δ₂) (T : Type Δ₁ l)
  → ⟦ subT σ T ⟧ η₂ ≡ ⟦ T ⟧ (subst-to-env* σ η₂)

subst-preserves : subst-preserves-type
subst-preserves {η₂ = η₂} σ (` x) = subst-var-preserves x σ η₂
subst-preserves{η₂ = η₂} σ (T₁ ⇒ T₂)
  rewrite subst-preserves{η₂ = η₂} σ T₁
  |  subst-preserves{η₂ = η₂} σ T₂ = refl
subst-preserves {η₂ = η₂} σ (`∀α l , T) =
  dependent-extensionality (λ α →
    trans (subst-preserves {η₂ = α ∷ η₂} (extₛ σ) T)
          (congωl (λ H → ⟦ T ⟧ (α ∷ H)) (subst-to-env*-wk σ α η₂)))
subst-preserves σ 𝟙 = refl

single-subst-preserves : ∀ (η : Env* Δ) (T′ : Type Δ l) (T : Type (l ∷ Δ) l′) → ⟦ T [ T′ ]T ⟧ η ≡ ⟦ T ⟧ (⟦ T′ ⟧ η ∷ η)
single-subst-preserves {Δ = Δ} {l = l}{l′ = l′} η T′ T =
  trans (subst-preserves (singleₛ idₛ T′) T)
        (congωl (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η))

E⟦_⟧ : ∀ {T : Type Δ l}{Γ : TEnv Δ} → Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → ⟦ T ⟧ η
E⟦ ` x ⟧ η γ = γ x
E⟦ ƛ_ e ⟧ η γ = λ v → E⟦ e ⟧ η (extend γ v)
E⟦ e₁ · e₂ ⟧ η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
E⟦ Λ l ⇒ e ⟧ η γ = λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η) (extend-tskip γ)
E⟦ _∙_ {T = T} e T′ ⟧ η γ
  with E⟦ e ⟧ η γ (⟦ T′ ⟧ η)
... | v rewrite single-subst-preserves η T′ T = v 

-- expr in expr substitution

RenE : TEnv Δ → TEnv Δ → Set
RenE {Δ} Γ₁ Γ₂ = ∀ {l} {T : Type Δ l} → inn T Γ₁ → inn T Γ₂

wkᵣE : ∀ {l Δ} {Γ : TEnv Δ} {T : Type Δ l} → RenE Γ (T ◁ Γ)
wkᵣE = there

extᵣE : RenE Γ₁ Γ₂ → RenE (T ◁ Γ₁) (T ◁ Γ₂)
extᵣE ρ here = here
extᵣE ρ (there x) = there (ρ x)

extᵣEl : RenE Γ₁ Γ₂ → RenE (l ◁* Γ₁) (l ◁* Γ₂)
extᵣEl ρ (tskip x) = tskip (ρ x) 

renE : RenE Γ₁ Γ₂ → (Expr Δ Γ₁ T → Expr Δ Γ₂ T)
renE ρ (` x) = ` ρ x
renE ρ (ƛ e) = ƛ renE (extᵣE ρ) e
renE ρ (e₁ · e₂) = renE ρ e₁ · renE ρ e₂
renE ρ (Λ l ⇒ e) = Λ l ⇒ renE (extᵣEl ρ) e
renE ρ (e ∙ T′) = renE ρ e ∙ T′

wkE : Expr Δ Γ T → Expr Δ (T₁ ◁ Γ) T 
wkE = renE wkᵣE

extEl : Expr Δ Γ T → Expr (l ∷ Δ) (l ◁* Γ) (wkT T)  
extEl = {!  !}

SubE : TEnv Δ → TEnv Δ → Set
SubE {Δ} Γ₁ Γ₂ = ∀ {l} {T : Type Δ l} → inn T Γ₁ → Expr Δ Γ₂ T

idₛE : SubE Γ Γ
idₛE = `_

wkₛE : ∀ {l Δ} {Γ₁ Γ₂ : TEnv Δ} {T : Type Δ l} → SubE Γ₁ Γ₂ → SubE Γ₁ (T ◁ Γ₂)
wkₛE σ x = wkE (σ x)

extₛE : SubE Γ₁ Γ₂ → SubE (T ◁ Γ₁) (T ◁ Γ₂)
extₛE σ here = ` here
extₛE σ (there x) = wkE (σ x)

extₛEl : SubE Γ₁ Γ₂ → SubE (l ◁* Γ₁) (l ◁* Γ₂)
extₛEl σ (tskip x) = extEl (σ x)

subE : SubE Γ₁ Γ₂ → Expr Δ Γ₁ T → Expr Δ Γ₂ T
subE σ (` x) = σ x
subE σ (ƛ e) = ƛ subE (extₛE σ) e
subE σ (e₁ · e₂) = subE σ e₁ · subE σ e₂
subE σ (Λ l ⇒ e) = Λ l ⇒ subE (extₛEl σ) e
subE σ (e ∙ T) = subE σ e ∙ T

singleₛE : SubE Γ₁ Γ₂ → Expr Δ Γ₂ T → SubE (T ◁ Γ₁) Γ₂
singleₛE σ e' here = e'
singleₛE σ e' (there x) = σ x

_[_]E : Expr Δ (T₁ ◁ Γ) T₂ → Expr Δ Γ T₁ → Expr Δ Γ T₂
_[_]E e e' = subE (singleₛE idₛE e') e

subET : ∀ {l Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T₁ : Type Δ₁ l} {T₂ : Type Δ₂ l} → 
  Sub Δ₁ Δ₂ → Expr Δ₁ Γ₁ T₁ → Expr Δ₂ Γ₂ T₂
subET σ (` x) = {!   !}
subET σ (ƛ e) = {!   !}
subET σ (e · e₁) = {!   !}
subET σ (Λ l ⇒ e) = {!   !}
subET σ (e ∙ T′) = {!   !}

-- small step call by value semantics

data Val : ∀ {Δ} {T : Type Δ l}{Γ : TEnv Δ} → Expr Δ Γ T → Set where
  v-ƛ : ∀ {l Δ} {Γ : TEnv Δ} {T : Type Δ l} {T′ : Type Δ l}  {e : Expr Δ (T′ ◁ Γ) T} → 
    Val (ƛ e)
  v-Λ : ∀ {l Δ} {Γ : TEnv Δ} {T : Type (l ∷ Δ) l′} {e : Expr (l ∷ Δ) (l ◁* Γ) T} →
    Val (Λ l ⇒ e)

data _↪_ : ∀ {Δ} {T : Type Δ l}{Γ : TEnv Δ} → Expr Δ Γ T → Expr Δ Γ T → Set where
  β-ƛ : 
     Val e₂ →
     ((ƛ e₁) · e₂) ↪ (e₁ [ e₂ ]E)
  {- β-Λ  : →
     Val e₂ →
     (Λ l  e₁) · t₂ ↪ (e₁ [ t₂ ]) -}
  ξ-·₁ : ∀ {T : Type Δ l} {T′ : Type Δ l′} {Γ : TEnv Δ} {e e₁ : Expr Δ Γ (T  ⇒ T′)} {e₂ : Expr Δ Γ T} →
    e₁ ↪ e →
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ : ∀ {T : Type Δ l} {T′ : Type Δ l′} {Γ : TEnv Δ} {e₁ : Expr Δ Γ (T  ⇒ T′)} {e e₂ : Expr Δ Γ T} →
    e₂ ↪ e → 
    Val e₁ →
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-∙ : ∀ {T : Type Δ l} {T′ : Type (l ∷ Δ) l′} {Γ : TEnv Δ} {e e' : Expr Δ Γ (`∀α l , T′)} →
    e ↪ e' →
    (e ∙ T) ↪ (e' ∙ T)
 