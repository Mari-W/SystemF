--{-# OPTIONS --allow-unsolved-metas #-}
-- This file contains the definitions for expression renamings and
-- substitutions and related operations like lifting and composition.

module StratF.ExpSubstitution where

open import Level
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; [] ; _∷_)
open import Data.Product.Base using (_,_)
open import Function using (_∘_; id; flip; _$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.Expressions
open import StratF.ExpEnvironments
open import StratF.TypeSubstProperties
open import StratF.TypeSubstitution
  using (TRen; Tidᵣ; Tskipᵣ; Tliftᵣ; ⟦_⟧Tᵣ_; TSub; Tidₛ; Tliftₛ; ⟦_⟧Tₛ_; _[_]Tₛ; [_]T)
open import StratF.Types
open import StratF.TypeEnvironments

--! Sub >

-- expression renamings: on values!

-- functional representation

VREN : (Γ₁ Γ₂ : Env Δ) → Set
VREN {Δ = Δ} Γ₁ Γ₂ = ∀ {l} {T : Type Δ l} → T ∈ Γ₁ → T ∈ Γ₂

-- equivalent to 'closure' form

module _ (ρ : VREN (T ∷ Γ₁) Γ₂) where

  popᵣ : VREN Γ₁ Γ₂
  popᵣ = ρ ∘ there

  topᵣ : T ∈ Γ₂
  topᵣ = ρ here

data ECloᵣ {Δ} Γ₂ : (Γ₁ : Env Δ) → Set where
  []  : ECloᵣ Γ₂ []
  _∷_ : ∀ {l} {T : Type Δ l} → T ∈ Γ₂ → ECloᵣ Γ₂ Γ₁ → ECloᵣ Γ₂ (T ∷ Γ₁)


tabulateᵣ : VREN Γ₁ Γ₂ → ECloᵣ Γ₂ Γ₁
tabulateᵣ {Γ₁ = []}    _ = []
tabulateᵣ {Γ₁ = _ ∷ _} ρ = topᵣ ρ ∷ tabulateᵣ (popᵣ ρ)

lookupᵣ : ECloᵣ Γ₂ Γ₁ → VREN Γ₁ Γ₂
lookupᵣ (T ∷ ρ) = λ where here → T ; (there x) → lookupᵣ ρ x

--! DefVren
record VRen (Γ₁ Γ₂ : Env Δ) : Set where
  constructor mkVren
  field
    vren : VREN Γ₁ Γ₂

  ER-level : Level
  ER-level = (Γ-level Γ₁) ⊔ (Γ-level Γ₂)

-- make VREN definitions into manifest fields

  wkᵣ : VREN Γ₁ (T ∷ Γ₂)
  wkᵣ = there ∘ vren

  liftᵣ : VREN (T ∷ Γ₁) (T ∷ Γ₂)
  liftᵣ here      = here
  liftᵣ (there x) = there $ vren x

  skipᵣ : VREN ([ l ]∷ Γ₁) ([ l ]∷ Γ₂)
  skipᵣ y with T , refl , x ← ⟦ y ⟧∈-wk⁻¹ = ⟦ vren x ⟧∈-wk


module _ (ρ : VRen (T ∷ Γ₁) Γ₂) where

  open VRen ρ

  Epopᵣ : VRen Γ₁ Γ₂
  vren Epopᵣ = popᵣ vren

  Etopᵣ : T ∈ Γ₂
  Etopᵣ = topᵣ vren

open VRen public using (vren)

-- then instantiate those definitions at top-level

module _ (ρ : VRen Γ₁ Γ₂) where

  open VRen ρ

  Vwkᵣ : VRen Γ₁ (T ∷ Γ₂)
  vren Vwkᵣ = wkᵣ

  Vliftᵣ : VRen (T ∷ Γ₁) (T ∷ Γ₂)
  vren Vliftᵣ = liftᵣ

  VΓskipᵣ : VRen ([ l ]∷ Γ₁) ([ l ]∷ Γ₂)
  vren VΓskipᵣ = skipᵣ


variable
  ρ ρ₁ ρ₂ : VRen Γ₁ Γ₂

--! DefTidR
Vidᵣ : VRen Γ Γ
vren Vidᵣ = id

Vskipᵣ : VRen Γ (T ∷ Γ)
Vskipᵣ = Vwkᵣ Vidᵣ

--! DefVren

-- generalised 'skipᵣ' (!)

module _ (ρ* : TRen Δ Δ′) (ρ : VRen (⟦ Γ₁ ⟧EEᵣ ρ*) Γ₂) where

  Vgskipᵣ : VRen (⟦ [ l ]∷ Γ₁ ⟧EEᵣ Tliftᵣ ρ*) ([ l ]∷ Γ₂)
  Vgskipᵣ {l = l} rewrite Γliftᵣ ρ* l Γ₁ = VΓskipᵣ ρ

Vren* : (ρ* : TRen Δ₁ Δ₂) → VRen (⟦ Γ₁ ⟧EEᵣ ρ*) Γ₂ → Val Γ₁ T → Val Γ₂ (⟦ T ⟧Tᵣ ρ*)
Eren* : (ρ* : TRen Δ₁ Δ₂) → VRen (⟦ Γ₁ ⟧EEᵣ ρ*) Γ₂ → Exp Γ₁ T → Exp Γ₂ (⟦ T ⟧Tᵣ ρ*)

Vren* ρ* ρ (‵ x) = ‵ vren ρ (ΓRen-∈ ρ* x)
Vren* ρ* ρ (# n) = # n
Vren* ρ* ρ (ƛ e) = ƛ Eren* ρ* (Vliftᵣ ρ) e
Vren* {Γ₁ = Γ₁} ρ* ρ (Λ l ⇒ e)
  with e′ ← Eren* (Tliftᵣ ρ*) (Vgskipᵣ ρ* ρ) e
  rewrite Γliftᵣ ρ* l Γ₁
  = Λ l ⇒ e′

Eren* ρ* ρ (‵val v)      = ‵val $ Vren* ρ* ρ v
Eren* ρ* ρ (‵suc e)      = ‵suc $ Eren* ρ* ρ e
Eren* ρ* ρ (f · e)       = (Eren* ρ* ρ f) · (Eren* ρ* ρ e)
Eren* ρ* ρ (e ∙[ T ] T′) 
  with e′ ← Eren* ρ* ρ e
  rewrite swap-Tren-[] ρ* T T′
  = e′ ∙ (⟦ T′ ⟧Tᵣ ρ*)

⟦_⟧Vᵣ_ : Val Γ₁ T → VRen Γ₁ Γ₂ → Val Γ₂ T
⟦_⟧Vᵣ_ {Γ₁ = Γ₁} {T = T} {Γ₂ = Γ₂} v ρ
  with ρ′ ← subst (flip VRen Γ₂) (sym ⟦ Γ₁ ⟧Γidᵣ≗id) ρ
  with v′ ← Vren* Tidᵣ ρ′ v
  rewrite ⟦ T ⟧Tidᵣ≗id
  = v′

⟦_⟧Eᵣ_ : Exp Γ₁ T → VRen Γ₁ Γ₂ → Exp Γ₂ T
⟦_⟧Eᵣ_ {Γ₁ = Γ₁} {T = T} {Γ₂ = Γ₂} e ρ
  with ρ′ ← subst (flip VRen Γ₂) (sym ⟦ Γ₁ ⟧Γidᵣ≗id) ρ
  with e′ ← Eren* Tidᵣ ρ′ e
  rewrite ⟦ T ⟧Tidᵣ≗id
  = e′

Vwk : Val Γ T′ → Val (T ∷ Γ) T′
Vwk = ⟦_⟧Vᵣ Vskipᵣ

Ewk : Exp Γ T′ → Exp (T ∷ Γ) T′
Ewk = ⟦_⟧Eᵣ Vskipᵣ

-- functional representation

ESUB : (Γ₁ Γ₂ : Env Δ) → Set
ESUB {Δ = Δ} Γ₁ Γ₂ = ∀ {l} {T : Type Δ l} → T ∈ Γ₁ → Exp {Δ} Γ₂ T

-- equivalent to 'closure' form

module _ (σ : ESUB (T ∷ Γ₁) Γ₂) where

  popₛ : ESUB Γ₁ Γ₂
  popₛ = σ ∘ there

  topₛ : Exp Γ₂ T
  topₛ = σ here

-- equivalent to 'closure' form

data ECloₛ {Δ} Γ₂ : (Γ₁ : Env Δ) → Set where
  []  : ECloₛ Γ₂ []
  _∷_ : ∀ {l} {T : Type Δ l} → Exp {Δ} Γ₂ T → ECloₛ Γ₂ Γ₁ → ECloₛ Γ₂ (T ∷ Γ₁)

tabulateₛ : ESUB Γ₁ Γ₂ → ECloₛ Γ₂ Γ₁
tabulateₛ {Γ₁ = []}    _ = []
tabulateₛ {Γ₁ = _ ∷ _} σ = topₛ σ ∷ tabulateₛ (popₛ σ)

lookupₛ : ECloₛ Γ₂ Γ₁ → ESUB Γ₁ Γ₂
lookupₛ (T ∷ ρ) = λ where here → T ; (there x) → lookupₛ ρ x

--! DefEsub
record ESub (Γ₁ Γ₂ : Env Δ) : Set where
  constructor mkESub
  field
    esub : ESUB Γ₁ Γ₂

  ES-level : Level
  ES-level = (Γ-level Γ₁) ⊔ (Γ-level Γ₂)

-- make ESUB definitions into manifest fields

  wkₛ : ESUB Γ₁ (T ∷ Γ₂)
  wkₛ = Ewk ∘ esub

  liftₛ : ESUB (T ∷ Γ₁) (T ∷ Γ₂)
  liftₛ here      = ‵var here
  liftₛ (there x) = Ewk $ esub x

  skipₛ : ESUB ([ l ]∷ Γ₁) ([ l ]∷ Γ₂)
  skipₛ y with T , refl , x ← ⟦ y ⟧∈-wk⁻¹
    = Eren* Tskipᵣ Vidᵣ (esub x)

  extₛ : Exp Γ₂ T → ESUB (T ∷ Γ₁) Γ₂
  extₛ e here      = e
  extₛ e (there x) = esub x

  module _ (σ* : TSub Δ Δ′) where

    Γsub* : ESUB (⟦ Γ₁ ⟧EEₛ σ*) (⟦ Γ₂ ⟧EEₛ σ*)
    Γsub* y with T , refl , x ← ΓSub-∈⁻¹ σ* y
      = ⟦ esub x ⟧ETₛ σ*

module _ (σ : ESub (T ∷ Γ₁) Γ₂) where

  open ESub σ

  Epopₛ : ESub Γ₁ Γ₂
  esub Epopₛ = popₛ esub

  Etopₛ : Exp Γ₂ T
  Etopₛ = topₛ esub

open ESub public using (esub)

-- then instantiate those definitions at top-level

module _ (σ : ESub {Δ = Δ} Γ₁ Γ₂) where

  open ESub σ

  Ewkₛ : ESub Γ₁ (T ∷ Γ₂)
  esub Ewkₛ = wkₛ

  Eliftₛ : ESub (T ∷ Γ₁) (T ∷ Γ₂)
  esub Eliftₛ = liftₛ

  Eskipₛ : ESub ([ l ]∷ Γ₁) ([ l ]∷ Γ₂)
  esub Eskipₛ = skipₛ

  Eextₛ : Exp Γ₂ T → ESub (T ∷ Γ₁) Γ₂
  esub (Eextₛ e) = extₛ e

  module _ (σ* : TSub Δ Δ′) where

    EΓsub* : ESub (⟦ Γ₁ ⟧EEₛ σ*) (⟦ Γ₂ ⟧EEₛ σ*)
    esub EΓsub* = Γsub* σ*

⟦_⟧ESₛ_ : (σ : ESub {Δ = Δ} Γ₁ Γ₂) (σ* : TSub Δ Δ′) → ESub (⟦ Γ₁ ⟧EEₛ σ*) (⟦ Γ₂ ⟧EEₛ σ*)
⟦ σ ⟧ESₛ σ* = EΓsub* σ σ*

infixr 5 _∷Eₛ_

_∷Eₛ_ : Exp Γ₂ T → ESub Γ₁ Γ₂ → ESub (T ∷ Γ₁) Γ₂
e ∷Eₛ σ = Eextₛ σ e

variable
  σ σ₁ σ₂ : ESub Γ₁ Γ₂

--! DefEidS
Eidₛ : ESub Γ Γ
esub Eidₛ = ‵var

--! DefEsub

-- generalised 'Eskipₛ' (! can this be simplified in terms of Eskipₛ? YES! !)

module _ (σ* : TSub Δ Δ′) (σ : ESub (⟦ Γ₁ ⟧EEₛ σ*) Γ₂) where

  Egskipₛ : ESub (⟦ [ l ]∷ Γ₁ ⟧EEₛ Tliftₛ σ*) ([ l ]∷ Γ₂)
  Egskipₛ {l = l} rewrite Γliftₛ σ* l Γ₁ = Eskipₛ σ

Vsub* : (σ* : TSub Δ₁ Δ₂) → ESub (⟦ Γ₁ ⟧EEₛ σ*) Γ₂ → Val Γ₁ T → Exp Γ₂ (⟦ T ⟧Tₛ σ*)
Esub* : (σ* : TSub Δ₁ Δ₂) → ESub (⟦ Γ₁ ⟧EEₛ σ*) Γ₂ → Exp Γ₁ T → Exp Γ₂ (⟦ T ⟧Tₛ σ*)

Vsub* σ* σ (‵ x)     = esub σ (ΓSub-∈ σ* x)
Vsub* σ* σ (# n)     = ‵# n
Vsub* σ* σ (ƛ e)     = ‵ƛ (Esub* σ* (Eliftₛ σ) e)
Vsub* σ* σ (Λ l ⇒ e) = ‵Λ l ⇒ Esub* (Tliftₛ σ*) (Egskipₛ σ* σ) e

Esub* σ* σ (‵val v)      = Vsub* σ* σ v
Esub* σ* σ (‵suc e)      = ‵suc $ Esub* σ* σ e
Esub* σ* σ (f · e)       = (Esub* σ* σ f) · (Esub* σ* σ e)
Esub* σ* σ (e ∙[ T ] T′) 
  with e′ ← Esub* σ* σ e
  rewrite swap-Tsub-[] σ* T T′
  = e′ ∙ (⟦ T′ ⟧Tₛ σ*)
{-
Vsub : (σ* : TSub Δ₁ Δ₂) → ESub (⟦ Γ₁ ⟧EEₛ σ*) Γ₂ → Val Γ₁ T → Exp Γ₂ (⟦ T ⟧Tₛ σ*)
Esub : (σ* : TSub Δ₁ Δ₂) → ESub (⟦ Γ₁ ⟧EEₛ σ*) Γ₂ → Exp Γ₁ T → Exp Γ₂ (⟦ T ⟧Tₛ σ*)

Vsub {Γ₁ = Γ₁} {Γ₂ = Γ₂} σ* σ = go module Vsub where
  go : Val Γ₁ T → Exp Γ₂ (⟦ T ⟧Tₛ σ*)
  go (‵ x) = esub σ (ΓSub-∈ σ* x)
  go (# n) = ‵# n
  go (ƛ e) = ‵ƛ (Esub* σ* (Eliftₛ σ) e)
  go (Λ l ⇒ e)
    with e′ ← Esub* (Tliftₛ σ*) (Egskipₛ σ* σ) e
    rewrite Γliftₛ σ* l Γ₁
    = ‵Λ l ⇒ e′

Esub {Γ₁ = Γ₁} {Γ₂ = Γ₂} σ* σ = go module Esub where
  go : Exp Γ₁ T → Exp Γ₂ (⟦ T ⟧Tₛ σ*)
  go (‵val v)      = Vsub* σ* σ v
  go (‵suc e)      = ‵suc $ go e
  go (f · e)       = go f · go e
  go (e ∙[ T ] T′) 
    with e′ ← go e
    rewrite swap-Tsub-[] σ* T T′
    = e′ ∙ (⟦ T′ ⟧Tₛ σ*)
-}
-- specialise to σ* = Tidₛ : TODO prove ⟦_⟧Eₛ σ ≗ Esub* Tidₛ σ

-- MW: in constrast to the definition in the case of expression renamings
-- we specialize the defintion and do not use an anlogous definition to the above.
-- i can't see any advantage as we need to prove the equality mentioned
-- in the comment above.
⟦_⟧Eₛ_ : Exp Γ₁ T → ESub Γ₁ Γ₂ → Exp Γ₂ T
⟦_⟧Vₛ_ : Val Γ₁ T → ESub Γ₁ Γ₂ → Exp Γ₂ T

⟦ ‵ x     ⟧Vₛ σ = esub σ x
⟦ # n     ⟧Vₛ σ = ‵# n
⟦ ƛ e     ⟧Vₛ σ = ‵ƛ (⟦ e ⟧Eₛ Eliftₛ σ)
⟦ Λ l ⇒ e ⟧Vₛ σ = ‵Λ l ⇒ (⟦ e ⟧Eₛ Eskipₛ σ)

⟦ ‵val v ⟧Eₛ σ = ⟦ v ⟧Vₛ σ
⟦ ‵suc e ⟧Eₛ σ = ‵suc (⟦ e ⟧Eₛ σ)
⟦ f · e  ⟧Eₛ σ = (⟦ f ⟧Eₛ σ) · (⟦ e ⟧Eₛ σ)
⟦ e ∙ T′ ⟧Eₛ σ = (⟦ e ⟧Eₛ σ) ∙ T′

_[_]Eₛ : Exp {Δ} (T₁ ∷ Γ) T₂ → Exp Γ T₁ → Exp Γ T₂
_[_]Eₛ e e′ = ⟦ e ⟧Eₛ (e′ ∷Eₛ Eidₛ)
