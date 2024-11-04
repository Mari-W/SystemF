{-# OPTIONS --allow-unsolved-metas #-}
module StratF.LogicalRelation where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.List.Base using (List; []; _∷_; [_])
open import Data.Unit.Base using (⊤; tt)
open import Function.Base using (_∘_; id; _$_)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; subst-subst-sym; subst-sym-subst; subst-subst; -- Properties
        module ≡-Reasoning)
open ≡-Reasoning

open import StratF.BigStep
open import StratF.Evaluation
open import StratF.ExpSubstProperties
open import StratF.ExpSubstitution hiding (topₛ; popₛ; tabulateₛ; lookupₛ)
open import StratF.Expressions
open import StratF.ExpEnvironments
open import StratF.TypeSubstPropertiesSem
open import StratF.TypeSubstProperties
open import StratF.TypeSubstitution hiding (topₛ; popₛ; tabulateₛ; lookupₛ)
open import StratF.Types
open import StratF.TypeEnvironments
open import StratF.Util.Extensionality

-- from TypeSubstPropertiesSem

TSub₀ : (Δ : TEnv) → Set
TSub₀ Δ = TSub Δ Δ₀

τ↑T[T′]≡TextₛτT′T : (τ* : TSub₀ Δ) (T′ : Type₀ l) (T : Type (l ∷ Δ) l′) →
                    (⟦ T ⟧Tₛ Tliftₛ τ*) [ T′ ]Tₛ ≡ ⟦ T ⟧Tₛ (T′ ∷Tₛ τ*)
τ↑T[T′]≡TextₛτT′T τ* T′ T =
  begin
    (⟦ T ⟧Tₛ Tliftₛ τ*) [ T′ ]Tₛ
  ≡⟨ fusionₛₛ T _ _ ⟩
    ⟦ T ⟧Tₛ (Tliftₛ τ* ∘ₛₛ (T′ ∷Tₛ Tidₛ))
  ≡⟨ cong ⟦ T ⟧Tₛ_ (Tliftₛ∘Textₛ τ* T′) ⟩
    ⟦ T ⟧Tₛ (T′ ∷Tₛ τ*)
  ∎ where open ≡-Reasoning


--! Logical >

-- logical relation

-- relation between a closed syntactic value of type `synT` and
-- a semantic value of the corresponding type `⟦ synT ⟧T η₀`...
-- or perhaps any type `semT` such that `⟦ synT ⟧T η₀ ≡ semT`? 

record ⟦_⟧𝓡 {l} (T₀ : Type₀ l) : Set (suc l) where
  constructor mk𝓡
  field
    semT : Set l
    eqT  : ⟦ T₀ ⟧T η₀ ≡ semT
  RelT = REL (Val₀ T₀) semT l
  field
    relT : RelT

record ⟦_⟧𝓛 l : Set (suc l) where
  constructor mk𝓛
  field
    synT : Type₀ l
    𝓡elT : ⟦ synT ⟧𝓡

  open ⟦_⟧𝓡 𝓡elT public
    using (semT; eqT; RelT; relT)


open ⟦_⟧𝓛 public using (synT; semT; eqT; RelT; relT)

⟦_⟧𝓓ω : TEnv → Setω
⟦ Δ ⟧𝓓ω = ∀ {l} → (l ∈ᵗ Δ) → ⟦ l ⟧𝓛

--! TRelEnv
⟦_⟧𝓓 : (Δ : TEnv) → Set (Δ-level Δ)
⟦  []   ⟧𝓓 = ⊤
⟦ l ∷ Δ ⟧𝓓 = ⟦ l ⟧𝓛 × ⟦ Δ ⟧𝓓

δ₀ : ⟦ Δ₀ ⟧𝓓
δ₀ = _

variable
  δ : ⟦ Δ ⟧𝓓
  δω : ⟦ Δ ⟧𝓓ω

⟦_⟧𝓓⇒𝓓ω : (δ : ⟦ Δ ⟧𝓓) → ⟦ Δ ⟧𝓓ω
⟦ ρ , _ ⟧𝓓⇒𝓓ω here      = ρ
⟦ _ , δ ⟧𝓓⇒𝓓ω (there α) = ⟦ δ ⟧𝓓⇒𝓓ω α

⟦_⟧𝓓ω⇒𝓓 : ⟦ Δ ⟧𝓓ω → ⟦ Δ ⟧𝓓
⟦_⟧𝓓ω⇒𝓓 {Δ = []}    _  = _
⟦_⟧𝓓ω⇒𝓓 {Δ = l ∷ Δ} δω = δω here , ⟦ δω ∘ there ⟧𝓓ω⇒𝓓


module _ (δ : ⟦ Δ ⟧𝓓) where

  𝓓Tsub : TSub₀ Δ
  tsub 𝓓Tsub = synT ∘ ⟦ δ ⟧𝓓⇒𝓓ω

  𝓓Trel : ∀ {l} (α : l ∈ᵗ Δ) → RelT (⟦ δ ⟧𝓓⇒𝓓ω α)
  𝓓Trel = relT ∘ ⟦ δ ⟧𝓓⇒𝓓ω

lemmaδ₀ : 𝓓Tsub δ₀ ≡ Tidₛ
lemmaδ₀ = cong mkTSub $ fun-ext₂ λ ()


-- specialised logical relations

⟦_⟧TVREL_ : (T : Type Δ l) (δ : ⟦ Δ ⟧𝓓) → Set (suc l)
⟦_⟧TVREL_ {l = l} T δ = REL (Val₀ ⟦T⟧δ) (⟦ T ⟧T (⟦ η₀ ⟧TETₛ 𝓓Tsub δ)) l
  where ⟦T⟧δ = ⟦ T ⟧Tₛ 𝓓Tsub δ

⟦_⟧TEREL_ : (T : Type Δ l) (δ : ⟦ Δ ⟧𝓓) → Set (suc l)
⟦_⟧TEREL_ {l = l} T δ = REL (Exp₀ ⟦T⟧δ) (⟦ T ⟧T (⟦ η₀ ⟧TETₛ 𝓓Tsub δ)) l
  where ⟦T⟧δ = ⟦ T ⟧Tₛ 𝓓Tsub δ
  -- NB for synT = ⟦T⟧δ, semT = ⟦ T ⟧T (⟦ η₀ ⟧TETₛ 𝓓Tsub δ), we have
  -- eqT = subst-preserves (𝓓Tsub δ) T {η = η₀} : semT ≡ ⟦ ⟦T⟧δ ⟧T η₀

-- pattern _∷⟦_⟧𝓓_ R T δ = record { synT = T ; relT = R } , δ
-- relT Ρ ∷⟦ synT Ρ ⟧𝓓 ⟦ δω ∘ there ⟧𝓓ω⇒𝓓  where Ρ = ...

-- type renaming acting on ⟦_⟧𝓓 by composition
--! TrenAct

⟦_⟧𝓓ᵣ_ : ⟦ Δ₂ ⟧𝓓 → (ρ* : TRen Δ₁ Δ₂) → ⟦ Δ₁ ⟧𝓓
⟦ δ ⟧𝓓ᵣ ρ* = ⟦ ⟦ δ ⟧𝓓⇒𝓓ω ∘ tren ρ* ⟧𝓓ω⇒𝓓
  
-- value substitution

-- functional representation

VSUB : (Γ₁ Γ₂ : Env Δ) → Set
VSUB {Δ = Δ} Γ₁ Γ₂ = ∀ {l} {T : Type Δ l} → T ∈ Γ₁ → Val {Δ} Γ₂ T

-- equivalent to 'closure' form

module _ (σ : VSUB (T ∷ Γ₁) Γ₂) where

  popₛ : VSUB Γ₁ Γ₂
  popₛ = σ ∘ there

  topₛ : Val Γ₂ T
  topₛ = σ here

-- equivalent to 'closure' form

data VCloₛ {Δ} Γ₂ : (Γ₁ : Env Δ) → Set where
  []  : VCloₛ Γ₂ []
  _∷_ : ∀ {l} {T : Type Δ l} → Val {Δ} Γ₂ T → VCloₛ Γ₂ Γ₁ → VCloₛ Γ₂ (T ∷ Γ₁)

tabulateₛ : VSUB Γ₁ Γ₂ → VCloₛ Γ₂ Γ₁
tabulateₛ {Γ₁ = []}    _ = []
tabulateₛ {Γ₁ = _ ∷ _} σ = topₛ σ ∷ tabulateₛ (popₛ σ)

lookupₛ : VCloₛ Γ₂ Γ₁ → VSUB Γ₁ Γ₂
lookupₛ (T ∷ ρ) = λ where here → T ; (there x) → lookupₛ ρ x

--! DefVsub
record VSub (Γ₁ Γ₂ : Env Δ) : Set where
  constructor mkVSub
  field
    vsub : VSUB Γ₁ Γ₂

  VS-level : Level
  VS-level = (Γ-level Γ₁) ⊔ (Γ-level Γ₂)

-- make VSUB definitions into manifest fields

  vs⇒es : ESUB  Γ₁ Γ₂
  vs⇒es = ‵val ∘ vsub

  wkₛ : VSUB Γ₁ (T ∷ Γ₂)
  wkₛ = Vwk ∘ vsub

  liftₛ : VSUB (T ∷ Γ₁) (T ∷ Γ₂)
  liftₛ here      = ‵ here
  liftₛ (there x) = Vwk $ vsub x

  skipₛ : VSUB ([ l ]∷ Γ₁) ([ l ]∷ Γ₂)
  skipₛ y with T , refl , x ← ⟦ y ⟧∈-wk⁻¹
    = Vren* Tskipᵣ Vidᵣ (vsub x)

  extₛ : Val Γ₂ T → VSUB (T ∷ Γ₁) Γ₂
  extₛ v here      = v
  extₛ v (there x) = vsub x

  module _ (σ* : TSub Δ Δ′) where

    Γsub* : VSUB (⟦ Γ₁ ⟧EEₛ σ*) (⟦ Γ₂ ⟧EEₛ σ*)
    Γsub* y with T , refl , x ← ΓSub-∈⁻¹ σ* y
      = ⟦ vsub x ⟧VTₛ σ*

module _ (σ : VSub (T ∷ Γ₁) Γ₂) where

  open VSub σ

  Vpopₛ : VSub Γ₁ Γ₂
  vsub Vpopₛ = popₛ vsub

  Vtopₛ : Val Γ₂ T
  Vtopₛ = topₛ vsub

open VSub public using (vsub)

-- then instantiate those definitions at top-level

module _ (σ : VSub {Δ = Δ} Γ₁ Γ₂) where

  open VSub σ

  VS⇒ES : ESub  Γ₁ Γ₂
  esub VS⇒ES = vs⇒es

  Vwkₛ : VSub Γ₁ (T ∷ Γ₂)
  vsub Vwkₛ = wkₛ

--! DefEidS
Vidₛ : VSub Γ Γ
vsub Vidₛ = ‵_

-- finally

χ₀ : VSub (⟦ Γ₀ ⟧EEₛ Tidₛ) Γ₀
vsub χ₀ = ‵_

lemmaχ₀ : VS⇒ES χ₀ ≡ Eidₛ
lemmaχ₀ = refl

--! Logical >

--! MCVType/MCEType

𝓥⟦_⟧ : (T : Type Δ l) (δ : ⟦ Δ ⟧𝓓) → ⟦ T ⟧TVREL δ
--      Val₀ (⟦ T ⟧Tₛ 𝓓Tsub δ) → ⟦ T ⟧T (⟦ η₀ ⟧TETₛ 𝓓Tsub δ) → Set l

𝓔⟦_⟧ : (T : Type Δ l) (δ : ⟦ Δ ⟧𝓓) → ⟦ T ⟧TEREL δ
--      Exp₀ (⟦ T ⟧Tₛ 𝓓Tsub δ) → ⟦ T ⟧T (⟦ η₀ ⟧TETₛ 𝓓Tsub δ) → Set l

--! MCE
𝓔⟦ T ⟧ δ e₀ w = ∃[ v₀ ] (e₀ ⇓ v₀) × 𝓥⟦ T ⟧ δ v₀ w

--! MCV
𝓥⟦ ‵ℕ       ⟧ δ (# n) w = w ≡ n

𝓥⟦ T₁ ‵⇒ T₂ ⟧ δ (ƛ e) f = ∀ v₀ w → 𝓥⟦ T₁ ⟧ δ v₀ w → 𝓔⟦ T₂ ⟧ δ (e [ ‵val v₀ ]Eₛ) (f w)

𝓥⟦ ‵ α ⟧ δ v₀ w
  rewrite subst-var-preserves (𝓓Tsub δ) η₀ α
  rewrite eqT (⟦ δ ⟧𝓓⇒𝓓ω α)
  = 𝓓Trel δ α v₀ w

𝓥⟦ ‵∀[ T ] ⟧ δ (Λ l ⇒ e) F = ∀ (T′ : Type₀ l) (R : ⟦ l ⟧𝓛) →
  𝓔⟦ T ⟧ (R , δ) {!!} {!!}
{-
  where
  e[T′] = e [ T′ ]ETₛ
  F[T′] = F ⟦ T′ ⟧T₀
-}
-- extended LR on environments

--! MCG
⟦_⟧𝓖 :  (Γ : Env Δ) (δ : ⟦ Δ ⟧𝓓) → let τ* = 𝓓Tsub δ; η = ⟦ η₀ ⟧TETₛ τ*  in
        VSub (⟦ Γ ⟧EEₛ τ*) Γ₀ → ⟦ Γ ⟧EE η → Set (Γ-level Γ)
⟦ []     ⟧𝓖 δ χ _       = ⊤
⟦ T ∷ Γ  ⟧𝓖 δ χ (v , γ) =  𝓥⟦ T ⟧ δ (Vtopₛ χ) v × ⟦ Γ ⟧𝓖 δ (Vpopₛ χ) γ

𝓖₀ : ⟦ Γ₀ ⟧𝓖 δ₀ χ₀ γ₀
𝓖₀ = _
