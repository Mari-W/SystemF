module StratF.TypeEnvironments where

open import Level
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_; _×_)
open import Data.Unit.Base using (⊤)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≗_; refl; cong)

variable l l′ l₁ l₂ l₃ : Level

-- type environments: type variables are represented by their level

TEnv = List Level

-- the empty type environment

Δ₀ : TEnv
Δ₀ = []

variable Δ Δ′ Δ₁ Δ₂ Δ₃ : TEnv

-- level of a type environment

Δ-level : TEnv → Level
Δ-level []      = zero
Δ-level (l ∷ Δ) = suc l ⊔ Δ-level Δ

-- semantic environments (mapping level l to an element of Set l)

-- MW: our early attempt to fit the denotational environment into set l, for some l, 
-- with homogenous lists did not work out because we where not allowed to calculcate the level of the data type based on the levels in LEnv. 
-- now, semantic environments are heterogenous lists and live in set l where l is the maximum level in our LEnv Δ.
-- here it is now allowed to calculate the level based on Δ, because this is a function!
⟦_⟧TE : (Δ : TEnv) → Set (Δ-level Δ)
⟦  []   ⟧TE = ⊤
⟦ l ∷ Δ ⟧TE = Set l × ⟦ Δ ⟧TE

-- curried form, for logical relations

⟦_⟧TE⇒Set_ : ∀ Δ l → Set (suc l ⊔ Δ-level Δ)
⟦   []  ⟧TE⇒Set l = Set l
⟦ l′ ∷ Δ ⟧TE⇒Set l = Set l′ → ⟦ Δ ⟧TE⇒Set l


variable
  η η₁ η₂ : ⟦ Δ ⟧TE

-- the empty semantic type environment

η₀ : ⟦ Δ₀ ⟧TE
η₀ = _

-- 'cons' for type environments

infixr 5 _∷η_

_∷η_ : Set l → ⟦ Δ ⟧TE → ⟦ l ∷ Δ ⟧TE
_∷η_ = _,_

-- equality on semantic type environments

-- MW: we also define a new equality that related is just a chain of equality proofs for each element. 
-- there is an isomorphism between _~_ and an _≡_.
-- this might allow us to build an equality proof between to semantic environments in a modular way via induction over Δ 
-- (since we cannot pattern match on product types)
_∼_ : ⟦ Δ ⟧TE → ⟦ Δ ⟧TE → Set (Δ-level Δ)
_∼_ {Δ = []}    _        _        = ⊤
_∼_ {Δ = l ∷ Δ} (S , η₁) (T , η₂) = S ≡ T × η₁ ∼ η₂

∼-refl : {η : ⟦ Δ ⟧TE} → η ∼ η
∼-refl {Δ = []}    = _
∼-refl {Δ = l ∷ Δ} = refl , ∼-refl {Δ = Δ}

∼-reflexive : {η₁ η₂ : ⟦ Δ ⟧TE} → η₁ ≡ η₂ → η₁ ∼ η₂
∼-reflexive refl = ∼-refl

∼⇒≡ : {η₁ η₂ : ⟦ Δ ⟧TE} → η₁ ∼ η₂ → η₁ ≡ η₂
∼⇒≡ {Δ = []}    {η₁ = ⊤} {η₂ = ⊤} _              = refl
∼⇒≡ {Δ = l ∷ Δ} {η₁ = _} {η₂ = _} (refl , η₁∼η₂) = cong (_ ,_) (∼⇒≡ η₁∼η₂)


-- environments can be constructed from functions, and vice versa

-- type variables

data _∈ᵗ_ : Level → TEnv → Set where
  here   : l ∈ᵗ (l ∷ Δ)
  there  : l ∈ᵗ Δ → l ∈ᵗ (l′ ∷ Δ)

-- interpreting type variables

⟦‵_⟧T_ : l ∈ᵗ Δ → ⟦ Δ ⟧TE → Set l
⟦‵ here    ⟧T  (T , _) = T
⟦‵ there α ⟧T  (_ , η) = ⟦‵ α ⟧T η

-- the interpretation is stable wrt _∼_

⟦`_⟧T∼_ : (α : l ∈ᵗ Δ) {η₁ η₂ : ⟦ Δ ⟧TE} → η₁ ∼ η₂ → (⟦‵ α ⟧T η₁) ≡ (⟦‵ α ⟧T η₂)
⟦` α ⟧T∼ η₁∼η₂ with refl ← ∼⇒≡ η₁∼η₂ = refl

-- functional type environments
-- NB the function space ∀ {l} → l ∈ᵗ Δ → Set l itself has sort Setω, so
-- as above, this representation is able to 'miniaturise' a (very) large
-- Set at a bounded level...

-- MW: in an functional representation we cannot use the `Set (Δ-level Δ)` approach because we need to quantify over l. 
-- note to myself: this would possibly expressible in my dependent type calculus where i allow quantification over non-limit ordinals, 
-- maybe something similar to this could be valid:
-- Δ-lub : TEnv → Level
-- Δ-lub Δ      = foldr _⊔_ zero Δ
-- notice that in constrast to Δ-level this does not give the level the env would live in but one below that, i.e. the maximum level in Δ
-- ⟦_⟧TEω : (Δ : TEnv) → Set (suc (Δ-lub Δ))
-- ⟦ Δ ⟧TEω = ∀ {l : Δ-lub Δ} → l ∈ᵗ Δ → Set l
-- notice that in the agda definition below implicitly it says 
-- ⟦ Δ ⟧TEω = ∀ {l : ω} → l ∈ᵗ Δ → Set ω

⟦_⟧TEω : (Δ : TEnv) → Setω
⟦ Δ ⟧TEω = ∀ {l} → l ∈ᵗ Δ → Set l

⟦_⟧TE⇒TEω : ⟦ Δ ⟧TE → ⟦ Δ ⟧TEω
⟦ η ⟧TE⇒TEω α = ⟦‵ α ⟧T η

⟦_⟧TEω⇒TE : ⟦ Δ ⟧TEω → ⟦ Δ ⟧TE
⟦_⟧TEω⇒TE {Δ = []}    _ = η₀
⟦_⟧TEω⇒TE {Δ = _ ∷ _} η = η here ∷η ⟦ η ∘ there ⟧TEω⇒TE

-- ⟦_⟧TE⇒TEω respects _∼_

⟦_⟧TE⇒TEω∼ : {η₁ η₂ : ⟦ Δ ⟧TE} → η₁ ∼ η₂ → ⟦ η₁ ⟧TE⇒TEω {l = l} ≗ ⟦ η₂ ⟧TE⇒TEω
⟦_⟧TE⇒TEω∼ η₁∼η₂ = ⟦`_⟧T∼ η₁∼η₂

-- the conversion TEω⇒TE respects extensional equivalence

⟦_⟧TEω⇒TE-ext : ∀ {f g : ⟦ Δ ⟧TEω} (f≗g : ∀ {l} → f {l = l} ≗ g) →
                ⟦ f ⟧TEω⇒TE ≡ ⟦ g ⟧TEω⇒TE
⟦ f≗g ⟧TEω⇒TE-ext = ∼⇒≡ (go f≗g) where
  go : ∀ {f g : ⟦ Δ ⟧TEω} (f≗g : ∀ {l} → f {l = l} ≗ g) →
       ⟦ f ⟧TEω⇒TE ∼ ⟦ g ⟧TEω⇒TE
  go {Δ = []}    f≗g = _
  go {Δ = _ ∷ _} f≗g = f≗g here , go (f≗g ∘ there)

-- the two representations are isomorphic

⟦_⟧TE⇒TEω∘TEω⇒TE≗id : (η : ⟦ Δ ⟧TE) → ⟦ ⟦ η ⟧TE⇒TEω ⟧TEω⇒TE ≡ η
⟦ η ⟧TE⇒TEω∘TEω⇒TE≗id = ∼⇒≡ go where
  go : {η : ⟦ Δ ⟧TE} → ⟦ ⟦ η ⟧TE⇒TEω ⟧TEω⇒TE ∼ η
  go {Δ = []}    = _
  go {Δ = _ ∷ Δ} = refl , go {Δ = Δ}

-- MW: avoids Setω equality, uses pointwise equality instead

⟦_⟧TEω⇒TE∘TE⇒TEω≗id : {η : ⟦ Δ ⟧TEω} → ⟦ ⟦ η ⟧TEω⇒TE ⟧TE⇒TEω ≗ η {l = l}
⟦ here    ⟧TEω⇒TE∘TE⇒TEω≗id = refl
⟦ there x ⟧TEω⇒TE∘TE⇒TEω≗id = ⟦ x ⟧TEω⇒TE∘TE⇒TEω≗id

 