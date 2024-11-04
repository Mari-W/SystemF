module StratF.Util.Extensionality where

open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
import Axiom.Extensionality.Heterogeneous as HEq
open import Level
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_)

--open import StratF.Util.PropositionalSetOmegaEquality

--! TF >

-- Functional Extensionality for homogeneous equality

postulate
  fun-ext : ∀{a b} → Extensionality a b

  fun-ext₂ : ∀ {l₁}{l₂}{l₃} {A₁ : Set l₁} {A₂ : A₁ → Set l₂} {B : ∀ {x} → A₂ x → Set l₃}
             {f g : ∀ {x} → (y : A₂ x) → B y} →
             (∀ {x} (y : A₂ x) → f y ≡ g y) →
             (λ {x} → f {x}) ≡ g

-- Functional Extensionality for heterogeneous equality

fun-ext-h : ∀{a b} → HEq.Extensionality a b
fun-ext-h = HEq.≡-ext⇒≅-ext fun-ext

-- Functional Extensionality for dependent functions

--! DependentExt
dep-ext : ∀ {a b} {A : Set a} {F G : (α : A) → Set b} →
  ((α : A) → F α ≡ G α) → ((α : A) → F α) ≡ ((α : A) → G α)
dep-ext = ∀-extensionality fun-ext _ _
{-
-- Functional Extensionalities for Setω-equalities

postulate
  fun-extω : {B : (l : Level) → Set l} {f g : (x : Level) → B x} →
    (∀ x → f x ≡ g x) → f ≡ω g

postulate
  fun-extω₂ : ∀ {A : (l : Level) → Set}{B : (l : Level) → A l → Set l}
    {f g : (x : Level) (y : A x) → B x y} →
    (∀ x y → f x y ≡ g x y) → f ≡ω g

postulate
  fun-ext-llω-ω :
    ∀ {b} {B : Level → Set b} {c} {C : (x : Level) (y : B x) → Set c}
      {D : (x : Level) (y : B x) (z : C x y) → Set x}
    → {f g : ∀ (x : Level) (y : B x) (z : C x y) → D x y z}
    → (∀ x y z → f x y z ≡ g x y z)
    → f ≡ω g
-}
