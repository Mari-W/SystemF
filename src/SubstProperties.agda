{-# OPTIONS --allow-unsolved-metas #-}
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import Ext

module SubstProperties where

subst-irrelevant : 
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
    {F : A → Set ℓ₁}
    (eq eq' : a₁ ≡ a₂)
    (x : F a₁) 
  → subst F eq x ≡ subst F eq' x
subst-irrelevant refl refl x = refl

elim-subst :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ a₃ a₄ : A}
  → (F : A → Set ℓ₁)
  → (a₂≡a₁ : a₂ ≡ a₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F a₁)
  → subst F a₂≡a₁ (subst F a₁≡a₂ x) ≡ x
elim-subst _ refl refl _ = refl

elim-subst₃ :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ a₃ : A}
  → (F : A → Set ℓ₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (a₃≡a₁ : a₃ ≡ a₁)
  → (a₂≡a₃ : a₂ ≡ a₃)
  → (x : F a₂)
  → subst F a₁≡a₂ (subst F a₃≡a₁ (subst F a₂≡a₃ x)) ≡ x
elim-subst₃ _ refl refl refl _ = refl

dist-subst :
  ∀ {ℓ₁ ℓ₂}
    {A A′ : Set ℓ₁} {B B′ : Set ℓ₂}
  → (f : A → B)
  → (A≡A′ : A′ ≡ A)
  → (A→B≡A′→B′ : (A → B) ≡ (A′ → B′))
  → (B≡B′ : B ≡ B′)
  → (x : A′) 
  → subst id B≡B′ (f (subst id A≡A′ x)) ≡ subst id A→B≡A′→B′ f x
dist-subst _ refl refl refl _ = refl

dist-subst′ :
  ∀ {ℓ₁ ℓ₂}
    {A A′ : Set ℓ₁} {B B′ : Set ℓ₂}
  → (f : A → B)
  → (A≡A′ : A ≡ A′)
  → (A→B≡A′→B′ : (A → B) ≡ (A′ → B′))
  → (B≡B′ : B ≡ B′)
  → (x : A) 
  → subst id A→B≡A′→B′ f (subst id A≡A′ x) ≡ subst id B≡B′ (f x)
dist-subst′ _ refl refl refl _ = refl

dist-subst′′ :
  ∀ {ℓ₁ ℓ₂}
    {A : Set ℓ₁} {B B′ : A → Set ℓ₂} 
  → (a : A) 
  → (f : (a : A) → B a)
  → (A→B≡A′→B′ : ((a : A) → B a) ≡ ((a : A) → B′ a))
  → (B≡B′ : (a : A) → B a ≡ B′ a)
  → subst id (B≡B′ a) (f a) ≡ subst id A→B≡A′→B′ f a
dist-subst′′ a _ A→B≡A′→B′ B≡B′ with fun-ext B≡B′ | B≡B′ a
dist-subst′′ _ _ refl B≡B′ | refl | refl = refl 

dist-elim′′′ :
  ∀ {ℓ}
    {A A₁ A₂ A₃ A₄ A₅ : Set ℓ} 
  → (a : A₄) 
  → (A≡A₁ : A ≡ A₁)
  → (A₂≡A : A₂ ≡ A)
  → (A₃≡A₂ : A₃ ≡ A₂)
  → (A₃≡A₄ : A₄ ≡ A₃)
  → (A≡A' : A₅ ≡ A₁)
  → (A≡A₄ : A₄ ≡ A₅)
  → subst id A≡A₁ (subst id A₂≡A (subst id A₃≡A₂ (subst id A₃≡A₄ a))) ≡ subst id A≡A' (subst id A≡A₄ a)
dist-elim′′′ _ refl refl refl refl refl refl = refl  


dist-subst' :
  ∀ {ℓ ℓ' ℓ₁ ℓ₂} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A}
    {F : A → Set ℓ₁} {G : B → Set ℓ₂}
  → (a→b : A → B)
  → (f : ∀ {a} → F a → G (a→b a))
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (b₁≡b₂ : a→b a₁ ≡ a→b a₂)
  → (x : F a₁) 
  → f {a₂} (subst F a₁≡a₂ x) ≡ subst G b₁≡b₂ (f {a₁} x)
dist-subst' _ _ refl refl _ = refl
 
dist-subst′′′ :
  ∀ {ℓ₁ ℓ₂}
    {A : Set ℓ₁} {B : A → Set ℓ₂} 
  → (a : A) 
  → (a′ : A)
  → (f : (a : A) → B a)
  → (a≡a′ : a ≡ a′)
  → (Ba′≡Ba : B a′ ≡ B a)
  → f a ≡ subst id Ba′≡Ba (f a′)
dist-subst′′′ _ _ _ refl refl = refl

subst-cong :
  ∀ {ℓ}{ℓ₁}{ℓ₂}
    {A₁ : Set ℓ₁}
    {A₂ : Set ℓ₂}
  → (F : A₁ → Set ℓ)
  → (G : A₂ → A₁)
  → {x y : A₂}
  → (x≡y : x ≡ y)
  → (a : F (G x))
  → subst F (cong G x≡y) a ≡ subst (λ z → F (G z)) x≡y a
subst-cong F G refl a = refl