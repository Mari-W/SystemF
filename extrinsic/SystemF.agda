module SystemF where

open import Level
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)

open ≡-Reasoning

open import Kits

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_
infixr  5  λx_  Λ[α:_]_  ∀[α∶_]_
infixr  6  _⇒_
infixl  6  _·_  _∙_
infix   7  `_

-- Sorts -----------------------------------------------------------------------

data Sort : SortTy → Set where -- Our syntax supports:
  𝕖     : Sort Var    -- expressions and expression variables;
  𝕥     : Sort Var    -- types and type variables; and
  𝕜     : Sort NoVar  -- kinds, but no kind variables.

-- Syntax ----------------------------------------------------------------------

private variable
  st                         : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃'  : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃'  : List (Sort Var)
  x y z x₁ x₂                : S ∋ s
  l l′ l₁ l₂ l₃              : Level



data _⊢_ : List (Sort Var) → Sort st → Set where
  `_        : S ∋ s → S ⊢ s                -- Expr and Type Var
  λx_       : (𝕖 ∷ S) ⊢ 𝕖 → S ⊢ 𝕖          -- Expr Abstraction
  Λ[α:_]_   : Level → (𝕥 ∷ S) ⊢ 𝕖 → S ⊢ 𝕖  -- Type Abstraction
  ∀[α∶_]_   : Level → (𝕥 ∷ S) ⊢ 𝕥 → S ⊢ 𝕥  -- Univ Quant
  _·_       : S ⊢ 𝕖 → S ⊢ 𝕖 → S ⊢ 𝕖        -- Expr Application
  _∙_       : S ⊢ 𝕖 → S ⊢ 𝕥 → S ⊢ 𝕖        -- Type Application
  _⇒_       : S ⊢ 𝕥 → S ⊢ 𝕥 → S ⊢ 𝕥         -- Function Type
  ★[_]      : Level → S ⊢ 𝕜                -- Type Kind

private variable
  e e₁ e₂ e₃ e' e₁' e₂'  : S ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂'  : S ⊢ 𝕥
  k k₁ k₂ k₃ k' k₁' k₂'  : S ⊢ 𝕜
  E E₁ E₂ E₃ E' E₁' E₂'  : S ⊢ s

-- Substitution & Lemmas -------------------------------------------------------

-- Can be derived in the full framework.
SystemF-Syntax : Syntax
SystemF-Syntax = record
  { Sort         = Sort
  ; _⊢_          = _⊢_
  ; `_           = `_
  ; `-injective  = λ { refl → refl } }

open Syntax SystemF-Syntax hiding (Sort; _⊢_; `_)

-- Can be derived in the full framework.
_⋯_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = `/id (x & ϕ)
(λx t)          ⋯ ϕ = λx (t ⋯ (ϕ ↑ 𝕖))
(Λ[α: l ] t)    ⋯ ϕ = Λ[α: l ] (t ⋯ (ϕ ↑ 𝕥))
(∀[α∶ l ] t)    ⋯ ϕ = ∀[α∶ l ] (t ⋯ (ϕ ↑ 𝕥))
(t₁ · t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) · (t₂ ⋯ ϕ)
(t₁ ∙ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ∙ (t₂ ⋯ ϕ)
(t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
★[ l ]              ⋯ ϕ = ★[ l ]

-- Can be derived in the full framework.
⋯-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s) → t ⋯ id ⦃ K ⦄ ≡ t
⋯-id ⦃ K ⦄ (` x)     = `/`-is-` ⦃ K ⦄ x
⋯-id (t₁ · t₂)       = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
⋯-id (λx t)          = cong λx_ (
  t ⋯ (id ↑ 𝕖)  ≡⟨ cong (t ⋯_) (~-ext id↑~id) ⟩
  t ⋯ id        ≡⟨ ⋯-id t ⟩
  t             ∎)
⋯-id (Λ[α: l ] t)    = cong Λ[α: l ]_ (
  t ⋯ (id ↑ 𝕥)  ≡⟨ cong (t ⋯_) (~-ext id↑~id) ⟩
  t ⋯ id        ≡⟨ ⋯-id t ⟩
  t             ∎)
⋯-id (∀[α∶ l ] t₂)  = cong ∀[α∶ l ]_ (
  t₂ ⋯ (id ↑ 𝕥)  ≡⟨ cong (t₂ ⋯_) (~-ext id↑~id) ⟩
  t₂ ⋯ id        ≡⟨ ⋯-id t₂ ⟩
  t₂             ∎)
⋯-id (t₁ ∙ t₂)       = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
⋯-id (t₁ ⇒ t₂)       = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
⋯-id ★[ l ]          = refl

-- Can be derived in the full framework.
SystemF-Traversal : Traversal
SystemF-Traversal = record
  { _⋯_ = _⋯_ ; ⋯-id = ⋯-id ; ⋯-var = λ x ϕ → refl }

open Traversal SystemF-Traversal hiding (_⋯_; ⋯-id)

-- Can be derived in the full framework.
⋯-fusion :
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
    ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)
  → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₖ ϕ₂)
⋯-fusion (` x)          ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
⋯-fusion (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_  (⋯-fusion t₁ ϕ₁ ϕ₂)
                                          (⋯-fusion t₂ ϕ₁ ϕ₂)
⋯-fusion (λx t)         ϕ₁ ϕ₂ = cong λx_ (
  (t ⋯ (ϕ₁ ↑ 𝕖)) ⋯ (ϕ₂ ↑ 𝕖)   ≡⟨ ⋯-fusion t (ϕ₁ ↑ 𝕖) (ϕ₂ ↑ 𝕖) ⟩
  t ⋯ ((ϕ₁ ↑ 𝕖) ·ₖ (ϕ₂ ↑ 𝕖))  ≡⟨ cong (t ⋯_) (sym (
                                   ~-ext (dist-↑-· 𝕖 ϕ₁ ϕ₂))) ⟩
  t ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ 𝕖)        ∎)
⋯-fusion (Λ[α: l ] t)         ϕ₁ ϕ₂ = cong Λ[α: l ]_ (
  (t ⋯ (ϕ₁ ↑ 𝕥)) ⋯ (ϕ₂ ↑ 𝕥)
    ≡⟨ ⋯-fusion t (ϕ₁ ↑ 𝕥) (ϕ₂ ↑ 𝕥) ⟩
  t ⋯ ((ϕ₁ ↑ 𝕥) ·ₖ (ϕ₂ ↑ 𝕥))
    ≡⟨ cong (t ⋯_) (sym (~-ext (dist-↑-· 𝕥 ϕ₁ ϕ₂))) ⟩
  t ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ 𝕥)
    ∎)
⋯-fusion (∀[α∶ l ] t₂) ϕ₁ ϕ₂ =
  cong ∀[α∶ l ]_ (
    (t₂ ⋯ (ϕ₁ ↑ 𝕥)) ⋯ (ϕ₂ ↑ 𝕥)
      ≡⟨ ⋯-fusion t₂ (ϕ₁ ↑ 𝕥) (ϕ₂ ↑ 𝕥) ⟩
    t₂ ⋯ ((ϕ₁ ↑ 𝕥) ·ₖ (ϕ₂ ↑ 𝕥))
      ≡⟨ cong (t₂ ⋯_) (sym (~-ext (dist-↑-· 𝕥 ϕ₁ ϕ₂))) ⟩
    t₂ ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ 𝕥)
      ∎)
⋯-fusion (t₁ ∙ t₂)      ϕ₁ ϕ₂ =
  cong₂ _∙_ (⋯-fusion t₁ ϕ₁ ϕ₂) (⋯-fusion t₂ ϕ₁ ϕ₂)
⋯-fusion (t₁ ⇒ t₂)      ϕ₁ ϕ₂ =
  cong₂ _⇒_ (⋯-fusion t₁ ϕ₁ ϕ₂) (⋯-fusion t₂ ϕ₁ ϕ₂)
⋯-fusion ★[ l ]              ϕ₁ ϕ₂ = refl

-- Can be derived in the full framework.
SystemF-CTraversal : ComposeTraversal
SystemF-CTraversal = record { ⋯-fusion = ⋯-fusion }

open ComposeTraversal SystemF-CTraversal hiding (⋯-fusion)

-- Type System -----------------------------------------------------------------

SystemF-Types : Types
SystemF-Types = record
  { ↑ᵗ = λ { 𝕖 → _ , 𝕥 ; 𝕥 → _ , 𝕜 ; 𝕜 → _ , 𝕜 } }

open Types SystemF-Types

private variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx S
  T T₁ T₂ T' T₁' T₂' : S ∶⊢ s

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢`  :  ∀ {x : S ∋ s} {T : S ∶⊢ s} →
         Γ ∋ x ∶ T →
         Γ ⊢ ` x ∶ T
  ⊢λ  :  ∀ {e : (𝕖 ∷ S) ⊢ 𝕖} →
         (t₁ ∷ₜ Γ) ⊢ e ∶ (wk _ t₂) →
         Γ ⊢ λx e ∶ t₁ ⇒ t₂
  ⊢Λ  :  (★[ l ] ∷ₜ Γ) ⊢ e ∶ t₂ →
         Γ ⊢ Λ[α: l ] e ∶ ∀[α∶ l ] t₂
  ⊢·  :  Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
         Γ ⊢ e₂ ∶ t₁ →
         Γ ⊢ e₁ · e₂ ∶ t₂
  ⊢∙  :  {Γ : Ctx S} →
         (★[ l ] ∷ₜ Γ) ⊢ t₁ ∶ ★[ l′ ] →
         Γ ⊢ t₂ ∶ ★[ l ] →
         Γ ⊢ e₁ ∶ ∀[α∶ l ] t₁ →
         Γ ⊢ e₁ ∙ t₂ ∶ t₁ ⋯ ⦅ t₂ ⦆
  ⊢⇒  :  Γ ⊢ t₁ ∶ ★[ l ] → 
         Γ ⊢ t₂ ∶ ★[ l′ ] →
         Γ ⊢ t₁ ⇒ t₂ ∶ ★[ l ⊔ l′ ]
  ⊢∀  :  (★[ l ] ∷ₜ Γ) ⊢ t ∶ ★[ l′ ] →
         Γ ⊢ ∀[α∶ l ] t ∶ ★[ Level.suc l ⊔ l′ ]

SystemF-Typing : Typing
SystemF-Typing = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }

open Typing SystemF-Typing hiding (_⊢_∶_; ⊢`) 

_⊢⋯_ :
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TypingKit K ⦄
    ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit K K K ⦄
    ⦃ C₃ : ComposeKit K Kₛ Kₛ ⦄
    {S₁ S₂ st} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
⊢` ⊢x ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ⊢x)
⊢λ {t₂ = t₂} ⊢e ⊢⋯ ⊢ϕ =
  ⊢λ (subst  (_ ⊢ _ ∶_) (sym (⋯-↑-wk t₂ _ _))
             (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
⊢Λ ⊢e ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢· ⊢e₁ ⊢e₂ ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢∙ {t₁ = t₁} {t₂ = t₂} ⊢t₁ ⊢t₂ ⊢e₁ ⊢⋯ ⊢ϕ =
  subst  (_ ⊢ _ ∶_) (sym (dist-↑-⦅⦆-⋯ t₁ t₂ _))
         (⊢∙ (⊢t₁ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)) (⊢t₂ ⊢⋯ ⊢ϕ) (⊢e₁ ⊢⋯ ⊢ϕ))
⊢⇒ ⊢τ₁ ⊢τ₂ ⊢⋯ ⊢ϕ = ⊢⇒ (⊢τ₁ ⊢⋯ ⊢ϕ) (⊢τ₂ ⊢⋯ ⊢ϕ)
⊢∀ ⊢τ ⊢⋯ ⊢ϕ = ⊢∀ (⊢τ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))

SystemF-TTraversal : TypingTraversal
SystemF-TTraversal = record { _⊢⋯_ = _⊢⋯_ }

open TypingTraversal SystemF-TTraversal hiding (_⊢⋯_)

-- Semantics -------------------------------------------------------------------

data _↪_ : S ⊢ s → S ⊢ s → Set where
  β-λ   :  ∀ {e₂ : S ⊢ 𝕖} → (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-Λ   :  ∀ {t₂ : S ⊢ 𝕥} → (Λ[α: l ] e₁) ∙ t₂ ↪ e₁ ⋯ ⦅ t₂ ⦆
  ξ-λ   :  e ↪ e' → λx e ↪ λx e'
  ξ-Λ   :  e ↪ e' → Λ[α: l ] e ↪ Λ[α: l ] e'
  ξ-·₁  :  e₁ ↪ e₁' → e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂  :  e₂ ↪ e₂' → e₁ · e₂ ↪ e₁ · e₂'
  ξ-∙₁  :  e₁ ↪ e₁' → e₁ ∙ t₂ ↪ e₁' ∙ t₂

-- Subject Reduction -----------------------------------------------------------

subject-reduction : Γ ⊢ e ∶ t → e ↪ e' → Γ ⊢ e' ∶ t
subject-reduction (⊢· {t₂ = t₂} (⊢λ ⊢e₁) ⊢e₂) β-λ =
  subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆-⋯ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ (⊢Λ ⊢e₁)) β-Λ = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢t₂ ⦆ₛ
subject-reduction (⊢λ ⊢e) (ξ-λ e↪e') =
  ⊢λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢Λ ⊢e) (ξ-Λ e↪e') =
  ⊢Λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ e₁↪e₁') =
  ⊢· (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e₂') =
  ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ ⊢e₁) (ξ-∙₁ e₁↪e₁') =
  ⊢∙ ⊢t₁ ⊢t₂ (subject-reduction ⊢e₁ e₁↪e₁')

-- Denotational Semantics ------------------------------------------------------

Envₜ : Ctx S → Setω
Envₜ {S = S} Γ = ∀ (l : Level) → (x : S ∋ 𝕥) → 
  Γ ∋ x ∶ ★[ l ] →
  Set l

variable η η′ η₁ η₂ η₃ : Envₜ Γ

extₜ : Envₜ Γ → Set l → Envₜ (_∷ₜ_ {s = 𝕥} ★[ l ] Γ)
extₜ Γ ⟦t⟧ _ _∋_.zero refl = ⟦t⟧
extₜ Γ ⟦t⟧ l (_∋_.suc x) ⊢x = Γ l x {!  !}

extₜ-t : Envₜ Γ → Envₜ (_∷ₜ_ {s = 𝕖} t Γ)
extₜ-t Γ _ (_∋_.suc x) ⊢x = Γ _ x {!   !}

⟦_⟧ₜ : Γ ⊢ t ∶ ★[ l ] → Envₜ Γ → Set l
⟦ ⊢` {x = x} ⊢x ⟧ₜ η = η _ x ⊢x
⟦ ⊢⇒ ⊢t₁ ⊢t₂ ⟧ₜ η = ⟦ ⊢t₁ ⟧ₜ η → ⟦ ⊢t₂ ⟧ₜ η
⟦ ⊢∀ {l = l} ⊢t ⟧ₜ η = (⟦t⟧ : Set l) → ⟦ ⊢t ⟧ₜ (extₜ η ⟦t⟧)

Envₑ : (Γ : Ctx S) → Envₜ Γ → Setω
Envₑ {S = S} Γ η = ∀ (l : Level) (x : S ∋ 𝕖) (t : S ⊢ 𝕥) (⊢t : Γ ⊢ t ∶ ★[ l ]) → 
  Γ ∋ x ∶ t → 
  ⟦ ⊢t ⟧ₜ η 

extₑ : ∀ {⊢t : Γ ⊢ t ∶ ★[ l ]} {η : Envₜ Γ} → 
  Envₑ Γ η → 
  ⟦ ⊢t ⟧ₜ η →
  Envₑ (_∷ₜ_ {s = 𝕖} t Γ) (extₜ-t η)
extₑ Γ ⟦e⟧ = {!   !}

extₑ-t : ∀ {η : Envₜ Γ} → 
  Envₑ Γ η → 
  (⟦t⟧ : Set l) → 
  Envₑ (_∷ₜ_ {s = 𝕥} ★[ l ] Γ) (extₜ η ⟦t⟧)
extₑ-t Γ ⟦t⟧ = {!   !}

⟦_⟧ₑ : ∀ {η : Envₜ Γ} → 
  Γ ⊢ e ∶ t → 
  (⊢t : Γ ⊢ t ∶ ★[ l ]) → 
  Envₑ Γ η → ⟦ ⊢t ⟧ₜ η
⟦ ⊢` {x = x} ⊢x ⟧ₑ ⊢t γ = γ _ x _ ⊢t ⊢x
⟦ ⊢λ ⊢e ⟧ₑ (⊢⇒ ⊢t₁ ⊢t₂) γ = {!   !}
⟦ ⊢Λ ⊢e ⟧ₑ (⊢∀ ⊢t) γ = {!   !}
⟦ ⊢· ⊢e₁ ⊢e₂ ⟧ₑ ⊢t γ = {!   !} -- produces multiple cases when split on ⊢t
⟦ ⊢∙ ⊢e ⊢e₁ ⊢e₂ ⟧ₑ ⊢t γ = {!  !}