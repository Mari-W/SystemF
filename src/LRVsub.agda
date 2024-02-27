module LRVsub where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; case_of_; _|>_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; dcong₂; subst; subst₂; resp₂; cong-app; icong;
        sym-cong; subst-∘; subst-application; subst-application′; subst-subst; subst-subst-sym; subst-sym-subst; -- Properties
        module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
-- module R = H.≅-Reasoning

open import Extensionality
open import PropositionalSetOmegaEquality
open import SubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import TypeSubstPropertiesSem 
open import Expressions
open import ExprSubstitution
open import ExprSubstProperties
open import BigStep
open import LogicalPrelim
open import Logical
open import LRVren

----------------------------------------------------------------------
--! LRVsub >

-- ext-σ-T′≡σ[T′] :
--   (T′        : Type Δ l′)
--   (T         : Type (l′ ∷ Δ) l)
--   (ρ         : RelEnv Δ)
--   (R′        : REL (Tsub (subst←RE ρ) T′))
--   → Tsub (subst←RE (REext ρ (Tsub (subst←RE ρ) T′ , R′))) T ≡ Tsub (subst←RE ρ) (T [ T′ ]T)
-- ext-σ-T′≡σ[T′] T′ T ρ R′ =
--   begin
--     Tsub (subst←RE (REext ρ (Tsub (subst←RE ρ) T′ , R′))) T
--   ≡⟨ cong (λ τ → Tsub τ T) (subst←RE-ext-ext ρ (Tsub (subst←RE ρ) T′) R′) ⟩
--     Tsub (Textₛ (subst←RE ρ) (Tsub (subst←RE ρ) T′)) T
--   ≡⟨ cong (λ τ → Tsub τ T) (fun-ext₂ (Text-sub-sub (subst←RE ρ) T′)) ⟩
--     Tsub (Textₛ Tidₛ T′ ∘ₛₛ subst←RE ρ) T
--   ≡⟨ sym (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) (subst←RE ρ)) ⟩
--     Tsub (subst←RE ρ) (T [ T′ ]T)
--   ∎ 

-- substitution action on RelEnv by composition

--! TsubAct
Tsub-act : TSub Δ₁ Δ₂ → RelEnv Δ₂ → RelEnv Δ₁
Tsub-act σ* ρ = λ l x →
  let ρ* = subst←RE ρ in
  let T₂ = σ* l x in
  Tsub ρ* T₂ , subst (λ ⟦x⟧ → (Value (Tsub ρ* T₂) → ⟦x⟧ → Set l)) (sym (subst-preserves (subst←RE ρ) T₂)) (𝓥⟦ T₂ ⟧ ρ)

--
subst-Tsub-act : (ρ : RelEnv Δ₂) (τ* : TSub Δ₁ Δ₂) → subst←RE (Tsub-act τ* ρ) ≡ (τ* ∘ₛₛ subst←RE ρ)
subst-Tsub-act ρ τ* = fun-ext₂ (helper ρ τ*)
  where
  helper : ∀ (ρ : RelEnv Δ₂) (τ* : TSub Δ₁ Δ₂) (l : Level) (x : l ∈ Δ₁)
    → subst←RE (Tsub-act τ* ρ) l x ≡ (τ* ∘ₛₛ subst←RE ρ) l x
  helper ρ τ* l here = refl
  helper ρ τ* l (there x) = refl

--
Tsub-act-REext-ext : (ρ : RelEnv Δ₂) (τ* : TSub Δ₁ Δ₂) (T′ : Type [] l) (R : REL T′)
  → ∀ l₂ x₂ → (REext (Tsub-act τ* ρ) (T′ , R)) l₂ x₂ ≡ Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)) l₂ x₂
Tsub-act-REext-ext ρ τ* T′ R l₂ here = refl
Tsub-act-REext-ext {l = l} ρ τ* T′ R l₂ (there x) =
  let ρ* = subst←RE ρ in
  let Tₓ = τ* l₂ x in
  let F = λ ⟦x⟧ → (Value (Tsub ρ* Tₓ) → ⟦x⟧ → Set l₂) in
  let eq₂ = subst-preserves ρ* Tₓ in
  let ρ*r = subst←RE (REext ρ (T′ , R)) in
  let Tₓr = (Tliftₛ τ* l) l₂ (there x) in
  let Fr = λ ⟦x⟧ → (Value (Tsub ρ*r Tₓr) → ⟦x⟧ → Set l₂) in
  let eq₂r = subst-preserves ρ*r Tₓr in
  let eq-1 = begin
               Tsub (subst←RE ρ) (τ* l₂ x)
             ≡˘⟨ fusion-Tsub-Tren (τ* l₂ x) (Twkᵣ Tidᵣ) (Textₛ (subst←RE ρ) T′)  ⟩
               Tsub (Textₛ (subst←RE ρ) T′) (Twk (τ* l₂ x))
             ≡˘⟨ cong (λ σ → Tsub σ (Twk (τ* l₂ x))) (subst←RE-ext-ext ρ T′ R) ⟩
               Tsub (subst←RE (REext ρ (T′ , R))) (Twk (τ* l₂ x))
             ∎ in
  let eq-ren = LRVren-eq Tₓ (REext ρ (T′ , R)) (Twkᵣ Tidᵣ) in
  let eq-2 = begin
          subst REL eq-1
            (subst F (sym eq₂)
              (𝓥⟦ Tₓ ⟧ ρ))
        ≡⟨ subst*-irrelevant (⟨ F , sym eq₂ ⟩∷ ⟨ REL , eq-1 ⟩∷ [] )
                             (⟨ (λ zz → Value (Tsub (Twkᵣ Tidᵣ ∘ᵣₛ ρ*r) Tₓ) → zz → Set l₂) , (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ)) ⟩∷
                              ⟨ (λ v → Value v → ⟦ Tren (Twkᵣ Tidᵣ) Tₓ ⟧ (subst-to-env* ρ*r []) → Set l₂) , (sym (fusion-Tsub-Tren Tₓ (Twkᵣ Tidᵣ) ρ*r)) ⟩∷
                              ⟨ Fr , sym eq₂r ⟩∷
                              [])
                             (𝓥⟦ Tₓ ⟧ ρ) ⟩
          subst Fr (sym eq₂r)
            (subst (λ v → Value v → ⟦ Tren (Twkᵣ Tidᵣ) Tₓ ⟧ (subst-to-env* ρ*r []) → Set l₂) (sym (fusion-Tsub-Tren Tₓ (Twkᵣ Tidᵣ) ρ*r))
             (subst (λ zz → Value (Tsub (Twkᵣ Tidᵣ ∘ᵣₛ ρ*r) Tₓ) → zz → Set l₂) (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ))
              (𝓥⟦ Tₓ ⟧ ρ)))
        ≡˘⟨ cong (subst Fr (sym eq₂r))
           (subst₂-subst-subst (λ vv zz → Value vv → zz → Set l₂)
                               (sym (fusion-Tsub-Tren Tₓ (Twkᵣ Tidᵣ) ρ*r))
                               (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ))
                               (𝓥⟦ Tₓ ⟧ ρ)) ⟩
          subst Fr (sym eq₂r)
            (subst₂ (λ vv zz → Value vv → zz → Set l₂)
             (sym (fusion-Tsub-Tren Tₓ (Twkᵣ Tidᵣ) ρ*r))
             (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ))
             (𝓥⟦ Tₓ ⟧ ρ))
        ≡⟨ cong (subst Fr (sym eq₂r))
           (cong (subst₂ (λ vv zz → Value vv → zz → Set l₂)
             (sym (fusion-Tsub-Tren Tₓ (Twkᵣ Tidᵣ) ρ*r))
             (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ)))
             (dcongωl (𝓥⟦ Tₓ ⟧) refl)) ⟩
          subst Fr (sym eq₂r)
            (subst₂ (λ vv zz → Value vv → zz → Set l₂)
             (sym (fusion-Tsub-Tren Tₓ (Twkᵣ Tidᵣ) ρ*r))
             (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ))
             (𝓥⟦ Tₓ ⟧ (Tren-act (Twkᵣ Tidᵣ) (REext ρ (T′ , R)))))
        ≡⟨ cong (subst Fr (sym eq₂r))
                (subst₂-swap′ (fusion-Tsub-Tren Tₓ (Twkᵣ Tidᵣ) ρ*r)
                              (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ)
                              _
                              _
                              eq-ren) ⟩
          subst Fr (sym eq₂r) (𝓥⟦ Twk (τ* l₂ x) ⟧ (REext ρ (T′ , R)))
        ∎ in
  begin
    Tsub-act τ* ρ l₂ x
  ≡⟨ refl ⟩
    Tsub ρ* Tₓ , subst F (sym eq₂) (𝓥⟦ Tₓ ⟧ ρ)
  ≡⟨ dcong₂ _,_ eq-1 eq-2 ⟩
    Tsub ρ*r Tₓr , subst Fr (sym eq₂r) (𝓥⟦ Tₓr ⟧ (REext ρ (T′ , R)))
  ≡⟨ refl ⟩
    Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)) l₂ (there x)
  ∎

Tsub-act-REext : (ρ : RelEnv Δ₂) (τ* : TSub Δ₁ Δ₂) (T′ : Type [] l) (R : REL T′)
  → (REext (Tsub-act τ* ρ) (T′ , R)) ≡ω Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R))
Tsub-act-REext ρ τ* T′ R = relenv-ext (Tsub-act-REext-ext ρ τ* T′ R)


-- holds definitionally
subst←RE-sub : ∀ (ρ : RelEnv Δ₂) (τ* : TSub Δ₁ Δ₂)
  → (l′ : Level) (x : l′ ∈ Δ₁) → subst←RE (Tsub-act τ* ρ) l′ x ≡ (τ* ∘ₛₛ subst←RE ρ) l′ x
subst←RE-sub ρ τ* l′ x = refl

-- logical relation is compatible with type substitution

--! LRVsubType
LRVsub : ∀ {Δ₁}{Δ₂}{l}
  → (T : Type Δ₁ l)
  → (ρ : RelEnv Δ₂)
  → (τ* : TSub Δ₁ Δ₂)
  → let ρ* = subst←RE ρ
  in (v : Value (Tsub (subst←RE (Tsub-act τ* ρ)) T))
  → (z : ⟦ T ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
  → 𝓥⟦ T ⟧ (Tsub-act τ* ρ) v z
  ≡ 𝓥⟦ Tsub τ* T ⟧ ρ
       (subst Value (sym (fusion-Tsub-Tsub T τ* (subst←RE ρ))) v)
       (subst id (sym (begin
                        ⟦ Tsub τ* T ⟧ (subst-to-env* (subst←RE ρ) [])
                      ≡⟨ subst-preserves τ* T ⟩
                        ⟦ T ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) []))
                      ≡⟨ congωl ⟦ T ⟧ (subst-to-env*-comp τ* (subst←RE ρ) []) ⟩
                        ⟦ T ⟧ (subst-to-env* (τ* ∘ₛₛ subst←RE ρ) [])
                      ≡⟨⟩
                        ⟦ T ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])
                      ∎)) z)

LRVsub (` α) ρ τ* v z =
  let T₂ = τ* _ α in
  let ρ* = subst←RE ρ in
  begin
    𝓥⟦ ` α ⟧ (Tsub-act τ* ρ) v z
  ≡⟨ refl ⟩
    proj₂ (Tsub-act τ* ρ _ α) v (subst id (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) []) z)
  ≡⟨ refl ⟩
    subst (λ ⟦x⟧ → Value (Tsub ρ* T₂) → ⟦x⟧ → Set _)
      (sym (subst-preserves (subst←RE ρ) T₂))
      (𝓥⟦ T₂ ⟧ ρ)
      v
      (subst id (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) []) z)
  ≡⟨ cong (λ ∎ → ∎ v (subst id (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) []) z))
    (eta-subst (λ v z → 𝓥⟦ T₂ ⟧ ρ v z) (sym (subst-preserves (subst←RE ρ) T₂)) ) ⟩
    subst (λ Z → Z → Set _) (sym (subst-preserves ρ* T₂))
      (λ z₁ → 𝓥⟦ T₂ ⟧ ρ v z₁)
      (subst id
       (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) []) z)
  ≡⟨ cong (λ ∎ → ∎ (subst id (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) []) z))
    (sym (app-subst (λ z₁ → 𝓥⟦ T₂ ⟧ ρ v z₁) (sym (subst-preserves ρ* T₂)))) ⟩
    𝓥⟦ T₂ ⟧ ρ v
      (subst id (sym (sym (subst-preserves ρ* T₂)))
       (subst id
        (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) []) z))
  ≡⟨ cong (𝓥⟦ T₂ ⟧ ρ v)
    (subst-subst {P = id} (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) [])
                           {(sym (sym (subst-preserves ρ* T₂)))}
                           {z}) ⟩
    𝓥⟦ T₂ ⟧ ρ v
      (subst id
       (trans (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) [])
        (sym (sym (subst-preserves ρ* T₂))))
       z)
  ≡⟨ cong (𝓥⟦ T₂ ⟧ ρ v)
    (subst-irrelevant {F = id}
                      (trans (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) []) (sym (sym (subst-preserves ρ* T₂))))
                      (sym
        (step-≡ (⟦ T₂ ⟧ (subst-to-env* (subst←RE ρ) []))
         (step-≡
          (apply-env (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])) α)
          (apply-env (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) α ∎)
          (congωl (λ η → apply-env η α)
           (subst-to-env*-comp τ* (subst←RE ρ) [])))
         (sym (subst-var-preserves α τ* (subst-to-env* (subst←RE ρ) [])))))
         z) ⟩
    𝓥⟦ T₂ ⟧ ρ v
      (subst id
       (sym
        (step-≡ (⟦ T₂ ⟧ (subst-to-env* (subst←RE ρ) []))
         (step-≡
          (apply-env (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])) α)
          (apply-env (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) α ∎)
          (congωl (λ η → apply-env η α)
           (subst-to-env*-comp τ* (subst←RE ρ) [])))
         (sym (subst-var-preserves α τ* (subst-to-env* (subst←RE ρ) [])))))
       z)
  ≡⟨ refl ⟩
    𝓥⟦ Tsub τ* (` α) ⟧ ρ
      (subst Value (sym (fusion-Tsub-Tsub (` α) τ* (subst←RE ρ))) v)
      (subst id
       (sym
        (step-≡ (⟦ Tsub τ* (` α) ⟧ (subst-to-env* (subst←RE ρ) []))
         (step-≡
          (⟦ ` α ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])))
          (⟦ ` α ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
          (congωl ⟦ ` α ⟧ (subst-to-env*-comp τ* (subst←RE ρ) [])))
         (subst-preserves τ* (` α))))
       z)
  ∎
LRVsub (T₁ ⇒ T₂) ρ τ* v z =
  let η = subst-to-env* (subst←RE ρ) [] in
  let ρ* = subst←RE ρ in
  let eq-T : ∀ {l} (T : Type _ l) → Tsub (subst←RE (Tsub-act τ* ρ)) T ≡ Tsub ρ* (Tsub τ* T)
      eq-T T =
        begin
          Tsub (subst←RE (Tsub-act τ* ρ)) T
        ≡⟨ refl ⟩
          Tsub (τ* ∘ₛₛ ρ*) T
        ≡˘⟨ fusion-Tsub-Tsub T τ* (subst←RE ρ) ⟩
          Tsub ρ* (Tsub τ* T)
        ∎

      fₗ = (λ e →
         (exp v ≡ (ƛ e)) ∧
         ((w : Value (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
          𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ) w z₁ →
          ∃-syntax
          (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁))))
  in
  begin
    𝓥⟦ T₁ ⇒ T₂ ⟧ (Tsub-act τ* ρ) v z
  ≡⟨ refl ⟩
    Σ (Expr [] (Tsub (subst←RE (Tsub-act τ* ρ)) T₁ ◁ ∅) (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
      fₗ
  ≡⟨ sigma-subst fₗ (cong₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) (eq-T T₁) (eq-T T₂)) ⟩
    Σ (Expr [] (Tsub ρ* (Tsub τ* T₁) ◁ ∅) (Tsub ρ* (Tsub τ* T₂)))
      (λ e →
         (exp v ≡
          (ƛ
           subst id
           (sym
            (cong₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
             (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
              (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
               (fusion-Tsub-Tsub T₁ τ* ρ*))
              refl)
             (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
              (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
               (fusion-Tsub-Tsub T₂ τ* ρ*))
              refl)))
           e))
         ∧
         ((w : Value (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
          𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ) w z₁ →
          ∃-syntax
          (λ v₁ →
             (subst id
              (sym
               (cong₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
                (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                 (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                  (fusion-Tsub-Tsub T₁ τ* ρ*))
                 refl)
                (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                 (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                  (fusion-Tsub-Tsub T₂ τ* ρ*))
                 refl)))
              e
              [ exp w ]E)
             ⇓ v₁
             ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁))))
  ≡⟨ cong (Σ (Expr [] (Tsub ρ* (Tsub τ* T₁) ◁ ∅) (Tsub ρ* (Tsub τ* T₂))))
      (fun-ext (λ e →
        cong₂ _∧_
      --------------------------------------------------
        (begin
          exp v ≡
            (ƛ
             subst id
             (sym
              (cong₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                 (fusion-Tsub-Tsub T₁ τ* ρ*))
                refl)
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                 (fusion-Tsub-Tsub T₂ τ* ρ*))
                refl)))
             e)
        ≡⟨ cong (exp v ≡_)
          (cong (λ ∎ → (ƛ subst id ∎ e))
            (sym-cong₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                 (fusion-Tsub-Tsub T₁ τ* ρ*))
                refl)
                (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                 (fusion-Tsub-Tsub T₂ τ* ρ*))
                refl))) ⟩
          exp v ≡
            (ƛ
             subst id
             (cong₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
              (sym
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                 (fusion-Tsub-Tsub T₁ τ* ρ*))
                refl))
              (sym
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                 (fusion-Tsub-Tsub T₂ τ* ρ*))
                refl)))
             e)
        ≡˘⟨ cong (exp v ≡_)
           (cong ƛ_
             (subst₂-∘ id (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
             (sym
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                 (fusion-Tsub-Tsub T₁ τ* ρ*))
                refl))
              (sym
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                 (fusion-Tsub-Tsub T₂ τ* ρ*))
                refl)) e)) ⟩
          exp v ≡
            (ƛ
             subst₂ (id Function.∘₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄))
             (sym
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                (fusion-Tsub-Tsub T₁ τ* ρ*))
               refl))
             (sym
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                (fusion-Tsub-Tsub T₂ τ* ρ*))
               refl))
             e)
        ≡˘⟨ cong (exp v ≡_)
            (subst-split-ƛ (cong₂ _⇒_ (sym (eq-T T₁)) (sym (eq-T T₂)))
            (sym
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                (fusion-Tsub-Tsub T₁ τ* ρ*))
               refl))
             (sym
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                (fusion-Tsub-Tsub T₂ τ* ρ*))
               refl)) e ) ⟩
          exp v ≡ (subst CExpr (cong₂ _⇒_ (sym (eq-T T₁)) (sym (eq-T T₂))) (ƛ e))
        ≡˘⟨ cong (exp v ≡_)
          (cong (λ ∎ → subst CExpr ∎ (ƛ e))
          (sym-cong₂ _⇒_
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                (fusion-Tsub-Tsub T₁ τ* ρ*))
               refl)
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                (fusion-Tsub-Tsub T₂ τ* ρ*))
               refl))) ⟩
          exp v ≡
            subst CExpr
            (sym
             (cong₂ _⇒_
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                (fusion-Tsub-Tsub T₁ τ* ρ*))
               refl)
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                (fusion-Tsub-Tsub T₂ τ* ρ*))
               refl)))
            (ƛ e)
        ≡˘⟨ subst-swap-eq {F = CExpr} (cong₂ _⇒_ (eq-T T₁) (eq-T T₂)) (exp v) (ƛ e) ⟩
          subst CExpr (cong₂ _⇒_ (eq-T T₁) (eq-T T₂)) (exp v) ≡ (ƛ e)
        ≡˘⟨ cong (_≡ (ƛ e))
            (dist-subst' {F = Value} {G = CExpr} id exp
                          (sym (cong₂ _⇒_ (fusion-Tsub-Tsub T₁ τ* ρ*) (fusion-Tsub-Tsub T₂ τ* ρ*)))
                          (cong₂ _⇒_ (eq-T T₁) (eq-T T₂))
                          v) ⟩
          exp (subst Value (sym (cong₂ _⇒_ (fusion-Tsub-Tsub T₁ τ* ρ*) (fusion-Tsub-Tsub T₂ τ* ρ*))) v)
            ≡ (ƛ e)
        ∎)
      --------------------------------------------------
        (begin
          ((w : Value (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))
            (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
            𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ) w z₁ →
            ∃-syntax
            (λ v₁ →
               (subst id
                (sym
                 (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                  (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                  (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                e
                [ exp w ]E)
               ⇓ v₁
               ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁)))
        ≡⟨ pi-subst
             (λ w →
                (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
                𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ) w z₁ →
                ∃-syntax
                (λ v₁ →
                   (subst id
                    (sym
                     (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                       (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                       (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                    e
                    [ exp w ]E)
                   ⇓ v₁
                   ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁)))
             (cong Value (sym (eq-T T₁))) ⟩
          ((w : Value (Tsub ρ* (Tsub τ* T₁))) →
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
            𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
            (subst id
             (cong Value
              (sym
               (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)))
             w)
            z₁ →
            ∃-syntax
            (λ v₁ →
               (subst id
                (sym
                 (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                  (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                   (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                    (fusion-Tsub-Tsub T₁ τ* ρ*))
                   refl)
                  (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                   (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                    (fusion-Tsub-Tsub T₂ τ* ρ*))
                   refl)))
                e
                [
                exp
                (subst id
                 (cong Value
                  (sym
                   (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                    (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                     (fusion-Tsub-Tsub T₁ τ* ρ*))
                    refl)))
                 w)
                ]E)
               ⇓ v₁
               ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁)))
        ≡⟨ dep-ext (λ w → 
           begin
             ((z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
               𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
               (subst id
                (cong Value
                 (sym
                  (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                   (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                    (fusion-Tsub-Tsub T₁ τ* ρ*))
                   refl)))
                w)
               z₁ →
               ∃-syntax
               (λ v₁ →
                  (subst id
                   (sym
                    (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                     (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                      (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                       (fusion-Tsub-Tsub T₁ τ* ρ*))
                      refl)
                     (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                      (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                       (fusion-Tsub-Tsub T₂ τ* ρ*))
                      refl)))
                   e
                   [
                   exp
                   (subst id
                    (cong Value
                     (sym
                      (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                       (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                        (fusion-Tsub-Tsub T₁ τ* ρ*))
                       refl)))
                    w)
                   ]E)
                  ⇓ v₁
                  ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁)))
           ≡⟨ pi-subst
                (λ z₁ →
                   𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
                   (subst id
                    (cong Value
                     (sym
                      (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                       (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                        (fusion-Tsub-Tsub T₁ τ* ρ*))
                       refl)))
                    w)
                   z₁ →
                   ∃-syntax
                   (λ v₁ →
                      (subst id
                       (sym
                        (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                         (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                          (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                           (fusion-Tsub-Tsub T₁ τ* ρ*))
                          refl)
                         (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                          (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                           (fusion-Tsub-Tsub T₂ τ* ρ*))
                          refl)))
                       e
                       [
                       exp
                       (subst id
                        (cong Value
                         (sym
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                            (fusion-Tsub-Tsub T₁ τ* ρ*))
                           refl)))
                        w)
                       ]E)
                      ⇓ v₁
                      ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁)))
                (trans (subst-preserves {η₂ = η} τ* T₁)
                       (sym (congωl (⟦ T₁ ⟧)
                            (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                                    (symω (subst-to-env*-comp τ* ρ* [])))))) ⟩
             ((z₁ : ⟦ Tsub τ* T₁ ⟧ η) → 𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
                                          (subst id
                                           (cong Value
                                            (sym
                                             (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                                              (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                                               (fusion-Tsub-Tsub T₁ τ* ρ*))
                                              refl)))
                                           w)
                                          (subst id (trans (subst-preserves τ* T₁) _) z₁) →
                                          ∃-syntax
                                          (λ v₁ →
                                             (subst id
                                              (sym
                                               (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                                                (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                                                 (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                                                  (fusion-Tsub-Tsub T₁ τ* ρ*))
                                                 refl)
                                                (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                                                 (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                                                  (fusion-Tsub-Tsub T₂ τ* ρ*))
                                                 refl)))
                                              e
                                              [
                                              exp
                                              (subst id
                                               (cong Value
                                                (sym
                                                 (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                                                  (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                                                   (fusion-Tsub-Tsub T₁ τ* ρ*))
                                                  refl)))
                                               w)
                                              ]E)
                                             ⇓ v₁
                                             ∧
                                             𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁
                                             (z (subst id (trans (subst-preserves τ* T₁) _) z₁))))
           ≡⟨ dep-ext (λ z₁ →
              begin
                (𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
                  (subst id
                   (cong Value
                    (sym
                     (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                      (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                       (fusion-Tsub-Tsub T₁ τ* ρ*))
                      refl)))
                   w)
                  (subst id
                   (trans (subst-preserves τ* T₁)
                    (sym
                     (congωl ⟦ T₁ ⟧
                      (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                       (symω (subst-to-env*-comp τ* ρ* []))))))
                   z₁) →
                  ∃-syntax
                  (λ v₁ →
                     (subst id
                      (sym
                       (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                        (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                         (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                          (fusion-Tsub-Tsub T₁ τ* ρ*))
                         refl)
                        (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                         (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                          (fusion-Tsub-Tsub T₂ τ* ρ*))
                         refl)))
                      e
                      [
                      exp
                      (subst id
                       (cong Value
                        (sym
                         (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                          (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                           (fusion-Tsub-Tsub T₁ τ* ρ*))
                          refl)))
                       w)
                      ]E)
                     ⇓ v₁
                     ∧
                     𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁
                     (z
                      (subst id
                       (trans (subst-preserves τ* T₁)
                        (sym
                         (congωl ⟦ T₁ ⟧
                          (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                           (symω (subst-to-env*-comp τ* ρ* []))))))
                       z₁))))
              ≡⟨ cong₂ (λ X Y → X → Y)
        --------------------------------------------------
                (begin
                  𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
                    (subst id
                     (cong Value
                      (sym
                       (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                        (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                         (fusion-Tsub-Tsub T₁ τ* ρ*))
                        refl)))
                     w)
                    (subst id
                     (trans (subst-preserves τ* T₁)
                      (sym
                       (congωl ⟦ T₁ ⟧
                        (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                         (symω (subst-to-env*-comp τ* ρ* []))))))
                     z₁)
                ≡⟨ LRVsub T₁ ρ τ*
                            (subst id
                     (cong Value
                      (sym
                       (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                        (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                         (fusion-Tsub-Tsub T₁ τ* ρ*))
                        refl)))
                     w)
                     (subst id
                     (trans (subst-preserves τ* T₁)
                      (sym
                       (congωl ⟦ T₁ ⟧
                        (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                         (symω (subst-to-env*-comp τ* ρ* []))))))
                     z₁) ⟩
                  𝓥⟦ Tsub τ* T₁ ⟧ ρ
                    (subst Value (sym (fusion-Tsub-Tsub T₁ τ* ρ*))
                     (subst id
                      (cong Value
                       (sym
                        (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                         (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                          (fusion-Tsub-Tsub T₁ τ* ρ*))
                         refl)))
                      w))
                    (subst id
                     (sym
                      (step-≡ (⟦ Tsub τ* T₁ ⟧ η)
                       (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η))
                        (⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
                        (congωl ⟦ T₁ ⟧ (subst-to-env*-comp τ* ρ* [])))
                       (subst-preserves τ* T₁)))
                     (subst id
                      (trans (subst-preserves τ* T₁)
                       (sym
                        (congωl ⟦ T₁ ⟧
                         (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                          (symω (subst-to-env*-comp τ* ρ* []))))))
                      z₁))
                ≡⟨ cong₂ (𝓥⟦ Tsub τ* T₁ ⟧ ρ)
                   (subst*-irrelevant
                     (⟨ id , (cong Value (sym
                                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                                              (fusion-Tsub-Tsub T₁ τ* ρ*))
                                             refl))) ⟩∷
                     ⟨ Value , (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) ⟩∷
                     []) [] w)
                   (subst*-irrelevant
                     (⟨ id , (trans (subst-preserves τ* T₁)
                                    (sym
                                     (congωl ⟦ T₁ ⟧
                                      (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                                       (symω (subst-to-env*-comp τ* ρ* [])))))) ⟩∷
                      ⟨ id , (sym
                               (step-≡ (⟦ Tsub τ* T₁ ⟧ η)
                                (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η))
                                 (⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
                                 (congωl ⟦ T₁ ⟧ (subst-to-env*-comp τ* ρ* [])))
                                (subst-preserves τ* T₁))) ⟩∷
                      [])
                     []
                     z₁) ⟩
                  𝓥⟦ Tsub τ* T₁ ⟧ ρ w z₁
                ∎)
        --------------------------------------------------
                (begin
                  Σ (Value (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                    (λ v₁ →
                       (subst id
                        (sym
                         (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                            (fusion-Tsub-Tsub T₁ τ* ρ*))
                           refl)
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                            (fusion-Tsub-Tsub T₂ τ* ρ*))
                           refl)))
                        e
                        [
                        exp
                        (subst id
                         (cong Value
                          (sym
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                             (fusion-Tsub-Tsub T₁ τ* ρ*))
                            refl)))
                         w)
                        ]E)
                       ⇓ v₁
                       ∧
                       𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁
                       (z
                        (subst id
                         (trans (subst-preserves τ* T₁)
                          (sym
                           (congωl ⟦ T₁ ⟧
                            (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                             (symω (subst-to-env*-comp τ* ρ* []))))))
                         z₁)))
                ≡⟨ sigma-subst (λ v₁ →
                       (subst id
                        (sym
                         (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                            (fusion-Tsub-Tsub T₁ τ* ρ*))
                           refl)
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                            (fusion-Tsub-Tsub T₂ τ* ρ*))
                           refl)))
                        e
                        [
                        exp
                        (subst id
                         (cong Value
                          (sym
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                             (fusion-Tsub-Tsub T₁ τ* ρ*))
                            refl)))
                         w)
                        ]E)
                       ⇓ v₁
                       ∧
                       𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁
                       (z
                        (subst id
                         (trans (subst-preserves τ* T₁)
                          (sym
                           (congωl ⟦ T₁ ⟧
                            (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                             (symω (subst-to-env*-comp τ* ρ* []))))))
                         z₁)))
                         (cong Value (eq-T T₂)) ⟩
                  Σ (Value (Tsub ρ* (Tsub τ* T₂)))
                    (λ v₁ →
                       (subst id
                        (sym
                         (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                            (fusion-Tsub-Tsub T₁ τ* ρ*))
                           refl)
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                            (fusion-Tsub-Tsub T₂ τ* ρ*))
                           refl)))
                        e
                        [
                        exp
                        (subst id
                         (cong Value
                          (sym
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                             (fusion-Tsub-Tsub T₁ τ* ρ*))
                            refl)))
                         w)
                        ]E)
                       ⇓
                       subst id
                       (sym
                        (cong Value
                         (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                          (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                           (fusion-Tsub-Tsub T₂ τ* ρ*))
                          refl)))
                       v₁
                       ∧
                       𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ)
                       (subst id
                        (sym
                         (cong Value
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                            (fusion-Tsub-Tsub T₂ τ* ρ*))
                           refl)))
                        v₁)
                       (z
                        (subst id
                         (trans (subst-preserves τ* T₁)
                          (sym
                           (congωl ⟦ T₁ ⟧
                            (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                             (symω (subst-to-env*-comp τ* ρ* []))))))
                         z₁)))
                ≡⟨ cong (Σ (Value (Tsub ρ* (Tsub τ* T₂))))
                  (fun-ext (λ v₁ →
                    cong₂ _∧_
                --------------------------------------------------
                    (begin
                      (subst id
                         (sym
                          (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                             (fusion-Tsub-Tsub T₁ τ* ρ*))
                            refl)
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                             (fusion-Tsub-Tsub T₂ τ* ρ*))
                            refl)))
                         e
                         [
                         exp
                         (subst id
                          (cong Value
                           (sym
                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                              (fusion-Tsub-Tsub T₁ τ* ρ*))
                             refl)))
                          w)
                         ]E)
                        ⇓
                        subst id
                        (sym
                         (cong Value
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                            (fusion-Tsub-Tsub T₂ τ* ρ*))
                           refl)))
                        v₁
                    ≡⟨ cong (_ ⇓_)
                       (cong (λ ∎ → subst id ∎ v₁)
                         (sym-cong {f = Value} (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) (Tsub ρ* (Tsub τ* T₂) ∎)))) ⟩
                      subst (Expr [] ∅) (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst (Expr [] ∅)
                           (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)))
                           (exp
                            (subst id
                             (cong Value
                              (sym
                               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                                 (fusion-Tsub-Tsub T₁ τ* ρ*))
                                refl)))
                             w))))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                              (fusion-Tsub-Tsub T₁ τ* ρ*))
                             refl)
                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                              (fusion-Tsub-Tsub T₂ τ* ρ*))
                             refl)))
                          e))
                        ⇓
                        subst id
                        (cong Value
                         (sym
                          (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) (Tsub ρ* (Tsub τ* T₂) ∎))))
                        v₁
                    ≡˘⟨ cong (_ ⇓_) (subst-∘ {P = id} {f = Value}
                                              (sym (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) (Tsub ρ* (Tsub τ* T₂) ∎))) {v₁}) ⟩
                      subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst CExpr
                           (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)))
                           (exp
                            (subst id
                             (cong Value
                              (sym
                               (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)))
                             w))))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                            (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                          e))
                        ⇓
                        subst Value (sym (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)) v₁
                    ≡⟨ cong (_ ⇓_) (cong (λ ∎ → subst Value ∎ v₁) (sym-trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)) ⟩
                      subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst CExpr (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)))
                           (exp
                            (subst id
                             (cong Value (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)))
                             w))))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                            (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                          e)) ⇓
                        subst Value (sym (sym (fusion-Tsub-Tsub T₂ τ* ρ*))) v₁
                    ≡⟨ cong (λ H → subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst CExpr (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)))
                           (exp H)))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                            (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                          e)) ⇓
                        subst Value (sym (sym (fusion-Tsub-Tsub T₂ τ* ρ*))) v₁)
                        (sym (subst-∘ {P = id} {f = Value} (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)) {w} )) ⟩
                      subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst CExpr (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)))
                           (exp
                            (subst Value (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl))
                             w))))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                            (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                          e))
                        ⇓ subst Value (sym (sym (fusion-Tsub-Tsub T₂ τ* ρ*))) v₁
                    ≡⟨ cong (λ H → subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst CExpr (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)))
                           H))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                            (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                          e)) ⇓
                        subst Value (sym (sym (fusion-Tsub-Tsub T₂ τ* ρ*))) v₁)
                        ( dist-subst' {F = Value} {G = CExpr}
                                       id
                                       exp
                                       (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl))
                                       (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl))
                                       w)
                    ⟩
                      subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst CExpr (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)))
                           (subst CExpr (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl))
                            (exp
                             w))))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                            (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                          e)) ⇓
                        subst Value (sym (sym (fusion-Tsub-Tsub T₂ τ* ρ*))) v₁ 
                    ≡⟨ cong (λ H → subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          H)
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                            (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                          e)) ⇓
                        subst Value (sym (sym (fusion-Tsub-Tsub T₂ τ* ρ*))) v₁)
                        (subst-subst {P = CExpr}
                                      (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl))
                                      {(sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)))}
                                      {exp w})
                    ⟩
                      subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst CExpr
                           (trans (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl))
                            (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                           (exp w)))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                            (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                          e))
                        ⇓ subst Value (sym (sym (fusion-Tsub-Tsub T₂ τ* ρ*))) v₁
                    ≡⟨ cong (λ H → subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst CExpr
                           (trans (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl))
                            (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                           (exp w)))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                            (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                          e))
                        ⇓ subst Value H v₁) (sym-sym (fusion-Tsub-Tsub T₂ τ* ρ*)) ⟩
                      subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst CExpr
                           (trans (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl))
                            (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                           (exp w)))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                            (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                          e))
                        ⇓ subst Value (fusion-Tsub-Tsub T₂ τ* ρ*) v₁
                    ≡⟨ cong (_⇓ subst Value (fusion-Tsub-Tsub T₂ τ* ρ*) v₁)
                       (begin
                         subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                           (Esub Tidₛ
                            (Eextₛ Tidₛ Eidₛ
                             (subst CExpr
                              (trans (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl))
                               (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                              (exp w)))
                            (subst id
                             (sym
                              (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                               (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                               (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                             e))
                       ≡⟨ cong (λ H → subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                           (Esub Tidₛ
                            (Eextₛ Tidₛ Eidₛ
                             (subst CExpr
                              (trans H
                               (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                              (exp w)))
                            (subst id
                             (sym
                              (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                               (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                               (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                             e)))
                             (trans (sym-trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl) 
                                    (sym-sym (fusion-Tsub-Tsub T₁ τ* ρ*)))
                       ⟩
                         subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                           (Esub Tidₛ
                            (Eextₛ Tidₛ Eidₛ
                             (subst CExpr
                              (trans (fusion-Tsub-Tsub T₁ τ* ρ*)
                               (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                              (exp w)))
                            (subst id
                             (sym
                              (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                               (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                               (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                             e))
                       ≡⟨ cong (λ H → subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                           (Esub Tidₛ
                            (Eextₛ Tidₛ Eidₛ
                             (subst CExpr
                              (trans (fusion-Tsub-Tsub T₁ τ* ρ*)
                               (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                              (exp w)))
                            (subst id H e)))
                            (sym-cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                                        (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl)
                                        (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)) ⟩
                         subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                           (Esub Tidₛ
                            (Eextₛ Tidₛ Eidₛ
                             (subst CExpr
                              (trans (fusion-Tsub-Tsub T₁ τ* ρ*)
                               (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                              (exp w)))
                            (subst id
                             (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                              (sym (trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl))
                              (sym (trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl)))
                             e))
                       ≡⟨ cong₂ (λ H₁ H₂ → subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                           (Esub Tidₛ
                            (Eextₛ Tidₛ Eidₛ
                             (subst CExpr
                              (trans (fusion-Tsub-Tsub T₁ τ* ρ*)
                               (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                              (exp w)))
                            (subst id
                             (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                              H₁ H₂)
                             e))) (trans (sym-trans (sym (fusion-Tsub-Tsub T₁ τ* ρ*)) refl) 
                                    (sym-sym (fusion-Tsub-Tsub T₁ τ* ρ*)))
                                  (trans (sym-trans (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) refl) 
                                    (sym-sym (fusion-Tsub-Tsub T₂ τ* ρ*))) ⟩
                         subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                           (Esub Tidₛ
                            (Eextₛ Tidₛ Eidₛ
                             (subst CExpr
                              (trans (fusion-Tsub-Tsub T₁ τ* ρ*)
                               (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                              (exp w)))
                            (subst id
                             (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                               (fusion-Tsub-Tsub T₁ τ* ρ*)
                              (fusion-Tsub-Tsub T₂ τ* ρ*))
                             e))
                       ≡⟨ cong (λ H → subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                           (Esub Tidₛ
                            (Eextₛ Tidₛ Eidₛ
                             (subst CExpr
                              (trans (fusion-Tsub-Tsub T₁ τ* ρ*)
                               (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                              (exp w)))
                            H))
                            (sym (subst₂-∘ id (λ T₃ → Expr [] (T₃ ◁ ∅)) (fusion-Tsub-Tsub T₁ τ* ρ*) (fusion-Tsub-Tsub T₂ τ* ρ*) e))
                        ⟩
                         subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                           (Esub Tidₛ
                            (Eextₛ Tidₛ Eidₛ
                             (subst CExpr
                              (trans (fusion-Tsub-Tsub T₁ τ* ρ*)
                               (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))))
                              (exp w)))
                            (subst₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                             (fusion-Tsub-Tsub T₁ τ* ρ*) (fusion-Tsub-Tsub T₂ τ* ρ*) e))
                       ≡⟨ cong (subst CExpr (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)))
                         (cong (λ H → Esub Tidₛ H
                                  (subst₂ (λ T₃ → Expr [] (T₃ ◁ ∅)) (fusion-Tsub-Tsub T₁ τ* ρ*) (fusion-Tsub-Tsub T₂ τ* ρ*) e))
                               (sym (cong (Eextₛ Tidₛ Eidₛ)
                                    (subst-subst {P = CExpr} (fusion-Tsub-Tsub T₁ τ* ρ*)
                                                             {(sym (TidₛT≡T (Tsub (τ* ∘ₛₛ ρ*) T₁)))}
                                                             {exp w})))) ⟩
                         ((subst₂ (λ T₃ → Expr [] (T₃ ◁ ∅)) (fusion-Tsub-Tsub T₁ τ* ρ*) (fusion-Tsub-Tsub T₂ τ* ρ*) e) [ (subst CExpr (fusion-Tsub-Tsub T₁ τ* ρ*) (exp w)) ]E)
                       ≡⟨ subst-split-[]E″ e (exp w) (fusion-Tsub-Tsub T₁ τ* ρ*) (fusion-Tsub-Tsub T₂ τ* ρ*) ⟩
                         subst CExpr (fusion-Tsub-Tsub T₂ τ* ρ*) (e [ exp w ]E)
                       ∎)
                     ⟩
                        subst CExpr (fusion-Tsub-Tsub T₂ τ* ρ*) (e [ exp w ]E) 
                        ⇓ subst Value (fusion-Tsub-Tsub T₂ τ* ρ*) v₁ 
                    ≡⟨ sym (subst-split-eq-⇓₂ (fusion-Tsub-Tsub T₂ τ* ρ*)) ⟩
                      (e [ exp w ]E) ⇓ v₁
                    ∎)
                --------------------------------------------------
                    (begin
                      𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ)
                        (subst id
                         (sym
                          (cong Value
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                             (fusion-Tsub-Tsub T₂ τ* ρ*))
                            refl)))
                         v₁)
                        (z
                         (subst id
                          (trans (subst-preserves τ* T₁)
                           (sym
                            (congωl ⟦ T₁ ⟧
                             (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                              (symω (subst-to-env*-comp τ* ρ* []))))))
                          z₁))
                    ≡⟨ LRVsub T₂ ρ τ*
                                (subst id
                         (sym
                          (cong Value
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                             (fusion-Tsub-Tsub T₂ τ* ρ*))
                            refl)))
                         v₁)
                        (z
                         (subst id
                          (trans (subst-preserves τ* T₁)
                           (sym
                            (congωl ⟦ T₁ ⟧
                             (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                              (symω (subst-to-env*-comp τ* ρ* []))))))
                          z₁)) ⟩
                      𝓥⟦ Tsub τ* T₂ ⟧ ρ
                        (subst Value (sym (fusion-Tsub-Tsub T₂ τ* ρ*))
                         (subst id
                          (sym
                           (cong Value
                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                              (fusion-Tsub-Tsub T₂ τ* ρ*))
                             refl)))
                          v₁))
                        (subst id
                         (sym
                          (step-≡ (⟦ Tsub τ* T₂ ⟧ η)
                           (step-≡ (⟦ T₂ ⟧ (subst-to-env* τ* η))
                            (⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
                            (congωl ⟦ T₂ ⟧ (subst-to-env*-comp τ* ρ* [])))
                           (subst-preserves τ* T₂)))
                         (z
                          (subst id
                           (trans (subst-preserves τ* T₁)
                            (sym
                             (congωl ⟦ T₁ ⟧
                              (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                               (symω (subst-to-env*-comp τ* ρ* []))))))
                           z₁)))
                    ≡⟨ cong₂ (𝓥⟦ Tsub τ* T₂ ⟧ ρ)
                --------------------------------------------------
                      (subst*-irrelevant
                        (⟨ id , (sym
                            (cong Value
                             (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                              (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                               (fusion-Tsub-Tsub T₂ τ* ρ*))
                              refl))) ⟩∷
                         ⟨ Value , (sym (fusion-Tsub-Tsub T₂ τ* ρ*)) ⟩∷
                         [])
                        []
                        v₁)
                --------------------------------------------------
                      (begin
                        subst id
                          (sym
                           (step-≡ (⟦ Tsub τ* T₂ ⟧ η)
                            (step-≡ (⟦ T₂ ⟧ (subst-to-env* τ* η))
                             (⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
                             (congωl ⟦ T₂ ⟧ (subst-to-env*-comp τ* ρ* [])))
                            (subst-preserves τ* T₂)))
                          (z
                           (subst id
                            (trans (subst-preserves τ* T₁)
                             (sym
                              (congωl ⟦ T₁ ⟧
                               (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                                (symω (subst-to-env*-comp τ* ρ* []))))))
                            z₁))
                      ≡⟨ dist-subst z
                           (trans (subst-preserves τ* T₁)
                             (sym
                              (congωl ⟦ T₁ ⟧
                               (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                                (symω (subst-to-env*-comp τ* ρ* []))))))
                                (sym
                           (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                            (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                             ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                               ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                              ∎)
                             (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                              (subst-to-env*-comp τ* ρ* [])))
                            (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                             (subst-preserves τ* T₂))))
                           (sym
                            (step-≡ (⟦ Tsub τ* T₂ ⟧ η)
                             (step-≡ (⟦ T₂ ⟧ (subst-to-env* τ* η))
                              (⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
                              (congωl ⟦ T₂ ⟧ (subst-to-env*-comp τ* ρ* [])))
                             (subst-preserves τ* T₂)))
                           z₁    ⟩
                        (subst id
                          (sym
                           (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                            (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                             ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                               ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                              ∎)
                             (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                              (subst-to-env*-comp τ* ρ* [])))
                            (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                             (subst-preserves τ* T₂))))
                          z) z₁
                      ∎)
                --------------------------------------------------
                     ⟩
                      𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
                        (subst id
                         (sym
                          (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                           (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                            ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                              ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                             ∎)
                            (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                             (subst-to-env*-comp τ* ρ* [])))
                           (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                            (subst-preserves τ* T₂))))
                         z z₁)
                    ∎)
                --------------------------------------------------
                    )) ⟩
                  Σ (Value (Tsub ρ* (Tsub τ* T₂)))
                    (λ v₁ →
                       (e [ exp w ]E) ⇓ v₁ ∧
                       𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
                       (subst id
                        (sym
                         (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                          (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                           ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                             ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                            ∎)
                           (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                            (subst-to-env*-comp τ* ρ* [])))
                          (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                           (subst-preserves τ* T₂))))
                        z z₁))
                ∎)
        --------------------------------------------------
                ⟩
                (𝓥⟦ Tsub τ* T₁ ⟧ ρ w z₁ →
                  ∃-syntax
                  (λ v₁ →
                     (e [ exp w ]E) ⇓ v₁ ∧
                     𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
                     (subst id
                      (sym
                       (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                        (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                         ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                           ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                          ∎)
                         (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                          (subst-to-env*-comp τ* ρ* [])))
                        (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                         (subst-preserves τ* T₂))))
                      z z₁)))
              ∎) ⟩
             ((z₁ : ⟦ Tsub τ* T₁ ⟧ η) →
               𝓥⟦ Tsub τ* T₁ ⟧ ρ w z₁ →
               ∃-syntax
               (λ v₁ →
                  (e [ exp w ]E) ⇓ v₁ ∧
                  𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
                  (subst id
                   (sym
                    (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                     (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                      ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                        ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                       ∎)
                      (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                       (subst-to-env*-comp τ* ρ* [])))
                     (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                      (subst-preserves τ* T₂))))
                   z z₁)))
           ∎) ⟩
          ((w : Value (Tsub ρ* (Tsub τ* T₁))) (z₁ : ⟦ Tsub τ* T₁ ⟧ η) →
            𝓥⟦ Tsub τ* T₁ ⟧ ρ w z₁ →
            ∃-syntax
            (λ v₁ →
               (e [ exp w ]E) ⇓ v₁ ∧
               𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
               (subst id
                (sym
                 (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                  (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                   ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                     ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                    ∎)
                   (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                    (subst-to-env*-comp τ* ρ* [])))
                  (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                   (subst-preserves τ* T₂))))
                z z₁)))
        ∎)
      --------------------------------------------------
        )) ⟩
    Σ (Expr [] (Tsub ρ* (Tsub τ* T₁) ◁ ∅) (Tsub ρ* (Tsub τ* T₂)))
      (λ e →
         (exp (subst Value (sym (cong₂ _⇒_ (fusion-Tsub-Tsub T₁ τ* ρ*) (fusion-Tsub-Tsub T₂ τ* ρ*))) v) ≡ (ƛ e))
         ∧
         ((w : Value (Tsub ρ* (Tsub τ* T₁))) (z₁ : ⟦ Tsub τ* T₁ ⟧ η) →
          𝓥⟦ Tsub τ* T₁ ⟧ ρ w z₁ →
          ∃-syntax
          (λ v₁ →
             (e [ exp w ]E) ⇓ v₁ ∧
             𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
             (subst id
              (sym
               (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                 ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                   ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                  ∎)
                 (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                  (subst-to-env*-comp τ* ρ* [])))
                (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                 (subst-preserves τ* T₂))))
              z z₁))))
  ≡⟨ refl ⟩
    𝓥⟦ Tsub τ* (T₁ ⇒ T₂) ⟧ ρ
      (subst Value (sym (fusion-Tsub-Tsub (T₁ ⇒ T₂) τ* ρ*)) v)
      (subst id
       (sym
        (step-≡ (⟦ Tsub τ* (T₁ ⇒ T₂) ⟧ η)
         (step-≡
          (⟦ T₁ ⇒ T₂ ⟧ (subst-to-env* τ* η))
          (⟦ T₁ ⇒ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
          (congωl ⟦ T₁ ⇒ T₂ ⟧ (subst-to-env*-comp τ* ρ* [])))
         (subst-preserves τ* (T₁ ⇒ T₂))))
       z)
  ∎
LRVsub {Δ₁ = Δ₁} (`∀α_,_ {l′ = l′} l T) ρ τ* v z =
  let
    ρ* = subst←RE ρ
  in
  begin
    𝓥⟦ `∀α l , T ⟧ (Tsub-act τ* ρ) v z
  ≡⟨ refl ⟩
    Σ (Expr (l ∷ []) (l ◁* ∅) (Tsub (Tliftₛ (subst←RE (Tsub-act τ* ρ)) l) T))
      (λ e →
         (exp v ≡ (Λ l ⇒ e)) ∧
         ((T′ : Type [] l) (R : REL T′) →
          ∃-syntax
          (λ v₁ →
             (e [ T′ ]ET) ⇓ v₁ ∧
             𝓥⟦ T ⟧ (REext (Tsub-act τ* ρ) (T′ , R))
             (subst Value (lemma1 (Tsub-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ [])))))
  ≡⟨ sigma-subst (λ e →
         (exp v ≡ (Λ l ⇒ e)) ∧
         ((T′ : Type [] l) (R : REL T′) →
          ∃-syntax
          (λ v₁ →
             (e [ T′ ]ET) ⇓ v₁ ∧
             𝓥⟦ T ⟧ (REext (Tsub-act τ* ρ) (T′ , R))
             (subst Value (lemma1 (Tsub-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ [])))))
          (cong (Expr (l ∷ []) (l ◁* ∅))
          (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                 (sym (assoc-sub↑-sub↑ T τ* ρ*)))) ⟩
    Σ (Expr (l ∷ []) (l ◁* ∅) (Tsub (Tliftₛ (subst←RE ρ) l) (Tsub (Tliftₛ τ* l) T)))
      (λ e →
          (exp v ≡
           (Λ l ⇒
            subst id
            (sym
             (cong (Expr (l ∷ []) (l ◁* ∅))
              (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
               (sym (assoc-sub↑-sub↑ T τ* ρ*)))))
            e))
          ∧
          ((T′ : Type [] l) (R : REL T′) →
           ∃-syntax
           (λ v₁ →
              (subst id
               (sym
                (cong (Expr (l ∷ []) (l ◁* ∅))
                 (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                  (sym (assoc-sub↑-sub↑ T τ* ρ*)))))
               e
               [ T′ ]ET)
              ⇓ v₁
              ∧
              𝓥⟦ T ⟧ (REext (Tsub-act τ* ρ) (T′ , R))
              (subst Value (lemma1 (Tsub-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ [])))))
  ≡⟨ cong (Σ (Expr (l ∷ []) (l ◁* ∅) (Tsub (Tliftₛ (subst←RE ρ) l) (Tsub (Tliftₛ τ* l) T))))
       (fun-ext (λ e →
         cong₂ _∧_
     --------------------------------------------------
         (begin
           exp v ≡
             (Λ l ⇒
              subst id
              (sym
               (cong (Expr (l ∷ []) (l ◁* ∅))
                (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                 (sym (assoc-sub↑-sub↑ T τ* ρ*)))))
              e)
         ≡⟨ cong (exp v ≡_) (cong (λ H → (Λ l ⇒ subst id H e))
            (sym-cong (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                 (sym (assoc-sub↑-sub↑ T τ* ρ*))))) ⟩
           exp v ≡
             (Λ l ⇒
              subst id
              (cong (λ v₁ → Expr (l ∷ []) (l ◁* ∅) v₁)
               (sym
                (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                 (sym (assoc-sub↑-sub↑ T τ* ρ*)))))
              e)
         ≡⟨ cong (exp v ≡_) (cong (λ H → (Λ l ⇒ H))
           (sym (subst-∘ {P = id} {f = Expr (l ∷ []) (l ◁* ∅)}
                          (sym
                (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                 (sym (assoc-sub↑-sub↑ T τ* ρ*)))) {e}))) ⟩
           exp v ≡
             (Λ l ⇒
              subst (Expr (l ∷ []) (l ◁* ∅))
              (sym
               (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                (sym (assoc-sub↑-sub↑ T τ* ρ*))))
              e)
         ≡⟨ cong (exp v ≡_) (sym (subst-split-Λ
                 (cong (`∀α_,_ l) (trans (assoc-sub↑-sub↑ T τ* ρ*) 
                                         (sym (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*)))))
               (sym
               (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                (sym (assoc-sub↑-sub↑ T τ* ρ*)))) e)) ⟩
           exp v ≡ subst (Expr [] ∅) (cong (`∀α_,_ l)
                                       (trans
                                        (trans (fusion-Tsub-Tsub T (Tliftₛ τ* l) (Tliftₛ ρ* l))
                                         (step-≡ (Tsub (Tliftₛ τ* l ∘ₛₛ Tliftₛ ρ* l) T)
                                          (Tsub (Tliftₛ (τ* ∘ₛₛ ρ*) l) T ∎)
                                          (cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ₛₛ l τ* ρ*)))))
                                        (sym (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*)))))
                           (Λ l ⇒ e)
         ≡⟨ cong (exp v ≡_)
           (subst*-irrelevant (⟨ (Expr [] ∅) , (cong (`∀α_,_ l)
                                       (trans
                                        (trans (fusion-Tsub-Tsub T (Tliftₛ τ* l) (Tliftₛ ρ* l))
                                         (step-≡ (Tsub (Tliftₛ τ* l ∘ₛₛ Tliftₛ ρ* l) T)
                                          (Tsub (Tliftₛ (τ* ∘ₛₛ ρ*) l) T ∎)
                                          (cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ₛₛ l τ* ρ*)))))
                                        (sym (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))))) ⟩∷ [])
                                (⟨ (λ x → CExpr (`∀α l , x)) , (assoc-sub↑-sub↑ T τ* ρ*) ⟩∷ []) (Λ l ⇒ e) ) ⟩
           exp v ≡
             subst (λ x → CExpr (`∀α l , x)) (assoc-sub↑-sub↑ T τ* ρ*) (Λ l ⇒ e)
         ≡⟨ subst-swap-eq′ {F = CExpr ∘ (`∀α_,_ l)} (assoc-sub↑-sub↑ T τ* ρ*)
                             (exp v) (Λ l ⇒ e)  ⟩
           subst (CExpr ∘ (`∀α_,_ l)) (sym (assoc-sub↑-sub↑ T τ* ρ*)) (exp v) ≡ (Λ l ⇒ e)
         ≡⟨ cong (_≡ (Λ l ⇒ e))
            (sym (dist-subst' {F = (Value ∘ `∀α_,_ l)} {G = (CExpr ∘ (`∀α_,_ l))} id exp
                             (sym (assoc-sub↑-sub↑ T τ* ρ*)) (sym (assoc-sub↑-sub↑ T τ* ρ*)) v )) ⟩
           exp (subst (Value ∘ `∀α_,_ l) (sym (assoc-sub↑-sub↑ T τ* ρ*)) v) ≡
             (Λ l ⇒ e)
         ≡⟨ cong (λ H → exp H ≡ (Λ l ⇒ e))
            (subst-∘ {P = Value} {f = (`∀α_,_ l)} (sym (assoc-sub↑-sub↑ T τ* ρ*)) {v} ) ⟩
           exp
             (subst Value
              (cong (λ v₁ → `∀α l , v₁) (sym (assoc-sub↑-sub↑ T τ* ρ*))) v)
             ≡ (Λ l ⇒ e)
         ≡⟨ cong (λ H → exp (subst Value H v) ≡ (Λ l ⇒ e)) (sym (sym-cong (assoc-sub↑-sub↑ T τ* ρ*))) ⟩
           exp (subst Value (sym (cong (`∀α_,_ l) (assoc-sub↑-sub↑ T τ* ρ*))) v)
             ≡ (Λ l ⇒ e)
         ∎)
     --------------------------------------------------
         (begin
           ((T′ : Type [] l) (R : REL T′) →
             ∃-syntax
             (λ v₁ →
                (subst id
                 (sym
                  (cong (Expr (l ∷ []) (l ◁* ∅))
                   (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                    (sym (assoc-sub↑-sub↑ T τ* ρ*)))))
                 e
                 [ T′ ]ET)
                ⇓ v₁
                ∧
                𝓥⟦ T ⟧ (REext (Tsub-act τ* ρ) (T′ , R))
                (subst Value (lemma1 (Tsub-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ []))))
         ≡⟨ dep-ext (λ T′ → dep-ext (λ R →
            begin
              Σ (Value (Tsub (Tliftₛ (subst←RE (Tsub-act τ* ρ)) l) T [ T′ ]T))
                (λ v₁ →
                   (subst id
                    (sym
                     (cong (Expr (l ∷ []) (l ◁* ∅))
                      (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                       (sym (assoc-sub↑-sub↑ T τ* ρ*)))))
                    e
                    [ T′ ]ET)
                   ⇓ v₁
                   ∧
                   𝓥⟦ T ⟧ (REext (Tsub-act τ* ρ) (T′ , R))
                   (subst Value (lemma1 (Tsub-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ [])))
            ≡⟨ sigma-subst
                 (λ v₁ →
                    (subst id
                     (sym
                      (cong (Expr (l ∷ []) (l ◁* ∅))
                       (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                        (sym (assoc-sub↑-sub↑ T τ* ρ*)))))
                     e
                     [ T′ ]ET)
                    ⇓ v₁
                    ∧
                    𝓥⟦ T ⟧ (REext (Tsub-act τ* ρ) (T′ , R))
                    (subst Value (lemma1 (Tsub-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ [])))
                 (cong Value (cong (_[ T′ ]T)
                 ((trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                 (sym (assoc-sub↑-sub↑ T τ* ρ*)))))) ⟩
              Σ (Value (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T))
              (λ v₁ →
                  (subst id
                   (sym
                    (cong (Expr (l ∷ []) (l ◁* ∅))
                     (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                      (sym (assoc-sub↑-sub↑ T τ* ρ*)))))
                   e
                   [ T′ ]ET)
                  ⇓
                  subst id
                  (sym
                   (cong Value
                    (cong (_[ T′ ]T)
                     (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                      (sym (assoc-sub↑-sub↑ T τ* ρ*))))))
                  v₁
                  ∧
                  𝓥⟦ T ⟧ (REext (Tsub-act τ* ρ) (T′ , R))
                  (subst Value (lemma1 (Tsub-act τ* ρ) T T′ R)
                   (subst id
                    (sym
                     (cong Value
                      (cong (_[ T′ ]T)
                       (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                        (sym (assoc-sub↑-sub↑ T τ* ρ*))))))
                    v₁))
                  (z (⟦ T′ ⟧ [])))
            ≡⟨ cong (Σ (Value (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)))
              (fun-ext (λ v₁ →
              cong₂ _∧_
     --------------------------------------------------
              (begin
                (subst id
                   (sym
                    (cong (Expr (l ∷ []) (l ◁* ∅))
                     (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                      (sym (assoc-sub↑-sub↑ T τ* ρ*)))))
                   e
                   [ T′ ]ET)
                  ⇓
                  subst id
                  (sym
                   (cong Value
                    (cong (_[ T′ ]T)
                     (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                      (sym (assoc-sub↑-sub↑ T τ* ρ*))))))
                  v₁
              ≡⟨ cong (_⇓ _) (cong (λ H → subst id H e [ T′ ]ET)
                (sym-cong {f = (Expr (l ∷ []) (l ◁* ∅))}
                  (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*)) (sym (assoc-sub↑-sub↑ T τ* ρ*))))) ⟩
                (subst id
                   (cong (Expr (l ∷ []) (l ◁* ∅))
                    (sym
                     (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                      (sym (assoc-sub↑-sub↑ T τ* ρ*)))))
                   e
                   [ T′ ]ET)
                  ⇓
                  subst id
                  (sym
                   (cong Value
                    (cong (_[ T′ ]T)
                     (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                      (sym (assoc-sub↑-sub↑ T τ* ρ*))))))
                  v₁
              ≡⟨ cong (_⇓ subst id
                  (sym
                   (cong Value
                    (cong (_[ T′ ]T)
                     (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                      (sym (assoc-sub↑-sub↑ T τ* ρ*))))))
                  v₁) (sym (cong (_[ T′ ]ET)
                 (subst-∘ {P = id} {f = (Expr (l ∷ []) (l ◁* ∅))}
                                             (sym (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                      (sym (assoc-sub↑-sub↑ T τ* ρ*))))))) ⟩
                (subst (Expr (l ∷ []) (l ◁* ∅))
                   (sym
                    (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                     (sym (assoc-sub↑-sub↑ T τ* ρ*))))
                   e
                   [ T′ ]ET)
                  ⇓
                  subst id
                  (sym
                   (cong Value
                    (cong (_[ T′ ]T)
                     (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                      (sym (assoc-sub↑-sub↑ T τ* ρ*))))))
                  v₁
              ≡⟨ cong (_⇓ _) (dist-subst' {F = Expr (l ∷ []) (l ◁* ∅)}{G = (CExpr ∘ (_[ T′ ]T))} id (_[ T′ ]ET)
                                          (sym
                    (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                     (sym (assoc-sub↑-sub↑ T τ* ρ*))))
                     (assoc-sub↑-sub↑ T τ* ρ*)
                     e) ⟩
                subst (CExpr ∘ (_[ T′ ]T)) (assoc-sub↑-sub↑ T τ* ρ*) (e [ T′ ]ET)
                  ⇓
                  subst id
                  (sym
                   (cong Value
                    (cong (_[ T′ ]T)
                     (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                      (sym (assoc-sub↑-sub↑ T τ* ρ*))))))
                  v₁
              ≡⟨ cong₂ _⇓_
                (subst-∘ {P = CExpr}{f = (_[ T′ ]T)} (assoc-sub↑-sub↑ T τ* ρ*))
                (subst*-irrelevant (⟨ id , (sym
                   (cong Value
                    (cong (_[ T′ ]T)
                     (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                      (sym (assoc-sub↑-sub↑ T τ* ρ*)))))) ⟩∷ [] )
                                    (⟨ Value , (cong (_[ T′ ]T) (assoc-sub↑-sub↑ T τ* ρ*)) ⟩∷ [] ) v₁)
               ⟩
                subst CExpr (cong (_[ T′ ]T) (assoc-sub↑-sub↑ T τ* ρ*))
                  (e [ T′ ]ET)
                  ⇓ subst Value (cong (_[ T′ ]T) (assoc-sub↑-sub↑ T τ* ρ*)) v₁
              ≡⟨ sym (subst-split-eq-⇓₂ (cong (_[ T′ ]T) (assoc-sub↑-sub↑ T τ* ρ*))) ⟩
                (e [ T′ ]ET) ⇓ v₁
              ∎)
     --------------------------------------------------
              (let
                eq-1 = (lemma1 (Tsub-act τ* ρ) T T′ R)
                eq-2 = (cong Value
                             (cong (_[ T′ ]T)
                               (trans (cong (λ σ → Tsub (Tliftₛ σ l) T) (subst-Tsub-act ρ τ*))
                                      (sym (assoc-sub↑-sub↑ T τ* ρ*)))))
                eq-1↑ = (lemma1 ρ (Tsub (Tliftₛ τ* l) T) T′ R)
                eq-2↑ = (sym
                    (step-≡
                     ((α : Set l) → ⟦ Tsub (Tliftₛ τ* l) T ⟧ (α ∷ subst-to-env* ρ* []))
                     (step-≡
                      ((α : Set l) → ⟦ T ⟧ (α ∷ subst-to-env* τ* (subst-to-env* ρ* [])))
                      (((α : Set l) →
                        ⟦ T ⟧ (α ∷ subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                       ∎)
                      (congωl (λ η → (α : Set l) → ⟦ T ⟧ (α ∷ η))
                       (subst-to-env*-comp τ* ρ* [])))
                     (dep-ext
                      (λ ⟦α⟧ →
                         trans (subst-preserves (Tliftₛ τ* l) T)
                         (congωl (λ H → ⟦ T ⟧ (⟦α⟧ ∷ H))
                          (subst-to-env*-wk τ* ⟦α⟧ (subst-to-env* ρ* [])))))))
              in 
              begin
                𝓥⟦ T ⟧ (REext (Tsub-act τ* ρ) (T′ , R))
                  (subst Value eq-1
                   (subst id (sym eq-2)
                     v₁))
                  (z (⟦ T′ ⟧ []))
              ≡⟨ dcongωlll 𝓥⟦ T ⟧
                           (Tsub-act-REext ρ τ* T′ R)
              --------------------------------------------------
                           (begin
                             subst Value eq-1 (subst id (sym eq-2) v₁)
                           ≡⟨ subst*-irrelevant (⟨ id , sym eq-2 ⟩∷
                                                  ⟨ Value , eq-1 ⟩∷ [])
                                                 (⟨ Value , (trans
                                (step-≡ (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)
                                 (step-≡ (Tsub (subst←RE (REext ρ (T′ , R))) (Tsub (Tliftₛ τ* l) T))
                                  (Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T ∎)
                                  (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))))
                                 eq-1↑)
                                (congωl (λ z₁ → Tsub (subst←RE z₁) T)
                                 (symω (Tsub-act-REext ρ τ* T′ R)))) ⟩∷ [])
                                                 v₁ ⟩
                             subst Value
                               (trans
                                (step-≡ (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)
                                 (step-≡ (Tsub (subst←RE (REext ρ (T′ , R))) (Tsub (Tliftₛ τ* l) T))
                                  (Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T ∎)
                                  (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))))
                                 eq-1↑)
                                (congωl (λ z₁ → Tsub (subst←RE z₁) T)
                                 (symω (Tsub-act-REext ρ τ* T′ R))))
                               v₁
                           ≡⟨ sym (subst-subst {P = Value} (step-≡ (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)
                                 (step-≡ (Tsub (subst←RE (REext ρ (T′ , R))) (Tsub (Tliftₛ τ* l) T))
                                  (Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T ∎)
                                  (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))))
                                 eq-1↑)
                                 {(congωl (λ z₁ → Tsub (subst←RE z₁) T)
                                (symω (Tsub-act-REext ρ τ* T′ R)))}) ⟩
                             subst Value
                               (congωl (λ z₁ → Tsub (subst←RE z₁) T)
                                (symω (Tsub-act-REext ρ τ* T′ R)))
                               (subst Value
                                (step-≡ (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)
                                 (step-≡ (Tsub (subst←RE (REext ρ (T′ , R))) (Tsub (Tliftₛ τ* l) T))
                                  (Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T ∎)
                                  (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))))
                                 eq-1↑)
                                v₁)
                           ≡⟨ sym (substω-congω Value (λ z₁ → Tsub (subst←RE z₁) T) (symω (Tsub-act-REext ρ τ* T′ R)) _ ) ⟩
                             substω (λ z₁ → Value (Tsub (subst←RE z₁) T))
                               (symω (Tsub-act-REext ρ τ* T′ R))
                               (subst Value
                                (step-≡ (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)
                                 (step-≡ (Tsub (subst←RE (REext ρ (T′ , R))) (Tsub (Tliftₛ τ* l) T))
                                  (Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T ∎)
                                  (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))))
                                 eq-1↑)
                                v₁)
                           ∎)
              --------------------------------------------------
                           (begin
                             z (⟦ T′ ⟧ [])
                           ≡⟨  subst*-irrelevant []
                                                  (⟨ id , (congωl ⟦ T ⟧
                                 (congωω (⟦ T′ ⟧ [] ∷_)
                                  (conglω (λ σ → subst-to-env* σ [])
                                   (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                    (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                                     (Tsub-act-REext ρ τ* T′ R)))))) ⟩∷
                                                   ⟨ id , (congωl (λ z₁ → ⟦ T ⟧ (subst-to-env* (subst←RE z₁) []))
                                (symω (Tsub-act-REext ρ τ* T′ R))) ⟩∷ []) (z (⟦ T′ ⟧ []))
                           ⟩
                             subst id
                               (congωl (λ z₁ → ⟦ T ⟧ (subst-to-env* (subst←RE z₁) []))
                                (symω (Tsub-act-REext ρ τ* T′ R)))
                               (subst id
                                (congωl ⟦ T ⟧
                                 (congωω (⟦ T′ ⟧ [] ∷_)
                                  (conglω (λ σ → subst-to-env* σ [])
                                   (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                    (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                                     (Tsub-act-REext ρ τ* T′ R))))))
                                (z (⟦ T′ ⟧ [])))
                           ≡⟨ cong (subst id
                               (congωl (λ z₁ → ⟦ T ⟧ (subst-to-env* (subst←RE z₁) []))
                                (symω (Tsub-act-REext ρ τ* T′ R))))
                                (sym (substω-congω id ⟦ T ⟧ (congωω (⟦ T′ ⟧ [] ∷_)
                                 (conglω (λ σ → subst-to-env* σ [])
                                  (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                   (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                                    (Tsub-act-REext ρ τ* T′ R)))))
                                 (z (⟦ T′ ⟧ [])))) ⟩
                             subst id
                               (congωl (λ z₁ → ⟦ T ⟧ (subst-to-env* (subst←RE z₁) []))
                                (symω (Tsub-act-REext ρ τ* T′ R)))
                               (substω ⟦ T ⟧
                                (congωω (⟦ T′ ⟧ [] ∷_)
                                 (conglω (λ σ → subst-to-env* σ [])
                                  (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                   (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                                    (Tsub-act-REext ρ τ* T′ R)))))
                                (z (⟦ T′ ⟧ [])))
                           ≡⟨ sym (substω-congω id (λ z₁ → ⟦ T ⟧ (subst-to-env* (subst←RE z₁) [])) (symω (Tsub-act-REext ρ τ* T′ R)) _) ⟩
                             substω (λ z₁ → ⟦ T ⟧ (subst-to-env* (subst←RE z₁) []))
                               (symω (Tsub-act-REext ρ τ* T′ R))
                               (substω ⟦ T ⟧
                                (congωω (⟦ T′ ⟧ [] ∷_)
                                 (conglω (λ σ → subst-to-env* σ [])
                                  (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                   (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                                    (Tsub-act-REext ρ τ* T′ R)))))
                                (z (⟦ T′ ⟧ [])))
                           ∎)
              --------------------------------------------------
                         ⟩
                𝓥⟦ T ⟧ (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))
                       (subst Value
                              (begin
                                (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)
                              ≡⟨ lemma1 ρ (Tsub (Tliftₛ τ* l) T) T′ R ⟩
                                Tsub (subst←RE (REext ρ (T′ , R))) (Tsub (Tliftₛ τ* l) T)
                              ≡⟨ fusion-Tsub-Tsub T  (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R))) ⟩
                                Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T
                              ∎)
                              v₁)
                       (substω ⟦ T ⟧
                               (congωω (⟦ T′ ⟧ [] ∷_)
                                       (conglω (λ σ → subst-to-env* σ [])
                                         (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                                (congωl (λ ρ → Tdropₛ (subst←RE ρ)) (Tsub-act-REext ρ τ* T′ R)))))
                                (z (⟦ T′ ⟧ [])))
              ≡⟨ LRVsub T
                         (REext ρ (T′ , R))
                         (Tliftₛ τ* l)
                         (subst Value
                              (begin
                                (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)
                              ≡⟨ lemma1 ρ (Tsub (Tliftₛ τ* l) T) T′ R ⟩
                                Tsub (subst←RE (REext ρ (T′ , R))) (Tsub (Tliftₛ τ* l) T)
                              ≡⟨ fusion-Tsub-Tsub T  (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R))) ⟩
                                Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T
                              ∎)
                              v₁)
                         (substω ⟦ T ⟧
                               (congωω (⟦ T′ ⟧ [] ∷_)
                                       (conglω (λ σ → subst-to-env* σ [])
                                         (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                                (congωl (λ ρ → Tdropₛ (subst←RE ρ)) (Tsub-act-REext ρ τ* T′ R)))))
                                (z (⟦ T′ ⟧ []))) ⟩
                𝓥⟦ Tsub (Tliftₛ τ* l) T ⟧ (REext ρ (T′ , R))
                  (subst Value
                   (sym (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))))
                   (subst Value
                    (step-≡ (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)
                     (trans (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))) refl)
                     eq-1↑)
                    v₁))
                  (subst id
                   (sym
                    (step-≡
                     (⟦ Tsub (Tliftₛ τ* l) T ⟧
                      (subst-to-env* (subst←RE (REext ρ (T′ , R))) []))
                     (trans (congωl ⟦ T ⟧ (subst-to-env*-comp (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R))) [])) refl)
                     (subst-preserves (Tliftₛ τ* l) T)))
                   (substω ⟦ T ⟧
                    (congωω (⟦ T′ ⟧ [] ∷_)
                     (conglω (λ σ → subst-to-env* σ [])
                      (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                       (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                        (Tsub-act-REext ρ τ* T′ R)))))
                    (z (⟦ T′ ⟧ []))))
              ≡⟨ dcong₂ (𝓥⟦ Tsub (Tliftₛ τ* l) T ⟧ (REext ρ (T′ , R)))
              --------------------------------------------------
                (subst*-irrelevant (⟨ Value , (step-≡ (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)
                                        (trans
                                         (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))) refl)
                                        eq-1↑) ⟩∷
                                     ⟨ Value , (sym (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R))))) ⟩∷ [])
                                    (⟨ Value , eq-1↑ ⟩∷ []) v₁)
              --------------------------------------------------
                (let
                  eq-3 =  (trans
                            (congωl ⟦ T ⟧
                             (congωω (⟦ T′ ⟧ [] ∷_)
                              (conglω (λ σ → subst-to-env* σ [])
                               (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                                 (Tsub-act-REext ρ τ* T′ R))))))
                            (sym
                             (step-≡
                              (⟦ Tsub (Tliftₛ τ* l) T ⟧
                               (subst-to-env* (subst←RE (REext ρ (T′ , R))) []))
                              (trans
                               (congωl ⟦ T ⟧
                                (subst-to-env*-comp (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))
                                 []))
                               refl)
                              (subst-preserves (Tliftₛ τ* l) T))))
{-
                  het = H.≅-to-≡
                       (R.begin
                         subst id eq-2↑ z (⟦ T′ ⟧ [])
                       R.≅⟨ H.cong₂ {A = Set l → Set l′} {B = λ q → (a : Set l) → q a} (λ _ z → z (⟦ T′ ⟧ []))
                                    (H.≡-to-≅ (fun-ext (λ x → trans
                                                               (trans (subst-preserves (Tliftₛ τ* l) T)
                                                                (congωl (λ H → ⟦ T ⟧ (x ∷ H))
                                                                 (subst-to-env*-wk τ* x (subst-to-env* ρ* []))))
                                                               (congωl (λ ■ → ⟦ T ⟧ (x ∷ ■)) (subst-to-env*-comp τ* ρ* [])))))
                                    (H.≡-subst-removable id eq-2↑ _) ⟩
                         z (⟦ T′ ⟧ [])
                       R.≅⟨ H.sym (H.≡-subst-removable id eq-3 _) ⟩
                         subst id eq-3 (z (⟦ T′ ⟧ []))
                       R.∎)
-}
                in
                begin
                  subst
                    (λ _ →
                       ⟦ Tsub (Tliftₛ τ* l) T ⟧
                       (subst-to-env* (subst←RE (REext ρ (T′ , R))) []))
                    (subst*-irrelevant
                     (⟨ Value ,
                      step-≡ (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)
                      (trans
                       (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))) refl)
                      eq-1↑
                      ⟩∷
                      (⟨ Value ,
                       sym (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R))))
                       ⟩∷ []))
                     (⟨ Value , eq-1↑ ⟩∷ []) v₁)
                    (subst id
                     (sym
                      (step-≡
                       (⟦ Tsub (Tliftₛ τ* l) T ⟧
                        (subst-to-env* (subst←RE (REext ρ (T′ , R))) []))
                       (trans
                        (congωl ⟦ T ⟧
                         (subst-to-env*-comp (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))
                          []))
                        refl)
                       (subst-preserves (Tliftₛ τ* l) T)))
                     (substω ⟦ T ⟧
                      (congωω (⟦ T′ ⟧ [] ∷_)
                       (conglω (λ σ → subst-to-env* σ [])
                        (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                         (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                          (Tsub-act-REext ρ τ* T′ R)))))
                      (z (⟦ T′ ⟧ []))))
                ≡⟨ subst-const (subst*-irrelevant
                     (⟨ Value ,
                      step-≡ (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T)
                      (trans
                       (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))) refl)
                      eq-1↑
                      ⟩∷
                      (⟨ Value ,
                       sym (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R))))
                       ⟩∷ []))
                     (⟨ Value , eq-1↑ ⟩∷ []) v₁) ⟩
                  subst id
                    (sym
                     (step-≡
                      (⟦ Tsub (Tliftₛ τ* l) T ⟧
                       (subst-to-env* (subst←RE (REext ρ (T′ , R))) []))
                      (trans
                       (congωl ⟦ T ⟧
                        (subst-to-env*-comp (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))
                         []))
                       refl)
                      (subst-preserves (Tliftₛ τ* l) T)))
                    (substω ⟦ T ⟧
                     (congωω (⟦ T′ ⟧ [] ∷_)
                      (conglω (λ σ → subst-to-env* σ [])
                       (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                        (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                         (Tsub-act-REext ρ τ* T′ R)))))
                     (z (⟦ T′ ⟧ [])))
                ≡⟨ cong (subst id
                    (sym
                     (step-≡
                      (⟦ Tsub (Tliftₛ τ* l) T ⟧
                       (subst-to-env* (subst←RE (REext ρ (T′ , R))) []))
                      (trans
                       (congωl ⟦ T ⟧
                        (subst-to-env*-comp (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))
                         []))
                       refl)
                      (subst-preserves (Tliftₛ τ* l) T))))
                      (substω-congω id ⟦ T ⟧
                      (congωω (⟦ T′ ⟧ [] ∷_)
                      (conglω (λ σ → subst-to-env* σ [])
                       (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                        (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                         (Tsub-act-REext ρ τ* T′ R)))))
                      (z (⟦ T′ ⟧ []))) ⟩
                  subst id
                    (sym
                     (step-≡
                      (⟦ Tsub (Tliftₛ τ* l) T ⟧
                       (subst-to-env* (subst←RE (REext ρ (T′ , R))) []))
                      (trans
                       (congωl ⟦ T ⟧
                        (subst-to-env*-comp (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))
                         []))
                       refl)
                      (subst-preserves (Tliftₛ τ* l) T)))
                    (subst id
                     (congωl ⟦ T ⟧
                      (congωω (⟦ T′ ⟧ [] ∷_)
                       (conglω (λ σ → subst-to-env* σ [])
                        (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                         (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                          (Tsub-act-REext ρ τ* T′ R))))))
                     (z (⟦ T′ ⟧ [])))
                ≡⟨ subst-subst {P = id}
                                (congωl ⟦ T ⟧
                                  (congωω (⟦ T′ ⟧ [] ∷_)
                                   (conglω (λ σ → subst-to-env* σ [])
                                    (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                     (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                                      (Tsub-act-REext ρ τ* T′ R))))))
                                {(sym
                                   (step-≡
                                    (⟦ Tsub (Tliftₛ τ* l) T ⟧
                                     (subst-to-env* (subst←RE (REext ρ (T′ , R))) []))
                                    (trans
                                     (congωl ⟦ T ⟧
                                      (subst-to-env*-comp (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))
                                       []))
                                     refl)
                                    (subst-preserves (Tliftₛ τ* l) T)))}
                                {z (⟦ T′ ⟧ [])} ⟩
                  subst id
                    (trans
                     (congωl ⟦ T ⟧
                      (congωω (⟦ T′ ⟧ [] ∷_)
                       (conglω (λ σ → subst-to-env* σ [])
                        (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                         (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                          (Tsub-act-REext ρ τ* T′ R))))))
                     (sym
                      (step-≡
                       (⟦ Tsub (Tliftₛ τ* l) T ⟧
                        (subst-to-env* (subst←RE (REext ρ (T′ , R))) []))
                       (trans
                        (congωl ⟦ T ⟧
                         (subst-to-env*-comp (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))
                          []))
                        refl)
                       (subst-preserves (Tliftₛ τ* l) T))))
                    (z (⟦ T′ ⟧ []))
                -- alternative: het
                ≡⟨ subst-irrelevant eq-3 _ (z (⟦ T′ ⟧ [])) ⟩
                  subst id (cong (λ r → r (⟦ T′ ⟧ [])) (sym (fun-ext (λ x → trans
                                                               (trans (subst-preserves (Tliftₛ τ* l) T)
                                                                (congωl (λ H → ⟦ T ⟧ (x ∷ H))
                                                                 (subst-to-env*-wk τ* x (subst-to-env* ρ* []))))
                                                               (congωl (λ ■ → ⟦ T ⟧ (x ∷ ■)) (subst-to-env*-comp τ* ρ* [])))))) (z (⟦ T′ ⟧ []))
                ≡⟨ sym (subst-fun-special (sym (fun-ext (λ x → trans
                                                               (trans (subst-preserves (Tliftₛ τ* l) T)
                                                                (congωl (λ H → ⟦ T ⟧ (x ∷ H))
                                                                 (subst-to-env*-wk τ* x (subst-to-env* ρ* []))))
                                                               (congωl (λ ■ → ⟦ T ⟧ (x ∷ ■)) (subst-to-env*-comp τ* ρ* [])))))
                                          eq-2↑
                                          z (⟦ T′ ⟧ [])) ⟩
                  subst id eq-2↑ z (⟦ T′ ⟧ [])
                ∎)
              -- z                : (α : Set l) → ⟦ T ⟧ (α ∷ subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])
              -- subst id eq-2↑ z : ((α : Set l) → ⟦ Tsub (Tliftₛ τ* l) T ⟧ (α ∷ subst-to-env* ρ* []))
              --------------------------------------------------
                ⟩
                𝓥⟦ Tsub (Tliftₛ τ* l) T ⟧ (REext ρ (T′ , R))
                  (subst Value eq-1↑ v₁)
                  (subst id
                   eq-2↑
                   z (⟦ T′ ⟧ []))
              ∎)
     --------------------------------------------------
              )) ⟩
              Σ (Value (Tsub (Tliftₛ ρ* l) (Tsub (Tliftₛ τ* l) T) [ T′ ]T))
                (λ v₁ →
                   (e [ T′ ]ET) ⇓ v₁ ∧
                   𝓥⟦ Tsub (Tliftₛ τ* l) T ⟧ (REext ρ (T′ , R))
                   (subst Value (lemma1 ρ (Tsub (Tliftₛ τ* l) T) T′ R) v₁)
                   (subst id
                    (sym
                     (step-≡
                      ((α : Set l) → ⟦ Tsub (Tliftₛ τ* l) T ⟧ (α ∷ subst-to-env* ρ* []))
                      (step-≡
                       ((α : Set l) → ⟦ T ⟧ (α ∷ subst-to-env* τ* (subst-to-env* ρ* [])))
                       (((α : Set l) →
                         ⟦ T ⟧ (α ∷ subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                        ∎)
                       (congωl (λ η → (α : Set l) → ⟦ T ⟧ (α ∷ η))
                        (subst-to-env*-comp τ* ρ* [])))
                      (dep-ext
                       (λ ⟦α⟧ →
                          trans (subst-preserves (Tliftₛ τ* l) T)
                          (congωl (λ H → ⟦ T ⟧ (⟦α⟧ ∷ H))
                           (subst-to-env*-wk τ* ⟦α⟧ (subst-to-env* ρ* [])))))))
                    z (⟦ T′ ⟧ [])))
            ∎)) ⟩
           ((T′ : Type [] l) (R : REL T′) →
             ∃-syntax
             (λ v₁ →
                (e [ T′ ]ET) ⇓ v₁ ∧
                𝓥⟦ Tsub (Tliftₛ τ* l) T ⟧ (REext ρ (T′ , R))
                (subst Value (lemma1 ρ (Tsub (Tliftₛ τ* l) T) T′ R) v₁)
                (subst id
                 (sym
                  (step-≡
                   ((α : Set l) → ⟦ Tsub (Tliftₛ τ* l) T ⟧ (α ∷ subst-to-env* ρ* []))
                   (step-≡
                    ((α : Set l) → ⟦ T ⟧ (α ∷ subst-to-env* τ* (subst-to-env* ρ* [])))
                    (((α : Set l) →
                      ⟦ T ⟧ (α ∷ subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                     ∎)
                    (congωl (λ η → (α : Set l) → ⟦ T ⟧ (α ∷ η))
                     (subst-to-env*-comp τ* ρ* [])))
                   (dep-ext
                    (λ ⟦α⟧ →
                       trans (subst-preserves (Tliftₛ τ* l) T)
                       (congωl (λ H → ⟦ T ⟧ (⟦α⟧ ∷ H))
                        (subst-to-env*-wk τ* ⟦α⟧ (subst-to-env* ρ* [])))))))
                 z (⟦ T′ ⟧ []))))
         ∎)
     --------------------------------------------------
         )) ⟩
    Σ (Expr (l ∷ []) (l ◁* ∅) (Tsub (Tliftₛ (subst←RE ρ) l) (Tsub (Tliftₛ τ* l) T)))
      (λ e →
         (exp
          (subst Value
           (sym (cong (`∀α_,_ l) (assoc-sub↑-sub↑ T τ* (subst←RE ρ)))) v)
          ≡ (Λ l ⇒ e))
         ∧
         ((T′ : Type [] l) (R : REL T′) →
          ∃-syntax
          (λ v₁ →
             (e [ T′ ]ET) ⇓ v₁ ∧
             𝓥⟦ Tsub (Tliftₛ τ* l) T ⟧ (REext ρ (T′ , R))
             (subst Value (lemma1 ρ (Tsub (Tliftₛ τ* l) T) T′ R) v₁)
             (subst id
              (sym
               (step-≡
                ((α : Set l) →
                 ⟦ Tsub (Tliftₛ τ* l) T ⟧ (α ∷ subst-to-env* (subst←RE ρ) []))
                (step-≡
                 ((α : Set l) →
                  ⟦ T ⟧ (α ∷ subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])))
                 (((α : Set l) →
                   ⟦ T ⟧ (α ∷ subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                  ∎)
                 (congωl (λ η → (α : Set l) → ⟦ T ⟧ (α ∷ η))
                  (subst-to-env*-comp τ* (subst←RE ρ) [])))
                (dep-ext
                 (λ ⟦α⟧ →
                    trans (subst-preserves (Tliftₛ τ* l) T)
                    (congωl (λ H → ⟦ T ⟧ (⟦α⟧ ∷ H))
                     (subst-to-env*-wk τ* ⟦α⟧ (subst-to-env* (subst←RE ρ) [])))))))
              z (⟦ T′ ⟧ [])))))
  ≡⟨ refl ⟩
    𝓥⟦ Tsub τ* (`∀α l , T) ⟧ ρ
      (subst Value (sym (fusion-Tsub-Tsub (`∀α l , T) τ* (subst←RE ρ))) v)
      (subst id
       (sym
        (step-≡ (⟦ Tsub τ* (`∀α l , T) ⟧ (subst-to-env* (subst←RE ρ) []))
         (step-≡
          (⟦ `∀α l , T ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])))
          (⟦ `∀α l , T ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
          (congωl ⟦ `∀α l , T ⟧ (subst-to-env*-comp τ* (subst←RE ρ) [])))
         (subst-preserves τ* (`∀α l , T))))
       z)
  ∎
LRVsub `ℕ ρ τ* v z =
  begin
    𝓥⟦ `ℕ ⟧ (Tsub-act τ* ρ) v z
  ≡⟨ refl ⟩
    Σ ℕ (λ n → (exp v ≡ # n) × (n ≡ z))
  ≡⟨ cong (Σ ℕ)
     (fun-ext (λ n → cong (Σ (exp v ≡ (# n)))
       (fun-ext (λ x → cong (n ≡_)
         (subst-irrelevant {F = id} refl (sym (trans (congωl (λ η → ℕ) (subst-to-env*-comp τ* (λ l x₁ → proj₁ (ρ l x₁)) [])) refl)) z))))) ⟩
    Σ ℕ (λ n →
         (exp v ≡ (# n)) × (n ≡ subst id (sym (trans (congωl (λ η → ℕ) (subst-to-env*-comp τ* (λ l x₁ → proj₁ (ρ l x₁)) [])) refl)) z))
  ≡⟨ refl ⟩
    𝓥⟦ Tsub τ* `ℕ ⟧ ρ
      (subst Value (sym (fusion-Tsub-Tsub `ℕ τ* (subst←RE ρ))) v)
      (subst id
       (sym
        (step-≡ (⟦ Tsub τ* `ℕ ⟧ (subst-to-env* (subst←RE ρ) []))
         (step-≡ (⟦ `ℕ ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])))
          (⟦ `ℕ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
          (congωl ⟦ `ℕ ⟧ (subst-to-env*-comp τ* (subst←RE ρ) [])))
         (subst-preserves{η₂ = subst-to-env* (subst←RE ρ) []} τ* `ℕ)))
       z)
  ∎

