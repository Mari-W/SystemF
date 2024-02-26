module Logical1 where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; tabulate)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; case_of_; _|>_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; subst-subst-sym; subst-sym-subst; subst-subst; -- Properties
        module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

open import Ext
open import SetOmega
open import SubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution
open import ExprSubstProperties
open import SmallStep

----------------------------------------------------------------------
-- auxiliary


exprTy : {T : Type Δ l} → Expr Δ Γ T → Type Δ l
exprTy {T = T} e = T

levelTy : Type Δ l → Level
levelTy {l = l} T = l

levelEnv : TEnv Δ → Level
levelEnv ∅ = zero
levelEnv (T ◁ Γ) = levelTy T ⊔ levelEnv Γ
levelEnv (l ◁* Γ) = levelEnv Γ

levelΔ : LEnv → Level
levelΔ [] = zero
levelΔ (l ∷ Δ) = l ⊔ levelΔ Δ

----------------------------------------------------------------------

-- big step call by value semantics (analogous to Benton et al)

Value : Type [] l → Set
Value T = Expr [] ∅ T

V-ℕ :  (n : ℕ) → Value `ℕ
V-ℕ n = # n

V-ƛ : ∀ {T : Type [] l}{T′ : Type [] l′} → Expr [] (T ◁ ∅) T′ → Value (T ⇒ T′)
V-ƛ e = ƛ e

V-Λ : ∀ (l : Level) → {T : Type (l ∷ []) l′} → Expr (l ∷ []) (l ◁* ∅) T → Value (`∀α l , T)
V-Λ l e = Λ l ⇒ e

exp : Value T → Expr [] ∅ T
exp = id

-- big step semantics

variable v v₂ : Value T

infix 15 _⇓_
data _⇓_ : Expr [] ∅ T → Value T → Set where
  ⇓-n : ∀ {n} → (# n) ⇓ V-ℕ n
  ⇓-ƛ : (ƛ e) ⇓ V-ƛ e
  ⇓-· : e₁ ⇓ V-ƛ e → e₂ ⇓ v₂ → (e [ exp v₂ ]E) ⇓ v → (e₁ · e₂) ⇓ v
  ⇓-Λ : (Λ l ⇒ e) ⇓ V-Λ l e
  ⇓-∙ : e₁ ⇓ V-Λ l e → (e [ T ]ET) ⇓ v → (e₁ ∙ T) ⇓ v

-- exp-v⇓v : ∀ (v : Value T) → exp v ⇓ v
-- exp-v⇓v (.(# _) , v-n) = ⇓-n
-- exp-v⇓v (.(ƛ _) , v-ƛ) = ⇓-ƛ
-- exp-v⇓v (.(Λ _ ⇒ _) , v-Λ) = ⇓-Λ

infixl 10 _∧_
_∧_ = _×_

-- logical relation

-- relation between a syntactic value and a semantic value

REL : Type [] l → Set (suc l)
REL {l} T = Value T → ⟦ T ⟧ [] → Set l 

RelEnv : (Δ : LEnv) → Setω
RelEnv Δ = ∀ l → l ∈ Δ → Σ (Type [] l) REL

RELIrred : ∀ {l}{T : Type [] l} → REL T → Set l
RELIrred r = ∀ v z → r v z → v ⇓ v

RelEnvIrred : RelEnv Δ → Setω
RelEnvIrred ρ = ∀ l x → RELIrred (proj₂ (ρ l x)) 

-- type renaming acting on RelEnv by composition

Tren-act : TRen Δ₁ Δ₂ → RelEnv Δ₂ → RelEnv Δ₁
Tren-act τ* ρ = λ l x → ρ l (τ* l x)

REdrop′ : RelEnv (l ∷ Δ) → RelEnv Δ
REdrop′ ρ l x = ρ l (there x)

REdrop : RelEnv (l ∷ Δ) → RelEnv Δ
REdrop = Tren-act (Twkᵣ Tidᵣ)

REdrop-≡ : ∀ ρ l x → REdrop{l = l′}{Δ = Δ} ρ l x ≡ REdrop′ ρ l x
REdrop-≡ ρ l x = refl

REext : RelEnv Δ → (Σ (Type [] l) REL) → RelEnv (l ∷ Δ)
REext ρ R _ here = R
REext ρ R _ (there x) = ρ _ x

subst←RE : RelEnv Δ → TSub Δ []
subst←RE ρ l x = proj₁ (ρ l x)

subst←RE-ext : ∀ (ρ : RelEnv Δ) (T : Type [] l) (R : REL T) (l′ : Level) (x : l′ ∈ (l ∷ Δ)) → subst←RE (REext ρ (T , R)) l′ x ≡ Textₛ (subst←RE ρ) T l′ x
subst←RE-ext ρ T R l here = refl
subst←RE-ext ρ T R l (there x) = refl

subst←RE-ext-ext : ∀ (ρ : RelEnv Δ) (T : Type [] l) (R : REL T) → subst←RE (REext ρ (T , R)) ≡ Textₛ (subst←RE ρ) T
subst←RE-ext-ext ρ T R = fun-ext₂ (subst←RE-ext ρ T R)


subst←RE-drop : ∀ (ρ : RelEnv (l ∷ Δ)) →
  (l′ : Level) (x : l′ ∈ Δ) → (subst←RE (REdrop ρ)) l′ x ≡ (Tdropₛ (subst←RE ρ)) l′ x
subst←RE-drop ρ l′ here = refl
subst←RE-drop ρ l′ (there x) = refl

subst←RE-drop-ext : ∀ (ρ : RelEnv (l ∷ Δ)) →
  (subst←RE (REdrop ρ)) ≡ (Tdropₛ (subst←RE ρ))
subst←RE-drop-ext ρ = fun-ext₂ (subst←RE-drop ρ)

REdrop-REext≡id : (ρ : RelEnv Δ) → (T′ : Type [] l) → (R : REL T′) → REdrop (REext ρ (T′ , R)) ≡ω ρ
REdrop-REext≡id {Δ = Δ} ρ T′ R = refl

-- holds definitionally
subst←RE-ren : ∀ (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂)
  → (l′ : Level) (x : l′ ∈ Δ₁) → subst←RE (Tren-act τ* ρ) l′ x ≡ (τ* ∘ᵣₛ subst←RE ρ) l′ x
subst←RE-ren ρ τ* l′ x = refl

-- special case of composition sub o ren

sublemma : (σ : TSub Δ []) → (Textₛ σ T) ≡ Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ T
sublemma {T = T} σ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → begin 
        σ _ x
      ≡⟨ sym (TidₛT≡T (σ _ x)) ⟩
        Tsub Tidₛ (σ _ x)
      ≡⟨ sym (fusion-Tsub-Tren (σ _ x) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T)) ⟩
        Tsub (Textₛ Tidₛ T) (Twk (σ _ x)) 
      ∎

lemma2 : (σ : TSub Δ []) → (T  : Type (l ∷ Δ) l′) → (T′ : Type [] l)
  → Tsub (Tliftₛ σ l) T [ T′ ]T ≡ Tsub (Textₛ σ T′) T
lemma2 σ T T′ = begin 
    Tsub (Textₛ Tidₛ T′) (Tsub (Tliftₛ σ _) T)
  ≡⟨ fusion-Tsub-Tsub T (Tliftₛ σ _) (Textₛ Tidₛ T′) ⟩
    Tsub (Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ T′) T
  ≡⟨ cong (λ σ → Tsub σ T) (sym (sublemma σ)) ⟩
    Tsub (Textₛ σ T′) T
  ∎
   

lemma1 : (ρ  : RelEnv Δ) → (T  : Type (l ∷ Δ) l′) → (T′ : Type [] l) → (R  : REL T′)
  → Tsub (Tliftₛ (subst←RE ρ) l) T [ T′ ]T ≡ Tsub (subst←RE (REext ρ (T′ , R))) T
lemma1 {l = l} ρ T T′ R =
  begin
    Tsub (Tliftₛ (subst←RE ρ) l) T [ T′ ]T
    ≡⟨ lemma2 (subst←RE ρ) T T′ ⟩
    Tsub (Textₛ (subst←RE ρ) T′) T
    ≡⟨ cong (λ G → Tsub G T) (sym (subst←RE-ext-ext ρ T′ R)) ⟩
    Tsub (subst←RE (REext ρ (T′ , R))) T
    ∎

postulate
  relenv-ext : ∀ {Δ}{f g : RelEnv Δ} → (∀ l x → f l x ≡ g l x) → f ≡ω g

Tren-act-REext-ext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l) (R : REL T′) → ∀ l₂ x₂ → (REext (Tren-act τ* ρ) (T′ , R)) l₂ x₂ ≡ Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R)) l₂ x₂
Tren-act-REext-ext ρ τ* T′ R l₂ here = refl
Tren-act-REext-ext ρ τ* T′ R l₂ (there x₂) = refl

Tren-act-REext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l) (R : REL T′) → (REext (Tren-act τ* ρ) (T′ , R)) ≡ω Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R))
Tren-act-REext ρ τ* T′ R = relenv-ext (Tren-act-REext-ext ρ τ* T′ R)

-- auxiliary


Gdropt : (σ* : TSub (l ∷ Δ) [])
  → Env (l ∷ Δ) (l ◁* Γ) (subst-to-env* σ* [])
  → Env Δ Γ (subst-to-env* (Tdropₛ σ*) [])
Gdropt σ* γ l T x =
  let r = γ l (Twk T) (tskip x) in
  subst id (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {subst-to-env* (Tdropₛ σ*) []} {subst-to-env* σ* []} (wkᵣ∈Ren* (subst-to-env* (Tdropₛ σ*) []) (⟦ σ* _ here ⟧ [])) T) r

ENVdrop : ∀ {l}{T : Type Δ l} → (Γ : TEnv Δ) → (η : Env* Δ) → Env Δ (T ◁ Γ) η → Env Δ Γ η
ENVdrop Γ η γ l T x = γ l T (there x)

ENVdrop-extend : ∀ {l}{Δ}{Γ}{T : Type Δ l}{η : Env* Δ}
  → (γ : Env Δ Γ η)
  → (z : ⟦ T ⟧ η)
  → γ ≡ω ENVdrop {T = T} Γ η (extend γ z)
ENVdrop-extend {l = l} {Δ = Δ} {Γ = Γ}{T = T}{η = η} γ z = fun-extω (λ l′ → fun-ext₂ (aux l′))
  where
    aux : (l′ : Level) (T′ : Type Δ l′) (x : inn T′ Γ) → γ l′ T′ x ≡ ENVdrop {T = T} Γ η (extend γ z) l′ T′ x
    aux l′ T′ here = refl
    aux l′ T′ (there x) = refl
    aux l′ .(Twk _) (tskip x) = refl

-- stratified logical relation

{-
module maybe-simpler? where
        LRV′ : (T : Type Δ l) → (ρ : RelEnv Δ)
          → REL (Tsub (subst←RE ρ) T)
        LRV′ (` α) ρ v z = proj₂ (ρ _ α) v z 
        LRV′ (T₁ ⇒ T₂) ρ u f =
          ∃[ e ] (u ≡ ƛ e) ∧
          ∀ (w : Value (Tsub (subst←RE ρ) T₁)) →
          ∀ (z : ⟦ Tsub (subst←RE ρ) T₁ ⟧ []) →
          LRV′ T₁ ρ w z →
          ∃[ v ] (e [ exp w ]E ⇓ v) ∧ LRV′ T₂ ρ v (f z)
        LRV′ (`∀α l , T) ρ u F =
          ∃[ e ] (u ≡ Λ l ⇒ e) ∧
          ∀ (T′ : Type [] l) →
          ∀ (R : REL T′) →
          ∃[ v ] (e [ T′ ]ET ⇓ v) ∧ 
                 let ρ′ = REext ρ (T′ , R)
                     z′ = F (⟦ T′ ⟧ [])
                 in LRV′ T ρ′
                         (subst Value (lemma1 ρ T T′ R) v)
                         (subst id (begin
                           ⟦ Tsub (Tliftₛ (subst←RE ρ) l) T ⟧ (⟦ T′ ⟧ [] ∷ [])
                         ≡⟨ sym (Tsingle-subst-preserves [] T′ (Tsub (Tliftₛ (subst←RE ρ) l) T)) ⟩
                           ⟦ Tsub (Tliftₛ (subst←RE ρ) l) T [ T′ ]T ⟧ []
                         ≡⟨ cong (λ t → ⟦ t ⟧ []) (σ↑T[T′]≡TextₛσT′T (subst←RE ρ) T′ T) ⟩
                           ⟦ Tsub (Textₛ (subst←RE ρ) T′) T ⟧ []
                         ≡⟨ sym (cong (λ t → ⟦ Tsub t T ⟧ []) (subst←RE-ext-ext ρ T′ R) ) ⟩
                           ⟦ Tsub (subst←RE (REext ρ (T′ , R))) T ⟧ []
                         ∎) z′)
        LRV′ `ℕ ρ u z = ∃[ n ] (u ≡ (# n)) ∧ (n ≡ z)
-}

𝓥⟦_⟧ : (T : Type Δ l) → (ρ : RelEnv Δ)
  → Value (Tsub (subst←RE ρ) T) → ⟦ T ⟧ (subst-to-env* (subst←RE ρ) []) → Set l
𝓥⟦ ` α ⟧ ρ v z =
  proj₂ (ρ _ α) v (subst id (sym (subst-var-preserves α (subst←RE ρ) [])) z)
𝓥⟦ T₁ ⇒ T₂ ⟧ ρ u f =
  ∃[ e ] (u ≡ ƛ e) ∧
  ∀ w z → 𝓥⟦ T₁ ⟧ ρ w z → ∃[ v ] (e [ exp w ]E ⇓ v) ∧ 𝓥⟦ T₂ ⟧ ρ v (f z)
𝓥⟦ `∀α l , T ⟧ ρ u F =
  ∃[ e ] (u ≡ Λ l ⇒ e) ∧
  ∀ T′ R →
  ∃[ v ] (e [ T′ ]ET ⇓ v)
       ∧ let ρ′ = REext ρ (T′ , R)
         in 𝓥⟦ T ⟧ ρ′ (subst Value (lemma1 ρ T T′ R) v) (F (⟦ T′ ⟧ []))
𝓥⟦ `ℕ ⟧ ρ u z =
  ∃[ n ] (u ≡ (# n)) ∧ (n ≡ z)


𝓔⟦_⟧ : (T : Type Δ l) → (ρ : RelEnv Δ)
  → Value (Tsub (subst←RE ρ) T) → ⟦ T ⟧ (subst-to-env* (subst←RE ρ) []) → Set l
𝓔⟦ T ⟧ ρ e z = ∃[ v ] (e ⇓ v) ∧ 𝓥⟦ T ⟧ ρ v z

-- closing value substitution

CSub : TSub Δ [] → TEnv Δ → Set
CSub {Δ} σ* Γ = ESub σ* Γ ∅

ES←SC : {σ* : TSub Δ []} → CSub σ* Γ → ESub σ* Γ ∅
ES←SC = id

Csub : {Γ : TEnv Δ} {σ* : TSub Δ []} → CSub σ* Γ → Expr Δ Γ T → Expr [] ∅ (Tsub σ* T)
Csub {σ* = σ*} χ e = Esub σ* χ e

Cdrop : ∀ {l} {T : Type Δ l} → CSub σ* (T ◁ Γ) → CSub σ* Γ
Cdrop χ _ _ x = χ _ _ (there x)

Cextend : ∀ {l} {T : Type Δ l} → CSub σ* Γ → Value (Tsub σ* T) → CSub σ* (T ◁ Γ)
Cextend χ v _ _ here = v
Cextend χ v _ _ (there x) = χ _ _ x

Cextend-Eext : ∀ {l} {T : Type Δ l} → (χ : CSub σ* Γ) → (w : Value (Tsub σ* T)) → 
  Cextend {T = T} χ w ≡ Eextₛ _ χ (exp w)
Cextend-Eext {Δ = Δ} {σ* = σ*} {Γ = Γ} {T = T} χ w = fun-ext λ l → fun-ext λ T′ → fun-ext λ x → aux l T′ x
  where
    aux : (l : Level) (T′ : Type Δ l) (x : inn T′ (T ◁ Γ)) →
      (Cextend χ w) l _ x ≡ Eextₛ σ* χ (exp w) l _ x
    aux l _ here = refl
    aux l _ (there x) = refl

Cdrop-Cextend : ∀ {l} {σ* : TSub Δ []} {T : Type Δ l}
  → (χ : CSub σ* Γ) → (v : Value (Tsub σ* T))
  → Cdrop {l = l} {T = T} (Cextend {l = l} χ v) ≡ χ
Cdrop-Cextend {Δ = Δ} {Γ = Γ} {l = l} {T = T} χ v = fun-ext λ l′ → fun-ext λ T′ → fun-ext λ x → aux l′ T′ x
  where
    aux : ∀ l′ (T′ : Type Δ l′) → (x : inn T′ Γ) → Cdrop {T = T} (Cextend χ v) l′ _ x ≡ χ l′ _ x
    aux _ _ here = refl
    aux _ _ (there x) = refl
    aux _ _ (tskip x) = refl

Cdropt : {Γ : TEnv Δ} → CSub σ* (l ◁* Γ) → CSub (Tdropₛ σ*) Γ
Cdropt {σ* = σ*} χ l T x = subst Value (fusion-Tsub-Tren T (Twkᵣ Tidᵣ) σ*) (χ _ _ (tskip x))

Cextt : ∀{l} → CSub σ* Γ → (T′ : Type [] l) → CSub (Textₛ σ* T′) (l ◁* Γ)
Cextt {σ* = σ*} χ T′ _ _ (tskip {T = T} x) = subst Value (sym (σT≡TextₛσTwkT σ* T)) (χ _ _ x)

-- extended LR on environments

𝓖⟦_⟧ : (Γ : TEnv Δ) → (ρ : RelEnv Δ)
  → CSub (subst←RE ρ) Γ
  → let η = subst-to-env* (subst←RE ρ) [] in Env Δ Γ η → Set (levelEnv Γ)
𝓖⟦ ∅ ⟧ ρ χ γ = ⊤
𝓖⟦ T ◁ Γ ⟧ ρ χ γ = 𝓥⟦ T ⟧ ρ (χ _ _ here) (γ _ T here)
                 ∧ 𝓖⟦ Γ ⟧ ρ (Cdrop χ) (ENVdrop Γ _ γ)
𝓖⟦ l ◁* Γ ⟧ ρ χ γ = 𝓖⟦ Γ ⟧ (REdrop ρ) (Cdropt χ) (Gdropt (subst←RE ρ) γ)

----------------------------------------

subst-split-ƛ : 
    ∀ {t₁ t₁′ : Type [] l₁}
  → {t₂ t₂′ : Type [] l₂}
  → (eq : t₁ ⇒ t₂ ≡ t₁′ ⇒ t₂′)
  → (eq₁ : t₁ ≡ t₁′)
  → (eq₂ : t₂ ≡ t₂′)
  → (a : Expr [] (t₁ ◁ ∅) t₂)
  → subst (Expr [] ∅) eq (ƛ a) ≡ ƛ subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) eq₁ eq₂ a
subst-split-ƛ refl refl refl a = refl

subst-split-Λ :
  ∀ {tᵢ tᵢ′ : Type [ l ] l₁}
  → (eqₒ : `∀α l , tᵢ ≡ `∀α l , tᵢ′)
  → (eqᵢ : tᵢ ≡ tᵢ′)
  → (a : Expr [ l ] (l ◁* ∅) tᵢ)
  → subst (Expr [] ∅) eqₒ (Λ l ⇒ a) ≡ Λ l ⇒ subst (Expr [ l ] (l ◁* ∅)) eqᵢ a
subst-split-Λ refl refl a = refl

subst-split-⇓ :
  ∀ {Tₑ Tᵥ : Type [] l}
  → (e : Value Tₑ)
  → (v : Value Tᵥ)
  → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
  → subst Value Tₑ≡Tᵥ e ⇓ v
  → e ⇓ subst Value (sym Tₑ≡Tᵥ) v
subst-split-⇓ e v refl x = x

subst-split-eq-⇓ :
  ∀ {Tₑ Tᵥ : Type [] l}
  → (e : Value Tₑ)
  → (v : Value Tᵥ)
  → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
  → subst Value Tₑ≡Tᵥ e ⇓ v ≡ e ⇓ subst Value (sym Tₑ≡Tᵥ) v
subst-split-eq-⇓ e v refl = refl

subst-split-⇓′ :
  ∀ {Tₑ Tᵥ : Type [] l}
  → (e : Value Tₑ)
  → (v : Value Tᵥ)
  → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
  → e ⇓ subst Value (sym Tₑ≡Tᵥ) v
  → subst Value Tₑ≡Tᵥ e ⇓ v
subst-split-⇓′ e v refl x = x

subst-split-⇓₂ :
  ∀ {T T′ : Type [] l}
  → {e v : Value T}
  → (T≡T′ : T ≡ T′)
  → e ⇓ v
  → subst Value T≡T′ e ⇓ subst Value T≡T′ v
subst-split-⇓₂ refl e⇓v = e⇓v

subst-split-[]E :
  ∀ {T₁ T₁′ : Type [] l₁} {T₂ T₂′ : Type [] l₂}
  → (e : Expr [] (T₁ ◁ ∅) T₂) (e′ : Expr [] ∅ T₁′)
  → (eq₁ : T₁ ≡ T₁′) (eq₂ : T₂ ≡ T₂′)
  → subst Value eq₂ (e [ subst Value (sym eq₁) e′ ]E) ≡ (subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) eq₁ eq₂ e [ e′ ]E)
subst-split-[]E e e′ refl refl = refl

Tdrop-σ≡Twk∘σ : ∀ (σ* : TSub (l ∷ Δ₁) Δ₂) → Tdropₛ σ* ≡ Twkᵣ Tidᵣ ∘ᵣₛ σ*
Tdrop-σ≡Twk∘σ σ* = fun-ext₂ (λ x y → refl)


dist-subst'' :
  ∀ {ℓ ℓ' ℓ''} {a₁ a₂ : Set ℓ}
  → (arg : Set ℓ → Set ℓ')
  → (res : Set ℓ → Set ℓ'')
  → (f : ∀ {a} → arg a → res a)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (b₁≡b₂ : res a₁ ≡ res a₂)
  → (x : arg a₁) 
  → f {a₂} (subst id (cong arg a₁≡a₂) x) ≡ subst id b₁≡b₂ (f {a₁} x)
dist-subst'' _ _ _ refl refl _ = refl



dist-subst* :
  ∀ {ℓ ℓ' ℓ'' ℓ₁ ℓ₂} {Z : Set ℓ''} {B : Set ℓ'} {a₁ a₂ : Z → Set ℓ}
    {F : Set (ℓ ⊔ ℓ'') → Set ℓ₁} {G : B → Set ℓ₂}
  → (a→b : (Z → Set ℓ) → B)
  → (f : ∀ {h} → F ((z : Z) → h z) → G (a→b h))
  → (a₁≡a₂ : ∀ z → a₁ z ≡ a₂ z)
  → (b₁≡b₂ : a→b a₁ ≡ a→b a₂)
  → (x : F ((z : Z) → a₁ z)) 
  → f {a₂} (subst F (dep-ext a₁≡a₂) x) ≡ subst G b₁≡b₂ (f {a₁} x)
dist-subst* a→b f a₁≡a₂ b₁≡b₂ x
  with fun-ext a₁≡a₂
dist-subst* a→b f a₁≡a₂ refl x | refl = refl


dist-subst*-sym :
  ∀ {ℓ ℓ' ℓ'' ℓ₁ ℓ₂} {Z : Set ℓ''} {B : Set ℓ'} {a₁ a₂ : Z → Set ℓ}
    {F : Set (ℓ ⊔ ℓ'') → Set ℓ₁} {G : B → Set ℓ₂}
  → (a→b : (Z → Set ℓ) → B)
  → (f : ∀ {h} → F ((z : Z) → h z) → G (a→b h))
  → (a₁≡a₂ : ∀ z → a₂ z ≡ a₁ z)
  → (b₁≡b₂ : a→b a₁ ≡ a→b a₂)
  → (x : F ((z : Z) → a₁ z)) 
  → f {a₂} (subst F (sym (dep-ext a₁≡a₂)) x) ≡ subst G b₁≡b₂ (f {a₁} x)
dist-subst*-sym a→b f a₁≡a₂ b₁≡b₂ x
  with fun-ext a₁≡a₂
dist-subst*-sym a→b f a₁≡a₂ refl x | refl = refl


-- generalizing LRVwk and LRVst; otherwise the `∀α case does not fly (?)

{- <-- TypeSubstProperties -}
apply-env-var : (σ* : TSub Δ []) (x : l ∈ Δ) → apply-env (subst-to-env* σ* []) x ≡ ⟦ σ* l x ⟧ []
apply-env-var σ* here = refl
apply-env-var σ* (there x) = apply-env-var (Tdropₛ σ*) x

τ*∈Ren* : (τ* : TRen Δ₁ Δ₂) (σ* : TSub Δ₂ []) → TRen* τ* (subst-to-env* (τ* ∘ᵣₛ σ*) []) (subst-to-env* σ* [])
τ*∈Ren* τ* σ* here = apply-env-var σ* (τ* _ here)
τ*∈Ren* τ* σ* (there x) = τ*∈Ren* (Tdropᵣ τ*) σ* x

σ[T′]≡↑τ*∘ext-ext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l) → ∀ l′ x →  Textₛ (τ* ∘ᵣₛ subst←RE ρ) T′ l′ x ≡ (Tliftᵣ τ* l ∘ᵣₛ Textₛ (subst←RE ρ) T′) l′ x
σ[T′]≡↑τ*∘ext-ext ρ τ* T′ l′ here = refl
σ[T′]≡↑τ*∘ext-ext ρ τ* T′ l′ (there x) = refl

σ[T′]≡↑τ*∘ext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l) →  Textₛ (τ* ∘ᵣₛ subst←RE ρ) T′ ≡ (Tliftᵣ τ* l ∘ᵣₛ Textₛ (subst←RE ρ) T′)
σ[T′]≡↑τ*∘ext ρ τ* T′ = fun-ext₂ (σ[T′]≡↑τ*∘ext-ext ρ τ* T′)


{- --> TypeSubstProperties -}

