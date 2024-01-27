{-# OPTIONS --allow-unsolved-metas #-}
module ExprSubstProperties where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; [_])
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; _$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-subst;
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

-- splitting substitutions

subst-split-ƛ : 
    ∀ {Δ}{Γ : TEnv Δ}
  → {t₁ t₁′ : Type Δ l₁}
  → {t₂ t₂′ : Type Δ l₂}
  → (eq : t₁ ⇒ t₂ ≡ t₁′ ⇒ t₂′)
  → (eq₁ : t₁ ≡ t₁′)
  → (eq₂ : t₂ ≡ t₂′)
  → (a : Expr Δ (t₁ ◁ Γ) t₂)
  → subst (Expr Δ Γ) eq (ƛ a) ≡ ƛ subst₂ (λ T₁ T₂ → Expr Δ (T₁ ◁ Γ) T₂) eq₁ eq₂ a
subst-split-ƛ refl refl refl a = refl

subst-split-ƛ-∅ : 
    ∀ {t₁ t₁′ : Type [] l₁}
  → {t₂ t₂′ : Type [] l₂}
  → (eq : t₁ ⇒ t₂ ≡ t₁′ ⇒ t₂′)
  → (eq₁ : t₁ ≡ t₁′)
  → (eq₂ : t₂ ≡ t₂′)
  → (a : Expr [] (t₁ ◁ ∅) t₂)
  → subst (Expr [] ∅) eq (ƛ a) ≡ ƛ subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) eq₁ eq₂ a
subst-split-ƛ-∅ refl refl refl a = refl

subst-split-Λ :
  ∀ {tᵢ tᵢ′ : Type [ l ] l₁}
  → (eqₒ : `∀α l , tᵢ ≡ `∀α l , tᵢ′)
  → (eqᵢ : tᵢ ≡ tᵢ′)
  → (a : Expr [ l ] (l ◁* ∅) tᵢ)
  → subst (Expr [] ∅) eqₒ (Λ l ⇒ a) ≡ Λ l ⇒ subst (Expr [ l ] (l ◁* ∅)) eqᵢ a
subst-split-Λ refl refl a = refl

subst-split-· : ∀ {l₁ l₂} {T₁ T₁′ : Type Δ l₁}{T₂ T₂′ : Type Δ l₂}
  → (eq : T₁ ⇒ T₂ ≡ T₁′ ⇒ T₂′)
  → (eq₁ : T₁ ≡ T₁′)
  → (eq₂ : T₂ ≡ T₂′)
  → (e₁ : Expr Δ Γ (T₁ ⇒ T₂)) (e₂ : Expr Δ Γ T₁)
  → subst (Expr _ _) eq e₁ · subst (Expr _ _) eq₁ e₂ ≡ subst (Expr _ _) eq₂ (e₁ · e₂)
subst-split-· refl refl refl e₁ e₂ = refl

subst₂-subst-subst′ : ∀ {l la lb}
  → {A : Set la} {B : Set lb}
  → {a₁ a₂ : A} {b₁ b₂ : B}
  → (F : A → B → Set l)
  → (eq₁ : a₁ ≡ a₂)
  → (eq₂ : b₁ ≡ b₂)
  → (x : F a₁ b₁)
  → subst (λ b → F a₂ b) eq₂ (subst (λ a → F a b₁) eq₁ x) ≡ subst₂ F eq₁ eq₂ x
subst₂-subst-subst′ F refl refl x = refl

cong-const : ∀ {a b} {A : Set a}{B : Set b} {x y : A} {K : B} (eq : x ≡ y) → cong (λ z → K) eq ≡ refl
cong-const refl = refl



-- single substitution dissected

sub0 : Expr Δ Γ (Tsub Tidₛ T₁) → ESub Tidₛ (T₁ ◁ Γ) Γ
sub0 e′ = Eextₛ Tidₛ Eidₛ e′

sub0′ : Expr Δ Γ T₁ → ESub Tidₛ (T₁ ◁ Γ) Γ
sub0′ e′ = Eextₛ Tidₛ Eidₛ (subst (Expr _ _) (sym (TidₛT≡T _)) e′)

-- general equality of expression substitutions

_~_ : {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → Set
_~_ {Δ₁ = Δ₁} {Γ₁ = Γ₁} σ₁ σ₂ = ∀ l (T : Type Δ₁ l) → (x : inn T Γ₁) → σ₁ l T x ≡ σ₂ l T x

~-lift : ∀ {l} {T : Type Δ₁ l} {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → Eliftₛ {T = T} σ* σ₁ ~ Eliftₛ σ* σ₂
~-lift σ₁ σ₂ σ₁~σ₂ l T here = refl
~-lift σ₁ σ₂ σ₁~σ₂ l T (there x) = cong Ewk (σ₁~σ₂ l T x)

~-lift* : ∀ {l : Level} {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → (Eliftₛ-l {l = l} σ* σ₁) ~ Eliftₛ-l σ* σ₂
~-lift* σ₁ σ₂ σ₁~σ₂ l _ (tskip x) rewrite σ₁~σ₂ l _ x = refl


Esub~ : {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → (e : Expr Δ₁ Γ₁ T) → Esub σ* σ₁ e ≡ Esub σ* σ₂ e
Esub~ σ₁ σ₂ σ₁~σ₂ (# n) = refl
Esub~ σ₁ σ₂ σ₁~σ₂ (` x) = σ₁~σ₂ _ _ x
Esub~ σ₁ σ₂ σ₁~σ₂ (ƛ e) = cong ƛ_ (Esub~ _ _ (~-lift σ₁ σ₂ σ₁~σ₂) e)
Esub~ σ₁ σ₂ σ₁~σ₂ (e · e₁) = cong₂ _·_ (Esub~ σ₁ σ₂ σ₁~σ₂ e) (Esub~ σ₁ σ₂ σ₁~σ₂ e₁)
Esub~ σ₁ σ₂ σ₁~σ₂ (Λ l ⇒ e) = cong (Λ l ⇒_) (Esub~ _ _ (~-lift* {l = l} σ₁ σ₂ σ₁~σ₂) e)
Esub~ σ₁ σ₂ σ₁~σ₂ (e ∙ T′) rewrite Esub~ σ₁ σ₂ σ₁~σ₂ e = refl


-- general lax equality of expression substitutions

_~[_]~_ : {σ*₁ σ*₂ : TSub Δ₁ Δ₂} → (σ₁ : ESub σ*₁ Γ₁ Γ₂) (eqσ : σ*₁ ≡ σ*₂) (σ₂ : ESub σ*₂ Γ₁ Γ₂) → Set
_~[_]~_ {Δ₁ = Δ₁}{Δ₂ = Δ₂}{Γ₁ = Γ₁}{Γ₂ = Γ₂} σ₁ eqσ σ₂ =
  ∀ l (T : Type Δ₁ l) → (x : inn T Γ₁)
  → σ₁ l T x ≡ subst (Expr Δ₂ Γ₂) (cong (λ σ* → Tsub σ* T) (sym eqσ)) (σ₂ l T x)


Esub~~ : {σ*₁ σ*₂ : TSub Δ₁ Δ₂} → (eqσ : σ*₁ ≡ σ*₂) (σ₁ : ESub σ*₁ Γ₁ Γ₂) (σ₂ : ESub σ*₂ Γ₁ Γ₂) → σ₁ ~[ eqσ ]~ σ₂ → (e : Expr Δ₁ Γ₁ T)
  → Esub σ*₁ σ₁ e ≡ subst (Expr Δ₂ Γ₂) (cong (λ σ* → Tsub σ* T) (sym eqσ)) (Esub σ*₂ σ₂ e)
Esub~~ refl σ₁ σ₂ ~~ e = Esub~ σ₁ σ₂ ~~ e


--- want to prove
--- Goal: Esub σ* (Eextₛ σ* σ e′) e
---     ≡ (Esub σ* (Eliftₛ σ* σ) e) [ e′ ]E
---
--- at the level of substitutions
---
---     (Eextₛ σ* σ e′) ~  (Eliftₛ σ* σ) >>SS sub0 e′

-- subst-`-lem : ∀ {Γ : TEnv Δ} {T T′ : Type Δ l} (eq : T′ ≡ T) →
--     (` here) ≡ subst (λ T → Expr _ (T ◁ Γ) T) eq (` here)
-- subst-`-lem refl = refl

subst-`-lem : ∀ {Γ : TEnv Δ} {T T′ : Type Δ l} (eq₁ : (T ◁ Γ) ≡ (T′ ◁ Γ)) (eq₂ : T ≡ T′) →
    (` here) ≡ subst (λ Γ → Expr _ Γ T′) eq₁ (subst (λ T′′ → Expr _ (T ◁ Γ) T′′) eq₂ (` here))
subst-`-lem refl refl = refl

subst-`-lem₂ :
  ∀ {Γ : TEnv Δ} {T U V W : Type Δ l} {T′ U′ : Type Δ l₁}
    (eq₁ : V ≡ U) (eq₂ : W ≡ V) (eq₃ : T ≡ W) (eq₄ : T ≡ U) (eq₅ : (T′ ◁ Γ) ≡ (U′ ◁ Γ))
    (x : inn T Γ) →
  let sub₁ = subst (Expr _ (U′ ◁ Γ)) eq₁ in
  let sub₃ = subst (Expr _ (U′ ◁ Γ)) eq₂ in
  let sub₅' = subst (Expr _ (U′ ◁ Γ)) eq₃ in
  let sub₅ = subst (Expr _ (T′ ◁ Γ)) eq₄ in
  let sub₆ = subst (λ Γ → Expr _ Γ U) eq₅ in
  sub₁ (sub₃ (sub₅' (` there x))) ≡ sub₆ (sub₅ (` there x))
subst-`-lem₂ refl refl refl refl refl x = refl

EliftₛEidₛ≡Eidₛ : ∀ {T : Type Δ l}{Γ : TEnv Δ}
  → Eliftₛ {Γ₁ = Γ}{Γ₂ = Γ} {T = T} Tidₛ Eidₛ ~ subst (ESub Tidₛ (T ◁ Γ)) (cong (_◁ Γ) (sym (TidₛT≡T T))) (Eidₛ {Γ  = T ◁ Γ})
EliftₛEidₛ≡Eidₛ {Γ = Γ} l T here =
  let sub₁ = subst (λ Γ → Expr _ Γ (Tsub Tidₛ T)) (cong (_◁ Γ) (sym (TidₛT≡T T))) in
  let sub₂ = subst (λ T′ → Expr _ (T ◁ Γ) T′) (sym (TidₛT≡T T)) in
  let sub₃ = subst (ESub Tidₛ (T ◁ Γ)) (cong (_◁ Γ) (sym (TidₛT≡T T))) in
  begin
    (` here)
  ≡⟨ subst-`-lem (cong (_◁ Γ) (sym (TidₛT≡T T))) (sym (TidₛT≡T T)) ⟩
    sub₁ (sub₂ (` here))
  ≡⟨⟩
    sub₁ (Eidₛ l T here)
  ≡⟨ sym (dist-subst' {F = (ESub Tidₛ (T ◁ Γ))} {G = λ Γ → Expr _ Γ (Tsub Tidₛ T)}
                      id (λ σ → σ l T here)
                      (cong (_◁ Γ) (sym (TidₛT≡T T))) (cong (_◁ Γ) (sym (TidₛT≡T T))) Eidₛ ) ⟩
    (sub₃ Eidₛ) l T here
  ∎
EliftₛEidₛ≡Eidₛ {Γ = Γ} l T (there {T′ = T′} x) =
  let sub₁ = subst (Expr _ (Tsub Tidₛ T′ ◁ Γ)) (TidᵣT≡T (Tsub Tidₛ T)) in
  let sub₂ = subst (Expr _ Γ) (sym (TidₛT≡T T)) in
  let sub₃ = subst (Expr _ (Tsub Tidₛ T′ ◁ Γ)) (cong (Tren Tidᵣ) (sym (TidₛT≡T T))) in
  let sub₄ = subst (λ T₁ → inn T₁ Γ) (sym (TidᵣT≡T T)) in
  let sub₅ = subst (Expr _ (T′ ◁ Γ)) (sym (TidₛT≡T T)) in
  let sub₆ = subst (λ Γ → Expr _ Γ (Tsub Tidₛ T)) (cong (_◁ Γ) (sym (TidₛT≡T T′))) in
  let sub₇ = subst (ESub Tidₛ (T′ ◁ Γ)) (cong (_◁ Γ) (sym (TidₛT≡T T′))) in
  let sub₈ = subst (Expr _ (Tsub Tidₛ T′ ◁ Γ)) (sym (TidᵣT≡T T)) in
  begin
    Eliftₛ {T = T′} Tidₛ Eidₛ l T (there x)
  ≡⟨⟩
    Ewk (Eidₛ _ _ x)
  ≡⟨⟩
    sub₁ (Eren _ (Ewkᵣ Tidᵣ Eidᵣ) (sub₂ (` x)))
  ≡⟨ cong sub₁ (dist-subst' {F = Expr _ Γ} {G = Expr _ (Tsub Tidₛ T′ ◁ Γ)}
                            (Tren Tidᵣ) (Eren _ (Ewkᵣ Tidᵣ Eidᵣ))
                            (sym (TidₛT≡T T)) (cong (Tren Tidᵣ) (sym (TidₛT≡T T))) (` x)) ⟩
    sub₁ (sub₃ (Eren _ (Ewkᵣ Tidᵣ Eidᵣ) (` x)))
  ≡⟨⟩
    sub₁ (sub₃ (` there (sub₄ x)))
  ≡⟨ cong (λ ■ → sub₁ (sub₃ ■)) (dist-subst' {F = λ T₁ → inn T₁ Γ} {G = Expr _ (Tsub Tidₛ T′ ◁ Γ)}
                                             id (λ x → ` there x)
                                             (sym (TidᵣT≡T T)) (sym (TidᵣT≡T T)) x) ⟩
    sub₁ (sub₃ (sub₈ (` there x)))
  ≡⟨ subst-`-lem₂ (TidᵣT≡T (Tsub Tidₛ T))
                  (cong (Tren Tidᵣ) (sym (TidₛT≡T T)))
                  (sym (TidᵣT≡T T))
                  (sym (TidₛT≡T T))
                  (cong (_◁ Γ) (sym (TidₛT≡T T′)))
                  x ⟩
    sub₆ (sub₅ (` there x))
  ≡⟨⟩
    sub₆ (Eidₛ l T (there x))
  ≡⟨ sym (dist-subst' {F = ESub Tidₛ (T′ ◁ Γ)} {G = λ Γ → Expr _ Γ (Tsub Tidₛ T)}
                      id (λ σ → σ l T (there x))
                      (cong (_◁ Γ) (sym (TidₛT≡T T′))) (cong (_◁ Γ) (sym (TidₛT≡T T′))) Eidₛ ) ⟩
    (sub₇ Eidₛ) l T (there x)
  ∎

{-
    subst (λ Γ₁ → Expr _ Γ₁ (Tsub Tidₛ T))
      (cong (_◁ _) (sym (TidₛT≡T T)))
      (subst (Expr _ _) (sym (TidₛT≡T T)) (` here))
  ≡⟨⟩
    subst (λ Γ → Expr _ Γ (Tsub Tidₛ T)) (cong (_◁ _) (sym (TidₛT≡T T))) (Eidₛ l T here)
  ≡⟨ {!!} ⟩

-}

-- identity renaming and substituions

EliftᵣEidᵣ≡Eidᵣ : Eliftᵣ {Γ₁ = Γ}{T = T} Tidᵣ Eidᵣ ≡ {!Eidᵣ{Γ = T ◁ Γ}!}
EliftᵣEidᵣ≡Eidᵣ = {!Eliftᵣ!}

Eidᵣx≡x : ∀ {T : Type Δ l} (x : inn T Γ) → let rhs = subst (λ t → inn{l = l} t Γ) (sym (TidᵣT≡T _)) in Eidᵣ l T x ≡ rhs x
Eidᵣx≡x x = refl

Eidᵣe≡e : ∀ (e : Expr Δ Γ T) → Eren Tidᵣ Eidᵣ e ≡ subst (Expr _ _) (sym (TidᵣT≡T _)) e
Eidᵣe≡e (# n) = refl
Eidᵣe≡e {Γ = Γ} (`_ {l = l} x) =
  begin
    Eren Tidᵣ Eidᵣ (` x)
  ≡⟨ refl ⟩
    (` subst (λ t → inn t Γ) (sym (TidᵣT≡T _)) x)
  ≡⟨ dist-subst' {F = (λ t → inn t Γ)} {G = Expr _ _} id `_ (sym (TidᵣT≡T _)) (sym (TidᵣT≡T _)) x ⟩
    subst (Expr _ _) (sym (TidᵣT≡T _)) (` x)
  ∎
Eidᵣe≡e (ƛ e) =
  begin
    Eren Tidᵣ Eidᵣ (ƛ e)
  ≡⟨ refl ⟩
    (ƛ Eren Tidᵣ (Eliftᵣ Tidᵣ Eidᵣ) e)
  ≡⟨ {!!} ⟩
    (ƛ subst₂ (λ T₁ → Expr _ (T₁ ◁ _)) (sym (TidᵣT≡T _)) (sym (TidᵣT≡T _)) e)
  ≡⟨ sym (subst-split-ƛ (sym (TidᵣT≡T (_ ⇒ _))) (sym (TidᵣT≡T _)) (sym (TidᵣT≡T _)) e) ⟩
    subst (Expr _ _) (sym (TidᵣT≡T (_ ⇒ _))) (ƛ e)
  ∎
Eidᵣe≡e (e₁ · e₂) = {!!}
Eidᵣe≡e (Λ l ⇒ e) = {!!}
Eidᵣe≡e (e ∙ T′) = {!!}

Eidₛx≡x : ∀ {T : Type Δ l} (x : inn T Γ) → Esub Tidₛ Eidₛ (` x) ≡ subst (Expr _ _) (sym (TidₛT≡T _)) (` x)
Eidₛx≡x {T = T} x rewrite TidₛT≡T T = refl

Eidₛe≡e : ∀ (e : Expr Δ Γ T) → Esub Tidₛ Eidₛ e ≡ subst (Expr _ _) (sym (TidₛT≡T _)) e
Eidₛe≡e (# n) = refl
Eidₛe≡e {T = T} (` x) rewrite TidₛT≡T T = refl
Eidₛe≡e (ƛ e) =
  begin
    Esub Tidₛ Eidₛ (ƛ e)
  ≡⟨⟩
    (ƛ Esub Tidₛ (Eliftₛ Tidₛ Eidₛ) e)
  ≡⟨ cong ƛ_ (begin
               Esub Tidₛ (Eliftₛ Tidₛ Eidₛ) e
             ≡⟨ Esub~ (Eliftₛ Tidₛ Eidₛ) {!Eidₛ!} EliftₛEidₛ≡Eidₛ e ⟩
               {!!}
             ≡⟨ {!!} ⟩
               subst₂ (λ T₁ → Expr _ (T₁ ◁ _)) (sym (TidₛT≡T _)) (sym (TidₛT≡T _))
                 e
             ∎) ⟩
    (ƛ
      subst₂ (λ T₁ → Expr _ (T₁ ◁ _)) (sym (TidₛT≡T _)) (sym (TidₛT≡T _))
      e)
  ≡⟨ sym (subst-split-ƛ (sym (TidₛT≡T (_ ⇒ _))) (sym (TidₛT≡T _)) (sym (TidₛT≡T _)) e ) ⟩
    subst (Expr _ _) (sym (TidₛT≡T (_ ⇒ _))) (ƛ e)
  ∎
Eidₛe≡e (e₁ · e₂) =
  begin
    Esub Tidₛ Eidₛ (e₁ · e₂)
  ≡⟨⟩
    (Esub Tidₛ Eidₛ e₁ · Esub Tidₛ Eidₛ e₂)
  ≡⟨ cong₂ _·_ (Eidₛe≡e e₁) (Eidₛe≡e e₂) ⟩
    (subst (Expr _ _) (sym (TidₛT≡T (_ ⇒ _))) e₁ ·
      subst (Expr _ _) (sym (TidₛT≡T _)) e₂)
  ≡⟨ subst-split-· (sym (TidₛT≡T (_ ⇒ _))) (sym (TidₛT≡T _)) (sym (TidₛT≡T _)) e₁ e₂ ⟩
    subst (Expr _ _) (sym (TidₛT≡T _)) (e₁ · e₂)
  ∎
Eidₛe≡e (Λ l ⇒ e) = {!!}
Eidₛe≡e (e ∙ T′) = {!!}


-- composition of expression substitutions and renamings

_>>SR_ : ∀ {Δ₁}{Δ₂}{Δ₃}{σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ESub σ* Γ₁ Γ₂ → ERen ρ* Γ₂ Γ₃ → ESub (σ* ∘ₛᵣ ρ*) Γ₁ Γ₃
_>>SR_ {Δ₃ = Δ₃}{σ* = σ*}{ρ* = ρ*}{Γ₃ = Γ₃} σ ρ l T x
  = subst (Expr Δ₃ Γ₃) (assoc-ren-sub T σ* ρ*) (Eren ρ* ρ (σ _ _ x))

_>>RS_ : ∀ {Δ₁}{Δ₂}{Δ₃}{ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ERen ρ* Γ₁ Γ₂ → ESub σ* Γ₂ Γ₃ → ESub (ρ* ∘ᵣₛ σ*) Γ₁ Γ₃
_>>RS_ {Δ₃ = Δ₃}{ρ* = ρ*}{σ* = σ*}{Γ₃ = Γ₃} ρ σ l T x
  = subst (Expr Δ₃ Γ₃) (assoc-sub-ren T ρ* σ*) (σ _ _ (ρ _ _ x))

_>>SS_ : ∀ {Δ₁}{Δ₂}{Δ₃}{σ₁* : TSub Δ₁ Δ₂} {σ₂* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ESub σ₁* Γ₁ Γ₂ → ESub σ₂* Γ₂ Γ₃ → ESub (σ₁* ∘ₛₛ σ₂*) Γ₁ Γ₃
_>>SS_ {Δ₃ = Δ₃}{σ₁* = σ₁*}{σ₂* = σ₂*}{Γ₃ = Γ₃} σ₁ σ₂ l T x
  = subst (Expr Δ₃ Γ₃) (assoc-sub-sub T  σ₁* σ₂*) (Esub _ σ₂ (σ₁ _ _ x))

_>>RR_ : ∀ {Δ₁}{Δ₂}{Δ₃}{ρ₁* : TRen Δ₁ Δ₂} {ρ₂* : TRen Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ERen ρ₁* Γ₁ Γ₂ → ERen ρ₂* Γ₂ Γ₃ → ERen (ρ₁* ∘ᵣᵣ ρ₂*) Γ₁ Γ₃
_>>RR_ {Δ₃ = Δ₃}{ρ₁* = ρ₁*}{ρ₂* = ρ₂*}{Γ₃ = Γ₃} ρ₁ ρ₂ l T x
  = subst (λ T → inn T Γ₃) (assoc-ren-ren T ρ₁* ρ₂*) (ρ₂ _ _ (ρ₁ _ _ x))

-- postulated because of substitution hell 
-- needs approx. 28 lemmas (we actually have two types of liftings here so thats why its even more) 
-- exactly of the structure as seen in `TypeSubstProperties` section `composition of type substitutions`
-- of which all of them require shuffling `subst`s
-- tbd :))
postulate
  Eassoc-sub-ren : 
      {ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (ρ : ERen ρ* Γ₁ Γ₂) (σ : ESub σ* Γ₂ Γ₃)
    → let lhs = Esub σ* σ (Eren ρ* ρ e) in
      let rhs = Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e in
      subst (Expr Δ₃ Γ₃) (assoc-sub-ren T ρ* σ*) lhs ≡ rhs
  Eassoc-ren-ren : 
      {ρ₁* : TRen Δ₁ Δ₂}{ρ₂* : TRen Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (ρ₁ : ERen ρ₁* Γ₁ Γ₂) → (ρ₂ : ERen ρ₂* Γ₂ Γ₃)
    → let lhs = Eren ρ₂* ρ₂ (Eren ρ₁* ρ₁ e) in
      let rhs = Eren (ρ₁* ∘ᵣᵣ ρ₂*) (ρ₁ >>RR ρ₂) e in
      subst (Expr Δ₃ Γ₃) (assoc-ren-ren T ρ₁* ρ₂*) lhs ≡ rhs
  Eassoc-ren-sub : 
      {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃)
    → let lhs = Eren ρ* ρ (Esub σ* σ e) in
      let rhs = Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e in
      subst (Expr Δ₃ Γ₃) (assoc-ren-sub T σ* ρ*) lhs ≡ rhs
  Eassoc-sub-sub : 
      {σ₁* : TSub Δ₁ Δ₂}{σ₂* : TSub Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (σ₁ : ESub σ₁* Γ₁ Γ₂) → (σ₂ : ESub σ₂* Γ₂ Γ₃)
    → let lhs = Esub σ₂* σ₂ (Esub σ₁* σ₁ e) in
      let rhs = Esub (σ₁* ∘ₛₛ σ₂*) (σ₁ >>SS σ₂) e in
      subst (Expr Δ₃ Γ₃) (assoc-sub-sub T σ₁* σ₂*) lhs ≡ rhs
      
  

-- outline can be seen here: 

-- ---- specialized ----
-- subst-split : ∀ {Δ}
--   → {ℓ : Level}
--   → (F : {l : Level} (t : Type Δ l) → Set ℓ)
--   → (f : ∀ {t₁ : Type Δ l₁}{t₂ : Type Δ l₂} → F (t₁ ⇒ t₂) → F t₁ → F t₂)
--   → {t₁ t₁′ : Type Δ l₁}{t₂ t₂′ : Type Δ l₂}
--   → (eq : (t₁ ⇒ t₂)  ≡ (t₁′ ⇒ t₂′)) (eq₁ : t₁ ≡ t₁′) (eq₂ : t₂ ≡ t₂′)
--   → (x₁ : F (t₁ ⇒ t₂)) (x₂ : F t₁)
--   → subst F eq₂ (f x₁ x₂) ≡ f (subst F eq x₁) (subst F eq₁ x₂)
-- subst-split F f refl refl refl x₁ x₂ = refl
-- 
-- 
-- Eassoc-sub↑-sub↑ :
--     {σ₁* : TSub Δ₁ Δ₂}{σ₂* : TSub Δ₂ Δ₃}
--   → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
--   → {T : Type Δ₁ l}
--   → {T′ : Type Δ₁ l′}
--   → (e : Expr Δ₁ (T′ ◁  Γ₁) T)
--   → (σ₁ : ESub σ₁* Γ₁ Γ₂) → (σ₂ : ESub σ₂* Γ₂ Γ₃)
--   → let lhs = Esub σ₂* (Eliftₛ {T = Tsub σ₁* T′} σ₂* σ₂) (Esub σ₁* (Eliftₛ σ₁* σ₁) e) in
--     let rhs = Esub (σ₁* ∘ₛₛ σ₂*) (Eliftₛ {T = T′} (σ₁* ∘ₛₛ σ₂*) (σ₁ >>SS σ₂)) e  in
--     subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*) (subst (Expr Δ₃ _) (assoc-sub-sub T σ₁* σ₂*) lhs) ≡ rhs
-- 
-- Esub↑-dist-∘ₛₛ : {σ₁* : TSub Δ₁ Δ₂}{σ₂* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃} 
--     (T : Type Δ₁ l)
--     (σ₁ : ESub σ₁* Γ₁ Γ₂) → (σ₂ : ESub σ₂* Γ₂ Γ₃) 
--   → Eliftₛ {T = T} σ₁* σ₁ >>SS Eliftₛ σ₂* σ₂ ≡ 
--     subst ((λ T → ESub _ _ (T ◁ Γ₃))) (sym (assoc-sub-sub T σ₁* σ₂*)) (Eliftₛ {T = T} (σ₁* ∘ₛₛ σ₂*) (σ₁ >>SS σ₂))
-- Esub↑-dist-∘ₛₛ {σ₁* = σ₁*} {σ₂* = σ₂*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} T σ₁ σ₂ = fun-ext λ l → fun-ext λ T₁ → fun-ext λ x → aux l T₁ x
--   where aux : ∀ l T₁ x → (Eliftₛ σ₁* σ₁ >>SS Eliftₛ σ₂* σ₂) l T₁ x ≡ subst (λ T₂ → ESub (σ₁* ∘ₛₛ σ₂*) (T ◁ Γ₁) (T₂ ◁ Γ₃))
--                         (sym (assoc-sub-sub T σ₁* σ₂*)) (Eliftₛ (σ₁* ∘ₛₛ σ₂*) (σ₁ >>SS σ₂)) l T₁ x
--         aux l T here = {!   !} -- subst-elim
--         aux l T (there x) = {!   !} -- needs Eassoc-sub-ren and Eassoc-ren-sub
-- 
-- Eassoc-sub↑-sub↑ {Δ₃ = Δ₃} {σ₁* = σ₁*} {σ₂* = σ₂*} {Γ₃ = Γ₃} {T = T} {T′ = T′} e σ₁ σ₂ = 
--   let ≡* = Eassoc-sub-sub e (Eliftₛ σ₁* σ₁) (Eliftₛ σ₂* σ₂) in
--   begin 
--     subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*) (subst (Expr Δ₃ _) (assoc-sub-sub T σ₁* σ₂*) 
--           (Esub σ₂* (Eliftₛ σ₂* σ₂) (Esub σ₁* (Eliftₛ σ₁* σ₁) e)))
--   ≡⟨ cong (subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*)) ≡* ⟩
--     subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*) 
--       (Esub (σ₁* ∘ₛₛ σ₂*) (Eliftₛ σ₁* σ₁ >>SS Eliftₛ σ₂* σ₂) e)
--   ≡⟨ cong (λ σ → subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*) (Esub (σ₁* ∘ₛₛ σ₂*) σ e)) (Esub↑-dist-∘ₛₛ T′ σ₁ σ₂) ⟩
--     subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*) 
--       (Esub (σ₁* ∘ₛₛ σ₂*)
--         (subst ((λ T → ESub _ _ (T ◁ Γ₃))) (sym (assoc-sub-sub T′ σ₁* σ₂*)) (Eliftₛ (σ₁* ∘ₛₛ σ₂*) (σ₁ >>SS σ₂))) 
--       e)
--   ≡⟨ {!   !} ⟩ -- subst elim
--     Esub (σ₁* ∘ₛₛ σ₂*) (Eliftₛ (σ₁* ∘ₛₛ σ₂*) (σ₁ >>SS σ₂)) e
--   ∎ 
-- Eassoc-sub-sub (# n) σ₁ σ₂ = refl
-- Eassoc-sub-sub (` x) σ₁ σ₂ = refl
-- Eassoc-sub-sub (ƛ e) σ₁ σ₂ = {!  !} -- use Eassoc-sub↑-sub↑
-- Eassoc-sub-sub {σ₁* = σ₁*} {σ₂* = σ₂*} (_·_ {T = T}{T′ = T′} e₁ e₂) σ₁ σ₂ =
--   begin
--     subst (Expr _ _) (assoc-sub-sub T′ σ₁* σ₂*)
--       (Esub σ₂* σ₂ (Esub σ₁* σ₁ e₁) · Esub σ₂* σ₂ (Esub σ₁* σ₁ e₂))
--   ≡⟨ subst-split (Expr _ _) _·_ (assoc-sub-sub (T ⇒ T′) σ₁* σ₂*) (assoc-sub-sub T σ₁* σ₂*) (assoc-sub-sub T′ σ₁* σ₂*) (Esub σ₂* σ₂ (Esub σ₁* σ₁ e₁)) (Esub σ₂* σ₂ (Esub σ₁* σ₁ e₂)) ⟩
--       (subst (Expr _ _) (assoc-sub-sub (T ⇒ T′) σ₁* σ₂*) (Esub σ₂* σ₂ (Esub σ₁* σ₁ e₁)) ·
--        subst (Expr _ _) (assoc-sub-sub T σ₁* σ₂*) (Esub σ₂* σ₂ (Esub σ₁* σ₁ e₂)))
--   ≡⟨ cong₂ _·_ (Eassoc-sub-sub e₁ σ₁ σ₂) (Eassoc-sub-sub e₂ σ₁ σ₂) ⟩
--     (Esub (σ₁* ∘ₛₛ σ₂*) (σ₁ >>SS σ₂) e₁ ·
--        Esub (σ₁* ∘ₛₛ σ₂*) (σ₁ >>SS σ₂) e₂)
--   ∎
-- Eassoc-sub-sub (Λ l ⇒ e) σ₁ σ₂ = {!  !} -- needs Eassoc-sub↑-sub↑-l
-- Eassoc-sub-sub (e ∙ T′) σ₁ σ₂ = {!!}


TSub-id-right : ∀ (σ* : TSub Δ₁ Δ₂) → (σ* ∘ₛₛ Tidₛ) ≡ σ*
TSub-id-right {Δ₁ = Δ₁} σ* = fun-ext₂ aux
  where
    aux : (l : Level) (x : l ∈ Δ₁) → (σ* ∘ₛₛ Tidₛ) l x ≡ σ* l x
    aux l x = TidₛT≡T (σ* l x)

TSub-id-left :  ∀ (σ* : TSub Δ₁ Δ₂) → (Tidₛ ∘ₛₛ σ*) ≡ σ*
TSub-id-left {Δ₁} σ* = fun-ext₂ λ x y → refl
  where
    aux : (l : Level) (x : l ∈ Δ₁) → (Tidₛ ∘ₛₛ σ*) l x ≡ σ* l x
    aux l x = refl

-- (Eidₛ l (Tren Tidᵣ T) (subst (λ T₂ → inn T₂ e.Γ) (sym (TidᵣT≡T T)) x))
-- ≡
-- (Esub Tidₛ Eidₛ (Eidₛ l T x))

wklift~id : {e : Expr Δ Γ (Tsub Tidₛ T′)} → (Ewkᵣ Tidᵣ Eidᵣ >>RS sub0 {T₁ = T′} e) ~ (Eidₛ >>SS Eidₛ)
wklift~id {e = e} l T′ x = begin 
    subst (Expr _ _) (assoc-sub-ren T′ Tidᵣ Tidₛ) 
      (((Eidₛ l (Tren Tidᵣ T′)) (subst (λ T → inn T _) (sym (TidᵣT≡T T′)) x)))
  ≡⟨ cong₂ (subst (Expr _ _)) refl refl ⟩
    subst (Expr _ _) (assoc-sub-sub T′ Tidₛ Tidₛ) (Esub Tidₛ Eidₛ (Eidₛ l T′ x))
  ∎

-- σT≡TextₛσTwkT : {T′ : Type Δ₂ l′} (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l) → Tsub (Textₛ σ T′) (Twk T) ≡ Tsub σ T
-- σT≡TextₛσTwkT {T′ = T′} σ T = begin 
--     Tsub (Textₛ σ _) (Twk T)
--   ≡⟨ assoc-sub-ren T (Twkᵣ Tidᵣ) (Textₛ σ _) ⟩
--     Tsub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ σ T′) T
--   ≡⟨ sym (assoc-sub-sub T _ σ) ⟩
--     Tsub σ (Tsub Tidₛ T)
--   ≡⟨ cong (λ T → Tsub σ T) (TidₛT≡T T) ⟩
--     Tsub σ T
--   ∎
ext-wk-e≡e : ∀ {Δ}{Γ}{l′}{T′ : Type Δ l′}{l}{T : Type Δ l} → 
  (e′ : Expr Δ Γ (Tsub Tidₛ T′)) (e : Expr Δ Γ T) → 
  Esub Tidₛ (sub0 {T₁ = T′} e′) (Ewk e) ≡ subst (Expr Δ Γ) (sym (TidₛT≡T T)) e
ext-wk-e≡e {T′ = T′} {T = T} e′ e = 
  let asr = Eassoc-sub-ren e (Ewkᵣ Tidᵣ Eidᵣ) (sub0 {T₁ = T′} e′) in
  let ass = sym (Eassoc-sub-sub e Eidₛ Eidₛ) in
  begin 
    Esub Tidₛ (sub0 {T₁ = T′} e′) (subst (Expr _ _) (TidᵣT≡T T) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e))
  ≡⟨ dist-subst' {F = Expr _ _} {G = Expr _ _} (λ T → Tsub Tidₛ T) (Esub Tidₛ (sub0 {T₁ = T′} e′)) (TidᵣT≡T T) (assoc-sub-ren T Tidᵣ Tidₛ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e) ⟩ 
    (subst (Expr _ _) (assoc-sub-ren T Tidᵣ Tidₛ) (Esub Tidₛ (sub0 {T₁ = T′} e′) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e)))
  ≡⟨ asr ⟩ 
    Esub Tidₛ (Ewkᵣ Tidᵣ Eidᵣ >>RS sub0 {T₁ = T′} e′) e
  ≡⟨ Esub~ (Ewkᵣ Tidᵣ Eidᵣ >>RS sub0 {T₁ = T′} e′) (Eidₛ >>SS Eidₛ) (wklift~id {T′ = T′} {e = e′}) e ⟩
    Esub Tidₛ (Eidₛ >>SS Eidₛ) e
  ≡⟨ ass ⟩ 
    subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ)
      (Esub Tidₛ Eidₛ (Esub Tidₛ Eidₛ e))
  ≡⟨ cong (subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ)) (Eidₛe≡e (Esub Tidₛ Eidₛ e)) ⟩ 
    subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ) (subst (Expr _ _) (sym (TidₛT≡T _)) (Esub Tidₛ Eidₛ e))
  ≡⟨ cong (λ e → subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ) (subst (Expr _ _) (sym (TidₛT≡T _)) e)) (Eidₛe≡e e) ⟩
    subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ) (subst (Expr _ _) (sym (TidₛT≡T (Tsub Tidₛ T))) (subst (Expr _ _) (sym (TidₛT≡T T)) e)) 
  ≡⟨ elim-subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ) (sym (TidₛT≡T (Tsub Tidₛ T))) (subst (Expr _ _) (sym (TidₛT≡T T)) e) ⟩ 
    subst (Expr _ _) (sym (TidₛT≡T T)) e
  ∎
-- ext=lift∘single~
Eext-Elift~ : ∀ {l}{Δ₁}{Δ₂} {σ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l} (σ : ESub σ* Γ₁ Γ₂) (e′ : Expr Δ₂ Γ₂ (Tsub σ* T))
  → let r = Eliftₛ {T = T} σ* σ >>SS sub0 (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) e′) in
    let subᵣ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
    Eextₛ {T = T} σ* σ e′ ~ subᵣ r
Eext-Elift~ {.l₁} {Δ₁} {Δ₂} {σ* = σ*} {Γ₁} {Γ₂} {T = T} σ e′ l₁ (.T) here =
  let sub₁ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
  let sub₁′ = subst (Expr Δ₂ Γ₂) (cong (λ σ* → Tsub σ* T) (TSub-id-right σ*)) in
  let sub₂ = subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) in
  let sub₃ = subst (Expr Δ₂ Γ₂) (assoc-sub-sub T  σ* Tidₛ) in
  begin
    e′
      ≡⟨ sym (elim-subst₃ (Expr Δ₂ Γ₂) (cong (λ τ* → Tsub τ* T) (TSub-id-right σ*)) (assoc-sub-sub T  σ* Tidₛ) (sym (TidₛT≡T (Tsub σ* T))) e′) ⟩
    sub₁′ (sub₃ (sub₂ e′))
      ≡⟨⟩
    sub₁′ (sub₃ (Esub {T = Tsub σ* T} _ (sub0 (sub₂ e′)) (` here)))
      ≡⟨⟩
    sub₁′ (sub₃ (Esub {T = Tsub σ* T} _ (sub0 (sub₂ e′)) ((Eliftₛ {T = T} σ* σ) l₁ _ here)))
      ≡⟨⟩
    sub₁′ ((Eliftₛ {T = T} σ* σ >>SS sub0 (sub₂ e′)) l₁ _ here)
      ≡⟨ sym (dist-subst' {F = (λ a → ESub a (T ◁ Γ₁) Γ₂)} {G = Expr Δ₂ Γ₂}
                          (λ τ* → Tsub τ* T)
                          (λ f → f l₁ _ here)
                          (TSub-id-right σ*)
                          (cong (λ σ*₁ → Tsub σ*₁ T) (TSub-id-right σ*))
                          (Eliftₛ σ* σ >>SS sub0 (subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) e′)))
       ⟩
    sub₁ (Eliftₛ σ* σ >>SS sub0 (sub₂ e′)) l₁ _ here 
  ∎
Eext-Elift~ {l} {Δ₁} {Δ₂} {σ* = σ*} {Γ₁} {Γ₂} {T = T} σ e′ l₁ T₁ (there x) =
  let sub₁ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
  let sub₁′ = subst (Expr Δ₂ Γ₂) (cong (λ τ* → Tsub τ* T₁) (TSub-id-right σ*)) in
  let sub₁″ = subst (λ τ* → Expr Δ₂ Γ₂ (Tsub τ* T₁)) (TSub-id-right σ*) in
  let sub₂ = subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) in
  let sub₃ = subst (Expr Δ₂ Γ₂) (assoc-sub-sub T₁ σ* Tidₛ) in
  sym $ begin
    sub₁ (Eliftₛ σ* σ >>SS sub0 (sub₂ e′)) l₁ _ (there x)
      ≡⟨ dist-subst' {F = (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂)} {G = (λ τ* → Expr Δ₂ Γ₂ (Tsub τ* T₁))} id (λ τ → τ l₁ _ (there x)) (TSub-id-right σ*) (TSub-id-right σ*) (Eliftₛ σ* σ >>SS sub0 (sub₂ e′)) ⟩
    sub₁″ ((Eliftₛ {T = T} σ* σ >>SS sub0 (sub₂ e′)) l₁ _ (there x))
      ≡⟨ sym (subst-cong (Expr Δ₂ Γ₂) (λ τ* → Tsub τ* T₁) (TSub-id-right σ*) ((Eliftₛ {T = T} σ* σ >>SS sub0 (sub₂ e′)) l₁ _ (there x))) ⟩ 
    sub₁′ ((Eliftₛ {T = T} σ* σ >>SS sub0 (sub₂ e′)) l₁ _ (there x))
      ≡⟨⟩
    sub₁′ ((Eliftₛ {T = T} σ* σ >>SS sub0 (sub₂ e′)) l₁ _ (there x))
      ≡⟨⟩
    sub₁′ (sub₃ (Esub _ (sub0 ( sub₂ e′)) (Eliftₛ {T = T} σ* σ l₁ _ (there x))))
      ≡⟨ cong sub₁′ (cong sub₃ (ext-wk-e≡e {l′ = l} (sub₂ e′) (σ l₁ _ x))) ⟩
    sub₁′ (sub₃ ((subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T _)) (σ l₁ _ x))))
      ≡⟨ elim-subst₃ (Expr Δ₂ Γ₂)
           (cong (λ τ* → Tsub τ* T₁) (TSub-id-right σ*))
           (assoc-sub-sub T₁ σ* Tidₛ) (sym (TidₛT≡T (Tsub σ* T₁))) (σ l₁ _ x)
       ⟩
    σ l₁ _ x
  ∎

-- ext=lift∘single
Eext-Elift :   ∀ {l}{Δ₁}{Δ₂} {σ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l} {Tₑ : Type Δ₁ l₁} (σ : ESub σ* Γ₁ Γ₂) (e′ : Expr Δ₂ Γ₂ (Tsub σ* T)) (e : Expr Δ₁ (T ◁ Γ₁) Tₑ)
  → let r = Eliftₛ {T = T} σ* σ >>SS sub0 (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) e′) in
    let subᵣ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
    Esub σ* (Eextₛ {T = T} σ* σ e′) e ≡ Esub σ* (subᵣ r) e
Eext-Elift {σ* = σ*}{Γ₁}{Γ₂} {T = T} σ e′ e = Esub~ (Eextₛ σ* σ e′)
                                                (subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*)
                                                 (Eliftₛ {T = T} σ* σ >>SS
                                                  sub0 (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) e′)))
                                                (Eext-Elift~ σ e′) e

-- Eext-Elift-l~ : ∀ {l}{Δ₁}{Δ₂} {σ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l} (σ : ESub σ* Γ₁ Γ₂) (e′ : Expr Δ₂ Γ₂ (Tsub σ* T))
--   → let r = Eliftₛ {T = T} σ* σ >>SS sub0 (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) e′) in
--     let subᵣ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
--     Eextₛ {T = T} σ* σ e′ ~ subᵣ r
-- Eext-Elift-l~ = {!   !}

Elift-l-[]≡Eext : {Γ : TEnv Δ} (l l′ : Level) (T′ : Type [] l) (T : Type (l ∷ Δ) l′) (τ* : TSub Δ []) (σ : ESub τ* Γ ∅) (e : Expr (l ∷ Δ) (l ◁* Γ) T)
  → let lhs = ((Esub (Tliftₛ τ* l) (Eliftₛ-l τ* σ) e) [ T′ ]ET) in
    let rhs = (Esub (Textₛ τ* T′) (Eextₛ-l τ* σ) e) in
    lhs ≡ subst (Expr [] ∅) (sym (σ↑T[T′]≡TextₛσT′T τ* T′ T)) rhs
Elift-l-[]≡Eext l l′ T′ T τ* σ e =
  begin
    (Esub (Tliftₛ τ* l) (Eliftₛ-l τ* σ) e [ T′ ]ET)
  ≡⟨ (let eq = Eassoc-sub-sub e (Eliftₛ-l τ* σ) (Eextₛ-l Tidₛ Eidₛ)
      in subst-swap (assoc-sub-sub T (Tliftₛ τ* l) (Textₛ Tidₛ T′))
           (Esub (Textₛ Tidₛ T′) (Eextₛ-l Tidₛ Eidₛ)
            (Esub (Tliftₛ τ* l) (Eliftₛ-l τ* σ) e))
           (Esub (Tliftₛ τ* l ∘ₛₛ Textₛ Tidₛ T′)
            (Eliftₛ-l τ* σ >>SS Eextₛ-l Tidₛ Eidₛ) e)
           eq) ⟩
    subst (Expr [] ∅)
      (sym (assoc-sub-sub T (Tliftₛ τ* l) (Textₛ Tidₛ T′)))
      (Esub (Tliftₛ τ* l ∘ₛₛ Textₛ Tidₛ T′)
       (Eliftₛ-l τ* σ >>SS Eextₛ-l Tidₛ Eidₛ) e)
  ≡⟨  {! !} ⟩
    subst (Expr [] ∅) (sym (σ↑T[T′]≡TextₛσT′T τ* T′ T))
      (Esub (Tliftₛ τ* l ∘ₛₛ Textₛ Tidₛ T′) (subst (λ ρ → ESub ρ _ ∅) (sym (Tliftₛ∘Textₛ _ τ* T′)) (Eextₛ-l τ* σ)) {!e!})
  ≡⟨ cong (subst (Expr [] ∅) (sym (σ↑T[T′]≡TextₛσT′T τ* T′ T))) (cong (λ K → K e) (dcong₂ Esub (Tliftₛ∘Textₛ _ τ* T′) refl)) ⟩
    subst (Expr [] ∅) (sym (σ↑T[T′]≡TextₛσT′T τ* T′ T))
      (Esub (Textₛ τ* T′) (Eextₛ-l τ* σ) e)
  ∎

-- let eqσ : Twkᵣ Tidᵣ ∘ᵣₛ Textₛ Tidₛ T′ ≡ Tidσ
equal-Esub-wk>>lift : ∀ {Γ : TEnv []} (T′ : Type [] l)
  → _~_ {Γ₁ = Γ} ((λ z z₁ → tskip) >>RS Eextₛ-l {T = T′} Tidₛ Eidₛ) Eidₛ
equal-Esub-wk>>lift T′ l T x =
  begin
    ((λ z z₁ → tskip) >>RS Eextₛ-l Tidₛ Eidₛ) l T x
  ≡⟨⟩
    subst (Expr [] _)
      (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))
      (subst (Expr [] _)
       (sym
        (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))
         (trans (sym (assoc-sub-sub T (λ z → `_) (λ z → `_)))
          (trans (cong (Tsub (λ z → `_)) (TidₛT≡T T)) refl))))
       (Eidₛ l T x))
  ≡⟨ subst-subst (sym
        (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))
         (trans (sym (assoc-sub-sub T (λ z → `_) (λ z → `_)))
          (trans (cong (Tsub (λ z → `_)) (TidₛT≡T T)) refl))))
          {(assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))}
          {Eidₛ l T x} ⟩
    subst (Expr [] _)
      (trans
       (sym
        (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))
         (trans (sym (assoc-sub-sub T (λ z → `_) (λ z → `_)))
          (trans (cong (Tsub (λ z → `_)) (TidₛT≡T T)) refl))))
       (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′)))
      (Eidₛ l T x)
  ≡⟨ subst-irrelevant
      (trans
       (sym
        (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))
         (trans (sym (assoc-sub-sub T (λ z → `_) (λ z → `_)))
          (trans (cong (Tsub (λ z → `_)) (TidₛT≡T T)) refl))))
       (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′)))
       refl
       (Eidₛ l T x) ⟩
    Eidₛ l T x
  ∎

-- let eqσ : Tliftₛ τ* l ∘ₛₛ Textₛ Tidₛ T′ ≡ Textₛ τ* T′
equal-ESub : ∀ {Γ : TEnv Δ} (T′ : Type [] l) (τ* : TSub Δ []) (σ : ESub τ* Γ ∅)
  → (Eliftₛ-l τ* σ >>SS Eextₛ-l Tidₛ Eidₛ) ~[ Tliftₛ∘Textₛ l τ* T′ ]~ Eextₛ-l τ* σ
equal-ESub T′ τ* σ l .(Twk _) (tskip {T = T} x) =
  begin
    (Eliftₛ-l τ* σ >>SS Eextₛ-l Tidₛ Eidₛ) l (Twk T) (tskip x)
  ≡⟨ refl ⟩
    subst (Expr _ _) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (Esub _ (Eextₛ-l Tidₛ Eidₛ) (Eliftₛ-l τ* σ _ _ (tskip x)))
  ≡⟨ refl ⟩
    subst (Expr _ _) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
    (Esub _ (Eextₛ-l Tidₛ Eidₛ) (subst (Expr _ _) (sym (σ↑-TwkT≡Twk-σT τ* T)) (Ewk-l (σ _ _ x))))
  ≡⟨ cong (subst (Expr _ _) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′)))
          (dist-subst' {F = Expr _ _} {G = Expr [] ∅} (λ T₁ → T₁ [ T′ ]T) (Esub _ (Eextₛ-l Tidₛ Eidₛ))
                   (sym (σ↑-TwkT≡Twk-σT τ* T))
                   (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
                   (Ewk-l (σ _ _ x))) ⟩
    subst (Expr _ _) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
    (subst (Expr [] ∅) (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
      (Esub _ (Eextₛ-l Tidₛ Eidₛ) (Ewk-l (σ _ _ x))))
  ≡⟨ cong
       (λ E →
          subst (Expr _ _)
          (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
          (subst (Expr [] ∅)
           (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T))) E))
       (subst-swap (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′))
          (Esub _ (Eextₛ-l Tidₛ Eidₛ) (Ewk-l (σ _ _ x)))
          (Esub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ Tidₛ T′)
           ((λ z z₁ → tskip) >>RS Eextₛ-l Tidₛ Eidₛ) (σ l T x))
          (Eassoc-sub-ren (σ l T x) (λ _ _ → tskip) (Eextₛ-l Tidₛ Eidₛ)))
    ⟩
    subst (Expr [] ∅)
      (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (subst (Expr [] ∅)
       (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
       (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (Esub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ Tidₛ T′)
         ((λ z z₁ → tskip) >>RS Eextₛ-l Tidₛ Eidₛ) (σ l T x))))
  ≡⟨ cong (λ E → subst (Expr [] ∅)
      (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (subst (Expr [] ∅)
       (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
       (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        E)))
     (Esub~ ((λ z z₁ → tskip) >>RS Eextₛ-l Tidₛ Eidₛ) Eidₛ (equal-Esub-wk>>lift T′) (σ l T x))
   ⟩
    subst (Expr [] ∅)
      (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (subst (Expr [] ∅)
       (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
       (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (Esub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ Tidₛ T′) Eidₛ (σ l T x))))
  ≡⟨ cong (λ E → subst (Expr [] ∅)
      (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (subst (Expr [] ∅)
       (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
       (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        E)))
        (Eidₛe≡e (σ l T x)) ⟩
    subst (Expr [] ∅)
      (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (subst (Expr [] ∅)
       (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
       (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub τ* T))) (σ l T x))))
  ≡⟨ subst-subst (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
     {(assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))}
     {(subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub τ* T))) (σ l T x)))} ⟩
    subst (Expr [] ∅)
      (trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T))) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′)))
      (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub τ* T))) (σ l T x)))
  ≡⟨ subst-subst (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
         {(trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T))) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′)))}
         {(subst (Expr [] ∅) (sym (TidₛT≡T (Tsub τ* T))) (σ l T x))} ⟩
    subst (Expr [] ∅)
      (trans
       (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
       (trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
        (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))))
      (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub τ* T))) (σ l T x))
  ≡⟨ subst-subst (sym (TidₛT≡T (Tsub τ* T)))
                  {(trans
       (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
       (trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
        (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))))}
                   {(σ l T x)} ⟩
    subst (Expr [] ∅)
      (trans (sym (TidₛT≡T (Tsub τ* T)))
       (trans
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
         (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′)))))
      (σ l T x)
  ≡⟨ subst-irrelevant
       (trans (sym (TidₛT≡T (Tsub τ* T)))
       (trans
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (σ↑-TwkT≡Twk-σT τ* T)))
         (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′)))))
       (trans (sym (σT≡TextₛσTwkT τ* T))
       (cong (λ σ* → Tsub σ* (Twk T)) (sym (Tliftₛ∘Textₛ _ τ* T′))))
       (σ l T x) ⟩
    subst (Expr [] ∅)
      (trans (sym (σT≡TextₛσTwkT τ* T))
       (cong (λ σ* → Tsub σ* (Twk T)) (sym (Tliftₛ∘Textₛ _ τ* T′))))
      (σ l T x)
  ≡⟨ sym (subst-subst (sym (σT≡TextₛσTwkT τ* T))
           {(cong (λ σ* → Tsub σ* (Twk T)) (sym (Tliftₛ∘Textₛ _ τ* T′)))}
           {(σ _ _ x)}) ⟩
    subst (Expr [] ∅) (cong (λ σ* → Tsub σ* (Twk T)) (sym (Tliftₛ∘Textₛ _ τ* T′)))
      (subst (Expr _ _) (sym (σT≡TextₛσTwkT τ* T)) 
        (σ _ _ x))
  ≡⟨ refl ⟩
    subst (Expr [] ∅)
      (cong (λ σ* → Tsub σ* (Twk T)) (sym (Tliftₛ∘Textₛ _ τ* T′)))
      (Eextₛ-l τ* σ l (Twk T) (tskip x))
  ∎

----------------------------------------------------------------------

-- semantic renamings on expression
ERen* : {ρ* : TRen Δ₁ Δ₂} (TRen* : TRen* ρ* η₁ η₂) → (ρ : ERen ρ* Γ₁ Γ₂) → (γ₁ : Env Δ₁ Γ₁ η₁) → (γ₂ : Env Δ₂ Γ₂ η₂) → Setω
ERen* {Δ₁ = Δ₁} {Γ₁ = Γ₁} {ρ*} Tren* ρ γ₁ γ₂ = ∀ {l} {T : Type Δ₁ l} → 
  (x : inn T Γ₁) → γ₂ _ _ (ρ _ _ x) ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (γ₁ _ _ x)
-- γ* l (Tren Tidᵣ T₁) (Eidᵣ l T₁ x) ≡
--       subst id (sym (Tren*-preserves-semantics (Tren*-id η) T₁))
--       (γ* l T₁ x)
Ewk∈ERen* : ∀ {T : Type Δ l} (γ : Env Δ Γ η) (⟦e⟧ : ⟦ T ⟧ η) →  
  ERen* (Tren*-id η) (Ewkᵣ {T = T} Tidᵣ Eidᵣ) γ (extend γ ⟦e⟧) 
Ewk∈ERen* {η = η} γ* ⟦e⟧ {T = T} x = begin 
    γ* _ (Tren Tidᵣ T) (subst (λ T → inn T _) (sym (TidᵣT≡T T)) x)
  ≡⟨ {!   !} ⟩
    subst id (sym (Tren*-preserves-semantics (Tren*-id η) T)) (γ* _ T x)
  ∎ 
ERen*-lift : ∀ {T : Type Δ₁ l} {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} → 
  (⟦e⟧ : ⟦ Tren ρ* T ⟧ η₂) →
  (Tren* : TRen* ρ* η₁ η₂) → 
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  ERen* Tren* (Eliftᵣ {T = T} _ ρ) (extend γ₁ (subst id (Tren*-preserves-semantics Tren* T) ⟦e⟧)) (extend γ₂ ⟦e⟧)
ERen*-lift {η₁ = η₁} {η₂ = η₂} {T = T} {ρ* = ρ*} ⟦e⟧ Tren* Eren* here 
  rewrite Tren*-preserves-semantics {ρ* = ρ*} {η₁ = η₁} {η₂ = η₂} Tren* T = refl
ERen*-lift {η₁ = η₁} {η₂ = η₂} {ρ* = ρ*} ⟦e⟧ Tren* Eren* {T = T} (there x) = Eren* x

ERen*-lift-l : ∀ {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} → 
  (⟦α⟧ : Set l) →
  (Tren* : TRen* ρ* η₁ η₂) → 
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  ERen* (Tren*-lift ⟦α⟧ Tren*) (Eliftᵣ-l _ ρ) (extend-tskip {⟦α⟧  = ⟦α⟧} γ₁) (extend-tskip {⟦α⟧  = ⟦α⟧} γ₂)
ERen*-lift-l {Γ₂ = Γ₂} {η₁ = η₁} {η₂ = η₂} {l = l₁} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} ⟦α⟧ Tren* Eren* {l} (tskip {T = T} x) =
  let eq* = Eren* x in 
  let eq = sym (Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) (Twk T)) in 
  let eq' = sym (Tren*-preserves-semantics (wkᵣ∈Ren* η₁ ⟦α⟧) T) in 
  let eq'' = sym (Tren*-preserves-semantics {ρ* = ρ*} {η₂ = η₂} Tren* T) in
  let eq₁ = cong (λ T₁ → inn T₁ (l₁ ◁* Γ₂)) (sym (↑ρ-TwkT≡Twk-ρT T ρ*)) in
  let eq₂ = (cong (λ T → ⟦ T ⟧ (⟦α⟧ ∷ η₂)) (sym (↑ρ-TwkT≡Twk-ρT T ρ*))) in
  let eq′ = trans (sym eq'') (trans eq' eq) in
  begin 
    extend-tskip γ₂ _ (Tren (Tliftᵣ ρ* l₁) (Twk T)) (subst id eq₁ (tskip (ρ _ T x)))
  ≡⟨ {! !} ⟩ -- dist subst -- 
    subst id eq₂ (extend-tskip γ₂ _ (Twk (Tren ρ* T)) (tskip (ρ _ _ x)))
  ≡⟨⟩ 
    subst id eq₂ (subst id (sym (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {η₂} {⟦α⟧ ∷ η₂} (wkᵣ∈Ren* η₂ ⟦α⟧) (Tren ρ* T))) (γ₂ l (Tren ρ* T) (ρ _ _ x)))
  ≡⟨ subst-shuffle′′′′ ((γ₂ l (Tren ρ* T) (ρ _ _ x))) eq₂ ((sym (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {η₂} {⟦α⟧ ∷ η₂} (wkᵣ∈Ren* η₂ ⟦α⟧) (Tren ρ* T)))) eq′ refl ⟩ 
    subst id eq′ (γ₂ l (Tren ρ* T) (ρ _ _ x))
  ≡⟨ cong (subst id eq′) eq* ⟩
    subst id eq′ (subst id eq'' (γ₁ l T x))
  ≡⟨ subst-shuffle′′′′ (γ₁ l T x) eq′ eq'' eq eq' ⟩
    subst id eq (subst id eq' (γ₁ l T x))
  ∎

Eren*-preserves-semantics : ∀ {T : Type Δ₁ l} {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} →
  (Tren* : TRen* ρ* η₁ η₂) →
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  (e : Expr Δ₁ Γ₁ T) → 
  E⟦ Eren ρ* ρ e ⟧ η₂ γ₂ ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (E⟦ e ⟧ η₁ γ₁)
Eren*-preserves-semantics Tren* Eren* (# n) = refl
Eren*-preserves-semantics Tren* Eren* (` x) = Eren* x
Eren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {T = .(T ⇒ T′)} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (ƛ_ {T = T} {T′} e) = fun-ext λ ⟦e⟧ →
  let eq* = Eren*-preserves-semantics {ρ = Eliftᵣ ρ* ρ} {γ₂ = extend γ₂ ⟦e⟧} Tren* (ERen*-lift {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} ⟦e⟧ Tren* Eren*) e  in
  let eq = sym (Tren*-preserves-semantics Tren* (T ⇒ T′)) in
  let eq₁ = Tren*-preserves-semantics Tren* T in
  let eq₂ = sym (Tren*-preserves-semantics Tren* T′) in
  begin 
    E⟦ Eren ρ* (Eliftᵣ ρ* ρ) e ⟧ η₂ (extend γ₂ ⟦e⟧)
  ≡⟨ eq* ⟩
    subst id eq₂ (E⟦ e ⟧ η₁ (extend γ₁ (subst id eq₁ ⟦e⟧)))
  ≡⟨ dist-subst (λ ⟦e⟧ → E⟦ e ⟧ η₁ (extend γ₁ ⟦e⟧)) eq₁ eq eq₂ ⟦e⟧ ⟩
    subst id eq (λ ⟦e⟧ → E⟦ e ⟧ η₁ (extend γ₁ ⟦e⟧)) ⟦e⟧
  ∎
Eren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (_·_ {T = T} {T′ = T′} e₁ e₂) =
  let eq₁* = Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* e₁ in
  let eq₂* = Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* e₂ in
  let eq = sym (Tren*-preserves-semantics Tren* (T ⇒ T′)) in
  let eq₁ = sym (Tren*-preserves-semantics Tren* T) in
  let eq₂ = sym (Tren*-preserves-semantics Tren* T′) in
  begin 
    E⟦ Eren _ ρ e₁ ⟧ η₂ γ₂ (E⟦ Eren _ ρ e₂ ⟧ η₂ γ₂)
  ≡⟨ cong₂ (λ x y → x y) eq₁* eq₂* ⟩
    (subst id eq (E⟦ e₁ ⟧ η₁ γ₁)) (subst id eq₁ (E⟦ e₂ ⟧ η₁ γ₁))
  ≡⟨ dist-subst′ (E⟦ e₁ ⟧ η₁ γ₁) eq₁ eq eq₂ (E⟦ e₂ ⟧ η₁ γ₁) ⟩
    subst id eq₂ (E⟦ e₁ ⟧ η₁ γ₁ (E⟦ e₂ ⟧ η₁ γ₁))
  ∎
Eren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {T = .(`∀α l , T)} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (Λ_⇒_ l {T = T} e) = fun-ext λ ⟦α⟧ → 
  let eq* = Eren*-preserves-semantics {ρ = Eliftᵣ-l _ ρ} {γ₁ = extend-tskip {⟦α⟧ = ⟦α⟧} γ₁} {γ₂ = extend-tskip {⟦α⟧ = ⟦α⟧} γ₂} 
            (Tren*-lift {η₁ = η₁} ⟦α⟧ Tren*) (ERen*-lift-l ⟦α⟧ Tren* Eren*) e in 
  let eq₁ = (λ { ⟦α⟧ → Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) T }) in
  let eq = sym (dep-ext eq₁) in 
  let eq₂ = sym (Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) T) in
  begin 
    E⟦ Eren _ (Eliftᵣ-l _ ρ) e ⟧ (⟦α⟧ ∷ η₂) (extend-tskip γ₂)
  ≡⟨ eq* ⟩
    subst id eq₂ (E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁))
  ≡⟨ dist-subst′′ ⟦α⟧ (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁)) eq (λ ⟦α⟧ → sym (eq₁ ⟦α⟧)) ⟩
    subst id eq (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁)) ⟦α⟧
  ∎
Eren*-preserves-semantics {Δ₂ = Δ₂} {Γ₂ = Γ₂} {η₁ = η₁} {η₂ = η₂} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (_∙_ {l} {T = T} e T′) = 
  let eq* = Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* e in 
  let eq*' = Tren*-preserves-semantics {ρ* = ρ*} {η₁ = η₁} {η₂ = η₂} Tren* T′ in 
  let eq = (sym (ρT[T′]≡ρT[ρ↑T′] ρ* T T′)) in 
  let eq' = (sym (Tren*-preserves-semantics Tren* (T [ T′ ]T))) in 
  let eq'''' = λ α → Tren*-preserves-semantics {ρ* = Tliftᵣ ρ* l} {η₁ = α ∷ η₁} {η₂ = α ∷ η₂} (Tren*-lift α Tren*) T in
  let eq'' = (sym (dep-ext eq'''')) in
  let eq''' = sym (Tren*-preserves-semantics {ρ* = Tliftᵣ ρ* l} {η₁ = ⟦ Tren ρ* T′ ⟧ η₂ ∷ η₁} {η₂ = ⟦ Tren ρ* T′ ⟧ η₂ ∷ η₂} (Tren*-lift (⟦ Tren ρ* T′ ⟧ η₂) Tren*) T) in
  let eq₁ = (cong (λ T → ⟦ T ⟧ η₂) eq) in
  let eq₂ = sym (Tsingle-subst-preserves η₂ (Tren ρ* T′) (Tren (Tliftᵣ ρ* l) T)) in
  let eq₃ = sym (Tsingle-subst-preserves η₁ T′ T) in
  let eq₄ = cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym eq*') in
  let eq₅ = (cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym (Tren*-preserves-semantics Tren* T′))) in
  begin 
    E⟦ subst (Expr Δ₂ Γ₂) eq (Eren _ ρ e ∙ Tren ρ* T′) ⟧ η₂ γ₂
  ≡⟨ dist-subst' {F = Expr Δ₂ Γ₂} {G = id} (λ T → ⟦ T ⟧ η₂) (λ e → E⟦ e ⟧ η₂ γ₂) eq eq₁ (Eren ρ* ρ e ∙ Tren ρ* T′) ⟩
    subst id eq₁ (E⟦ (Eren ρ* ρ e ∙ Tren ρ* T′) ⟧ η₂ γ₂)
  ≡⟨⟩
    subst id eq₁ (subst id eq₂ (E⟦ (Eren ρ* ρ e) ⟧ η₂ γ₂ (⟦ Tren ρ* T′ ⟧ η₂)))
  ≡⟨ cong (λ e → subst id eq₁ (subst id eq₂ (e (⟦ Tren ρ* T′ ⟧ η₂)))) eq* ⟩
    subst id eq₁ (subst id eq₂ ((subst id eq'' (E⟦ e ⟧ η₁ γ₁)) (⟦ Tren ρ* T′ ⟧ η₂)))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂ x)) 
     (sym (dist-subst′′ (⟦ Tren ρ* T′ ⟧ η₂) (E⟦ e ⟧ η₁ γ₁) eq'' λ α → sym (eq'''' α))) ⟩
    subst id eq₁ (subst id eq₂  (subst id eq''' ((E⟦ e ⟧ η₁ γ₁) (⟦ Tren ρ* T′ ⟧ η₂))))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂  (subst id eq''' x))) 
     (dist-subst′′′ (⟦ Tren ρ* T′ ⟧ η₂) (⟦ T′ ⟧ η₁) (E⟦ e ⟧ η₁ γ₁) (Tren*-preserves-semantics Tren* T′) eq₅) ⟩
    subst id eq₁ (subst id eq₂  (subst id eq''' (subst id eq₄ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))))
  ≡⟨ subst-elim′′′ ((E⟦ e ⟧ η₁ γ₁) (⟦ T′ ⟧ η₁)) eq₁ eq₂ eq''' eq₄ eq' eq₃ ⟩
    subst id eq' (subst id eq₃ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))
  ≡⟨⟩
    subst id eq' (E⟦ e ∙ T′ ⟧ η₁ γ₁)  
  ∎

-- semantic substituions on expressions


subst-to-env : {σ* : TSub Δ₁ Δ₂} → ESub σ* Γ₁ Γ₂ → Env Δ₂ Γ₂ η₂ → Env Δ₁ Γ₁ (subst-to-env* σ* η₂)
subst-to-env {η₂ = η₂} {σ* = σ*} σ γ₂ _ T x = subst id (subst-preserves σ* T) (E⟦ σ _ _ x ⟧ η₂ γ₂)

subst-to-env-dist-extend : {T : Type Δ₁ l} {σ* : TSub Δ₁ Δ₂} 
  → (γ₂ : Env Δ₂ Γ₂ η₂)
  → (σ : ESub σ* Γ₁ Γ₂) 
  → (⟦e⟧ : ⟦ Tsub σ* T ⟧ η₂)
  → subst-to-env (Eliftₛ {T = T} σ* σ) (extend {Γ = Γ₂} γ₂ ⟦e⟧) ≡ω extend (subst-to-env σ γ₂) (subst id (subst-preserves {η₂ = η₂} σ* T) ⟦e⟧)
subst-to-env-dist-extend {η₂ = η₂} {σ* = σ*} γ₂ σ ⟦e⟧ = fun-extω λ l → fun-ext λ T → fun-ext λ where 
  here → refl
  (there {T′ = T′} x) → cong (subst id (subst-preserves {η₂ = η₂} σ* T)) {! (Eren*-preserves-semantics {T = Tsub σ* T} {γ₂ = γ₂} (Tren*-id η₂) (Ewk∈ERen* {T = Tsub σ* T′} γ₂ ⟦e⟧) (σ l T x))  !}

subst-to-env-dist-extend-l : {σ* : TSub Δ₁ Δ₂} 
  → (γ₂ : Env Δ₂ Γ₂ η₂)
  → (σ : ESub σ* Γ₁ Γ₂) 
  → (⟦α⟧ : Set l)
  → subst-to-env (Eliftₛ-l {l = l} σ* σ) (extend-tskip {⟦α⟧ = ⟦α⟧} γ₂) ≡ω 
    substωω (Env _ _) (congωω (⟦α⟧ ∷_) (symω (subst-to-env*-wk σ* ⟦α⟧ η₂))) (extend-tskip {⟦α⟧ = ⟦α⟧} (subst-to-env σ γ₂))
subst-to-env-dist-extend-l {η₂ = η₂} {σ* = σ*} γ₂ σ ⟦α⟧ = fun-extω λ l → fun-ext λ T → fun-ext λ where 
  (tskip x) → {!   !}

Esubst-preserves : ∀ {T : Type Δ₁ l} {η₂ : Env* Δ₂} {γ₂ : Env Δ₂ Γ₂ η₂} {σ* : TSub Δ₁ Δ₂} 
  → (σ : ESub σ* Γ₁ Γ₂) (e : Expr Δ₁ Γ₁ T)
  → E⟦ Esub σ* σ e ⟧ η₂ γ₂ ≡ subst id (sym (subst-preserves σ* T)) (E⟦ e ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂))
Esubst-preserves σ (# n) = refl
Esubst-preserves {l = l} {T = T } {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (` x) =  
  sym (elim-subst id (sym (subst-preserves σ* T)) (subst-preserves σ* T) (E⟦ σ l _ x ⟧ η₂ γ₂))
Esubst-preserves {T = T ⇒ T′} {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (ƛ e) = fun-ext λ ⟦e⟧ → 
  let eq* = Esubst-preserves {η₂ = η₂} {γ₂ = extend γ₂ ⟦e⟧} (Eliftₛ σ* σ) e in 
  let eq = sym (subst-preserves {η₂ = η₂} σ* (T ⇒ T′)) in 
  let eq₁ = subst-preserves {η₂ = η₂} σ* T in
  let eq₂ = (sym (subst-preserves {η₂ = η₂} σ* T′)) in
  begin 
    E⟦ Esub σ* (Eliftₛ σ* σ) e ⟧ η₂ (extend γ₂ ⟦e⟧)
  ≡⟨ eq* ⟩
    subst id eq₂ (E⟦ e ⟧ (subst-to-env* σ* η₂) (subst-to-env (Eliftₛ σ* σ) (extend γ₂ ⟦e⟧)))
  ≡⟨ congωl (λ γ → subst id eq₂ (E⟦ e ⟧ (subst-to-env* σ* η₂) γ)) (subst-to-env-dist-extend γ₂ σ ⟦e⟧) ⟩
    subst id eq₂ (E⟦ e ⟧ (subst-to-env* σ* η₂) (extend (subst-to-env σ γ₂) (subst id eq₁ ⟦e⟧)))
  ≡⟨ dist-subst (λ ⟦e⟧ → E⟦ e ⟧ (subst-to-env* σ* η₂) (extend (subst-to-env σ γ₂) ⟦e⟧)) eq₁ eq eq₂ ⟦e⟧ ⟩
    subst id eq (λ ⟦e⟧ → E⟦ e ⟧ (subst-to-env* σ* η₂) (extend (subst-to-env σ γ₂) ⟦e⟧)) ⟦e⟧
  ∎ 
Esubst-preserves {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (_·_ {T = T} {T′ = T′} e₁ e₂) = 
  let eq₁* = Esubst-preserves {η₂ = η₂} {γ₂ = γ₂} σ e₁ in
  let eq₂* = Esubst-preserves {η₂ = η₂} {γ₂ = γ₂} σ e₂ in 
  let eq = sym (subst-preserves {η₂ = η₂} σ* (T ⇒ T′)) in 
  let eq₁ = sym (subst-preserves {η₂ = η₂} σ* T′) in
  let eq₂ = sym (subst-preserves {η₂ = η₂} σ* T) in
  begin 
    E⟦ Esub σ* σ e₁ ⟧ η₂ γ₂ (E⟦ Esub σ* σ e₂ ⟧ η₂ γ₂)
  ≡⟨ cong₂ (λ x y → x y) eq₁* eq₂* ⟩
    (subst id eq (E⟦ e₁ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂))) 
    (subst id eq₂ (E⟦ e₂ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)))
  ≡⟨ dist-subst′ (E⟦ e₁ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)) eq₂ eq eq₁ (E⟦ e₂ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)) ⟩
    subst id eq₁ (E⟦ e₁ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂) (E⟦ e₂ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)))
  ∎ 
Esubst-preserves {T = T′} {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (Λ_⇒_ l {T = T} e) = fun-ext λ ⟦α⟧ → 
  let eq* = Esubst-preserves {η₂ = ⟦α⟧ ∷ η₂} {γ₂ = extend-tskip γ₂} (Eliftₛ-l σ* σ) e in 
  let eq₁ = (λ { ⟦α⟧ → trans (subst-preserves (Tliftₛ σ* l) T) (congωl (λ H → ⟦ T ⟧ (⟦α⟧ ∷ H)) (subst-to-env*-wk σ* ⟦α⟧ η₂)) }) in
  let eq = sym (dep-ext eq₁) in
  let eq′ = sym (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (Tliftₛ σ* l) T) in
  let eq′′ = sym (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (Tdropₛ (Tliftₛ σ* l)) T′) in
  begin 
    E⟦ Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) e ⟧ (⟦α⟧ ∷ η₂) (extend-tskip γ₂)
  ≡⟨ eq* ⟩
    subst id eq′ (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* (Twkₛ σ*) (⟦α⟧ ∷ η₂)) (subst-to-env (Eliftₛ-l σ* σ) (extend-tskip γ₂)))
  ≡⟨ congωl (λ γ → subst id eq′ (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* (Twkₛ σ*) (⟦α⟧ ∷ η₂)) γ)) (subst-to-env-dist-extend-l γ₂ σ ⟦α⟧) ⟩
    subst id eq′ (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* (Twkₛ σ*) (⟦α⟧ ∷ η₂)) 
      (substωω (Env _ _) (congωω (⟦α⟧ ∷_) (symω (subst-to-env*-wk σ* ⟦α⟧ η₂))) (extend-tskip {⟦α⟧ = ⟦α⟧} (subst-to-env σ γ₂))))
  ≡⟨ {!   !} ⟩
    {!   !}
  ≡⟨ {! cong  !} ⟩
    subst id (sym (eq₁ ⟦α⟧)) (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂)))
  ≡⟨ dist-subst′′ ⟦α⟧ (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂))) eq (λ ⟦α⟧ → sym (eq₁ ⟦α⟧)) ⟩
    subst id eq (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂))) ⟦α⟧
  ∎ 
Esubst-preserves {Δ₂ = Δ₂} {Γ₂ = Γ₂} {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (_∙_ {l} {T = T} e T′) = 
  let η₁ = (subst-to-env* σ* η₂) in
  let γ₁ = (subst-to-env σ γ₂) in
  let eq* = Esubst-preserves {γ₂ = γ₂} σ e in 
  let eq*' = subst-preserves {η₂ = η₂} σ* T′ in 
  let eq = (sym (σT[T′]≡σ↑T[σT'] σ* T T′)) in 
  let eq' = (sym (subst-preserves {η₂ = η₂} σ* (T [ T′ ]T))) in  
  let eq'''' = λ α → trans (subst-preserves {η₂ = α ∷ η₂} (Tliftₛ σ* l) T) (congωl (λ η → ⟦ T ⟧ (α ∷ η)) (subst-to-env*-wk σ* α η₂)) in
  let eq''''′ = λ α → trans (congωl (λ η → ⟦ T ⟧ (α ∷ η)) (symω (subst-to-env*-wk σ* α η₂))) (sym (subst-preserves (Tliftₛ σ* l) T)) in
  let eq'' = (sym (dep-ext eq'''')) in
  let eq''' = sym (subst-preserves {η₂ = ⟦ Tsub σ* T′ ⟧ η₂ ∷ η₂} (Tliftₛ σ* l) T) in
  let eq''''' = trans (congωl (λ η → ⟦ T ⟧ (⟦ Tsub σ* T′ ⟧ η₂ ∷ η)) (symω (subst-to-env*-wk σ* (⟦ Tsub σ* T′ ⟧ η₂) η₂))) eq''' in
  let eq₁ = (cong (λ T → ⟦ T ⟧ η₂) eq) in
  let eq₂ = sym (Tsingle-subst-preserves η₂ (Tsub σ* T′) (Tsub (Tliftₛ σ* l) T)) in
  let eq₃ = (sym (Tsingle-subst-preserves η₁ T′ T)) in 
  let eq₄ = cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym eq*') in
  let eq₅ = (cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym (subst-preserves {η₂ = η₂} σ* T′))) in
  begin 
    E⟦ subst (Expr Δ₂ Γ₂) eq (Esub σ* σ e ∙ Tsub σ* T′) ⟧ η₂ γ₂
  ≡⟨ dist-subst' {F = Expr Δ₂ Γ₂} {G = id} (λ T → ⟦ T ⟧ η₂) (λ e → E⟦ e ⟧ η₂ γ₂) eq eq₁ (Esub σ* σ e ∙ Tsub σ* T′) ⟩
    subst id eq₁ (subst id eq₂ (E⟦ Esub σ* σ e ⟧ η₂ γ₂ (⟦ Tsub σ* T′ ⟧ η₂)))
  ≡⟨ cong (λ e → subst id eq₁ (subst id eq₂ (e (⟦ Tsub σ* T′ ⟧ η₂)))) eq* ⟩
    subst id eq₁ (subst id eq₂ ((subst id eq'' (E⟦ e ⟧ η₁ γ₁)) (⟦ Tsub σ* T′ ⟧ η₂)))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂ x)) 
     (sym (dist-subst′′ (⟦ Tsub σ* T′ ⟧ η₂) (E⟦ e ⟧ η₁ γ₁) eq'' eq''''′)) ⟩ 
    subst id eq₁ (subst id eq₂  (subst id eq''''' ((E⟦ e ⟧ η₁ γ₁) (⟦ Tsub σ* T′ ⟧ η₂))))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂  (subst id eq''''' x))) 
     (dist-subst′′′ (⟦ Tsub σ* T′ ⟧ η₂) (⟦ T′ ⟧ η₁) (E⟦ e ⟧ η₁ γ₁) (subst-preserves σ* T′) eq₅) ⟩
    subst id eq₁ (subst id eq₂  (subst id eq''''' (subst id eq₄ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))))
  ≡⟨ subst-elim′′′ ((E⟦ e ⟧ η₁ γ₁) (⟦ T′ ⟧ η₁)) eq₁ eq₂ eq''''' eq₄ eq' eq₃ ⟩
    subst id eq' (subst id eq₃ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))
  ≡⟨⟩
    subst id eq' (E⟦ e ∙ T′ ⟧ η₁ γ₁)
  ∎         
   
