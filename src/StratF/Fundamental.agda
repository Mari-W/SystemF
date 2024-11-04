{-# OPTIONS --allow-unsolved-metas #-}
module StratF.Fundamental where

--open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Function using (_∘_; id; case_of_; _|>_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; subst; subst₂; resp₂; cong-app; icong;
        subst-subst; subst-∘; subst-application; subst-application′; subst-sym-subst; subst-subst-sym; -- Properties
        module ≡-Reasoning)
open ≡-Reasoning

open import StratF.LogicalRelation
open import StratF.BigStep
open import StratF.Evaluation
open import StratF.ExpSubstPropertiesSem
open import StratF.ExpSubstProperties
open import StratF.ExpSubstitution
open import StratF.Expressions
open import StratF.ExpEnvironments
open import StratF.TypeSubstProperties
open import StratF.TypeSubstPropertiesSem
open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.TypeEnvironments
open import StratF.Util.Extensionality


-- semantic soundness

--! SemanticSoundness {
Soundness : (e : Exp {Δ} Γ {l} T) → Set (E-level e)
Soundness {Δ = Δ} {Γ = Γ} {T = T} e = ∀ (δ : ⟦ Δ ⟧𝓓) →
  let τ* = 𝓓Tsub δ; η = ⟦ η₀ ⟧TETₛ τ*  in
  (χ : VSub (⟦ Γ ⟧EEₛ τ*) Γ₀) (γ : ⟦ Γ ⟧EE η) →

  ⟦ Γ ⟧𝓖 δ χ γ  → 𝓔⟦ T ⟧ δ (Esub* τ* (VS⇒ES χ) e) (⟦ e ⟧E γ)

--! }

-- fundamental theorem

--! AdequacyType
Adequacy : (e : Exp₀ ‵ℕ) (n : ℕ) → Set
Adequacy e n = n ≡ ⟦ e ⟧E γ₀ → e ⇓ # n

--! AdequacyBody

adequacy : (e₀ : Exp₀ ‵ℕ) (n₀ : ℕ) → Adequacy e₀ n₀

--! FundamentalType
soundnessV :  (v : Val {Δ} Γ {l} T) → Soundness (‵val v)
soundnessE :  (e : Exp {Δ} Γ {l} T) → Soundness e

adequacy e₀ n₀ refl
  with v₀@(# .n₀) , δ₀*χ₀*e₀⇓#n₀ , refl ← soundnessE e₀ δ₀ χ₀ γ₀ 𝓖₀ = e₀⇓v₀
  where
  -- δ₀*χ₀*e₀⇓#n : Esub* (𝓓Tsub δ₀) (ς χ₀) e₀ ⇓ v₀
  e₀⇓v₀ : e₀ ⇓ v₀
  e₀⇓v₀ rewrite lemmaδ₀ rewrite lemmaχ₀ rewrite ⟦ e₀ ⟧Esub*TidₛEidₛ≗idE
    = {!lemmaδ₀!} -- δ₀*χ₀*e₀⇓#n₀, still modulo ⟦ e₀ ⟧ETₛ Tidₛ ≡ e₀


soundnessV {Δ = Δ} {Γ = Γ} {T = T}        (‵ x)     δ χ γ 𝓖⟦Γ⟧ = _ , ⇓-v , {!!}
soundnessV {Δ = Δ} {Γ = Γ} {T = ‵ℕ}       (# n)     δ χ γ 𝓖⟦Γ⟧ = # n , ⇓-v , refl
soundnessV {Δ = Δ} {Γ = Γ} {T = T₁ ‵⇒ T₂} (ƛ e)     δ χ γ 𝓖⟦Γ⟧ =
  ƛ Esub* (𝓓Tsub δ) (Eliftₛ (VS⇒ES χ)) e , ⇓-v ,
   λ v₀ w v₀[T₁]w → {!!} , {!!} , {!!}
soundnessV {Δ = Δ} {Γ = Γ} {T = ‵∀[ T ]}  (Λ l ⇒ e) δ χ γ 𝓖⟦Γ⟧ = {!!}

soundnessE {Δ = Δ} {Γ = Γ} {T = T} (‵val v)            = soundnessV v
soundnessE {Δ = Δ} {Γ = Γ} {T = T} (‵suc e) δ χ γ 𝓖⟦Γ⟧
  with # n , e⇓#n , eq ←  soundnessE e δ χ γ 𝓖⟦Γ⟧ = # suc n , ⇓-s e⇓#n , cong suc eq
soundnessE {Δ = Δ} {Γ = Γ} {T = T} (f · e)  δ χ γ 𝓖⟦Γ⟧ = {!!}
soundnessE {Δ = Δ} {Γ = Γ} {T = _`} (e ∙ T′) δ χ γ 𝓖⟦Γ⟧ = {!!}

{-
--! FundamentalConstant
fundamental Γ .`ℕ (# n) ρ χ γ 𝓖⟦Γ⟧ =
  (# n , V-♯) , ⇓-n , (n , (refl , refl))

--! FundamentalSuccessor
fundamental Γ .`ℕ (`suc e) ρ χ γ 𝓖⟦Γ⟧
  with fundamental Γ `ℕ e ρ χ γ 𝓖⟦Γ⟧
... | (# n , V-♯) , e⇓v , (. n , refl , lrv) =
  (# ℕ.suc n , V-♯) , ⇓-s e⇓v , (ℕ.suc n  , refl , cong ℕ.suc lrv)

--! FundamentalVariable
fundamental Γ T (` x) ρ χ γ 𝓖⟦Γ⟧ =
  let w = χ _ _ x ; 𝓥⟦T⟧wz = 𝓖-lookup Γ ρ χ γ T 𝓖⟦Γ⟧ x in
  w , Value-⇓ w , 𝓥⟦T⟧wz

--! FundamentalLambda
fundamental Γ (T₁ ⇒ T₂) (ƛ e) ρ χ γ 𝓖⟦Γ⟧ =
  (Csub χ (ƛ e), V-ƛ) , ⇓-ƛ , Esub _ (Eliftₛ _ (ς₁ χ)) e , refl ,
  (λ w z 𝓥⟦T₁⟧wz →
    let eq₁      :  χ ≡ Cdrop {T = T₁} (Cextend χ w)
        eq₁      =  Cdrop-Cextend {T = T₁} χ w
        eqω₁     :  γ ≡ω Gdrop {T = T₁} (extend γ z)
        eqω₁     =  Gdrop-extend {T = T₁} γ z
        𝓖⟦T₁◁Γ⟧  =  (𝓥⟦T₁⟧wz , substlω (𝓖⟦ Γ ⟧ ρ) eq₁ eqω₁ 𝓖⟦Γ⟧)
        eq₂      :  Csub (Cextend χ w) e ≡
                    Esub (π₁ ρ) (Eliftₛ (π₁ ρ) (ς₁ χ)) e [ exp w ]E
        eq₂      =  Cextend-Elift χ w e
        (v , ew⇓v , 𝓥⟦T₂⟧vy) = fundamental (T₁ ◁ Γ) T₂ e ρ
          (Cextend χ w) (extend γ z) 𝓖⟦T₁◁Γ⟧
    in v , subst (_⇓ v) eq₂ ew⇓v , 𝓥⟦T₂⟧vy)

--! FundamentalApplication
fundamental Γ T (_·_ {T = T₂} {T′ = .T} e₁ e₂) ρ χ γ 𝓖⟦Γ⟧
  with fundamental Γ (T₂ ⇒ T) e₁ ρ χ γ 𝓖⟦Γ⟧
... | v₁@(_ , V-ƛ) , e₁⇓v₁ , (e₁′ , refl , 𝓥⟦T₂⇒T⟧v₁z₁)
  with fundamental Γ T₂ e₂ ρ χ γ 𝓖⟦Γ⟧
... | v₂ , e₂⇓v₂ , 𝓥⟦T₂⟧v₂z₂
  with 𝓥⟦T₂⇒T⟧v₁z₁ v₂ (E⟦ e₂ ⟧ (⟦ π₁ ρ ⟧* []) γ) 𝓥⟦T₂⟧v₂z₂
... | v₃ , e₃[]⇓v₃ , 𝓥⟦T⟧v₃z₃
  = v₃ , ⇓-· e₁⇓v₁ e₂⇓v₂ e₃[]⇓v₃ , 𝓥⟦T⟧v₃z₃

--! FundamentalTypeAbstraction
fundamental Γ (`∀α .l , T) (Λ l ⇒ e) ρ χ γ 𝓖⟦Γ⟧ =
  (Csub χ (Λ l ⇒ e), V-Λ) ,
  ⇓-Λ ,
  Esub (Tliftₛ (π₁ ρ) l) (Eliftₛ-l (π₁ ρ) (ς₁ χ)) e ,
  refl ,
  λ T′ R →
    let lrg′ = substωlω-l (𝓖⟦ Γ ⟧)
                      refl
                      (Cdrop-t-Cextt≡id Γ ρ χ l T′ R)
                      (Gdrop-t-ext≡id ρ γ T′ R)
                      𝓖⟦Γ⟧ in
    fundamental (l ◁* Γ)
        T
        e
        (REext ρ (T′ , R))
        (subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) (Cextt χ T′))
        (extend-tskip γ)
        lrg′
    |> λ where
      (v , e⇓v , lrv-t) →
        let v′ = subst CValue (sym (lemma1 ρ T T′ R)) v in
        let e⇓v = subst₂ _⇓_ (sym (Elift-[]≡Cextt Γ ρ χ _ l T e T′ R)) refl e⇓v in
        let sub-lrvt = subst₂ (𝓥⟦ T ⟧ (REext ρ (T′ , R))) (sym (subst-subst-sym (lemma1 ρ T T′ R))) refl in
        let σ* = π₁ ρ in
        let σ = ς₁ χ in
        let 𝕖 = Esub (Textₛ Tidₛ T′) (Eextₛ-l Tidₛ Eidₛ) (Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) e) in
        let eq = lemma1 ρ T T′ R in
           v′ ,
           subst id (begin
              subst CExpr eq 𝕖 ⇓ v
            ≡⟨ subst-swap′′ CExpr CValue _⇓_ 𝕖 v (sym eq) eq ⟩
              𝕖 ⇓ subst CValue (sym eq) v
            ∎) e⇓v ,
           sub-lrvt lrv-t

fundamental Γ .(T [ T′ ]T) (_∙_ {l = l}{T = T} e  T′) ρ χ γ lrg
  with fundamental Γ (`∀α l , T) e ρ χ γ lrg
... | v@ (_ , V-Λ) , e⇓v , e′ , refl , lrv
  with lrv (Tsub (π₁ ρ) T′)
           (subst (λ ⟦T⟧ → CValue (Tsub (π₁ ρ) T′) → ⟦T⟧ → Set l)
                  (sym (subst-preserves (π₁ ρ) T′))
                  (𝓥⟦ T′ ⟧ ρ))
... | v₂ , vT′⇓v₂ , lrv₂  =
  let ρ* = π₁ ρ in
  let σ = ς₁ χ in
  let η = ⟦ ρ* ⟧* [] in
  let eq₁ = sym (swap-Tsub-[] (π₁ ρ) T T′)  in
  let e•T⇓v = ⇓-∙ e⇓v vT′⇓v₂ in
  subst CValue eq₁ v₂ ,
  subst id (begin
      Esub ρ* σ e ∙ Tsub ρ* T′ ⇓ v₂
    ≡⟨ subst-elim′′′′ (Expr [] ∅) CValue _⇓_ (Esub ρ* σ e ∙ Tsub ρ* T′) v₂ eq₁ ⟩
      subst (Expr [] ∅) eq₁ (Esub ρ* σ e ∙ Tsub ρ* T′) ⇓ subst CValue eq₁ v₂
    ∎) e•T⇓v ,
    let
      eq-sub =
        (begin
          𝓥⟦ T ⟧
            (REext ρ
             (Tsub ρ* T′ ,
              subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                (sym (subst-preserves ρ* T′))
                (𝓥⟦ T′ ⟧ ρ)))
            (subst CValue
             (trans
               (trans
                (fusion-Tsub-Tsub T (Tliftₛ ρ* l)
                 (Textₛ Tidₛ (Tsub ρ* T′)))
                (trans
                 (cong (λ σ₁ → Tsub σ₁ T)
                  (sym (fun-ext₂ (sublemma-ext ρ*))))
                 refl))
               (trans
                (cong (λ G → Tsub G T)
                 (sym
                  (fun-ext₂ (subst←RE-ext ρ (Tsub ρ* T′)
                       (subst
                        (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                        (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))))))
                refl))
             v₂)
            (E⟦ e ⟧ η γ (⟦ Tsub ρ* T′ ⟧ []))
        ≡⟨ cong₂
             (λ E₁ E₂ →
                𝓥⟦ T ⟧
                (REext ρ
                 (Tsub ρ* T′ ,
                  subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                  (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ)))
                (subst CValue
                 (trans
                  (trans (fusion-Tsub-Tsub T (Tliftₛ ρ* l) (Textₛ Tidₛ (Tsub ρ* T′)))
                   E₁)
                  E₂)
                 v₂)
                (E⟦ e ⟧ η γ (⟦ Tsub ρ* T′ ⟧ [])))
             (trans-idʳ (cong (λ σ₁ → Tsub σ₁ T) (sym (fun-ext₂ (sublemma-ext ρ*)))))
             (trans-idʳ (cong (λ G → Tsub G T)
       (sym
        (fun-ext₂
         (subst←RE-ext ρ (Tsub ρ* T′)
          (subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
           (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))))))) ⟩
          𝓥⟦ T ⟧
            (REext ρ
             (Tsub ρ* T′ ,
              subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                (sym (subst-preserves ρ* T′))
                (𝓥⟦ T′ ⟧ ρ)))
            (subst CValue
             (trans
               (trans
                (fusion-Tsub-Tsub T (Tliftₛ ρ* l)
                 (Textₛ Tidₛ (Tsub ρ* T′)))
                (cong (λ σ₁ → Tsub σ₁ T)
                  (sym (fun-ext₂ (sublemma-ext ρ*)))))
               (cong (λ G → Tsub G T)
                 (sym
                  (fun-ext₂ (subst←RE-ext ρ (Tsub ρ* T′)
                       (subst
                        (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                        (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ)))))))
             v₂)
            (E⟦ e ⟧ η γ (⟦ Tsub ρ* T′ ⟧ []))
        ≡⟨ dcongωlll 𝓥⟦ T ⟧
           (relenv-ext (λ l₂ x →
             begin
               REext ρ
                 (Tsub ρ* T′ ,
                  subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                  (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                 l₂ x
             ≡⟨ Tsub-act-Text ρ T′ l₂ x ⟩
               Tsub-act (Textₛ Tidₛ T′) ρ l₂ x
             ∎))
    --------------------------------------------------
           (begin
             subst CValue
               (trans
                (trans (fusion-Tsub-Tsub T (Tliftₛ ρ* l) (Textₛ Tidₛ (Tsub ρ* T′)))
                 (cong (λ σ₁ → Tsub σ₁ T) (sym (fun-ext₂ (sublemma-ext ρ*)))))
                (cong (λ G → Tsub G T)
                 (sym
                  (fun-ext₂
                   (subst←RE-ext ρ (Tsub ρ* T′)
                    (subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                     (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ)))))))
               v₂
           ≡⟨ subst*-irrelevant (⟨ CValue , (trans
                (trans (fusion-Tsub-Tsub T (Tliftₛ ρ* l) (Textₛ Tidₛ (Tsub ρ* T′)))
                 (cong (λ σ₁ → Tsub σ₁ T) (sym (fun-ext₂ (sublemma-ext ρ*)))))
                (cong (λ G → Tsub G T)
                 (sym
                  (fun-ext₂
                   (subst←RE-ext ρ (Tsub ρ* T′)
                    (subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                     (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))))))) ⟩∷ [])
                               (⟨ CValue , (trans eq₁ (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) ρ*)) ⟩∷
                                ⟨ CValue , (congωl (λ z → Tsub (π₁ z) T)
                (symω
                 (relenv-ext
                  (λ l₂ x →
                     step-≡
                     (REext ρ
                      (Tsub ρ* T′ ,
                       subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                       (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                      l₂ x)
                     (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))) ⟩∷ []) v₂ ⟩
             subst CValue
               (congωl (λ z → Tsub (π₁ z) T)
                (symω
                 (relenv-ext
                  (λ l₂ x →
                     step-≡
                     (REext ρ
                      (Tsub ρ* T′ ,
                       subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                       (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                      l₂ x)
                     (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x)))))
               (subst CValue (trans eq₁ (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) ρ*)) v₂)
           ≡⟨ sym (substω-congω CValue (λ z → (Tsub (π₁ z) T))
                                 (symω
                (relenv-ext
                 (λ l₂ x →
                    step-≡
                    (REext ρ
                     (Tsub ρ* T′ ,
                      subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                      (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                     l₂ x)
                    (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))
                    (subst CValue (trans eq₁ (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) ρ*)) v₂)) ⟩
             substω (λ z → CValue (Tsub (π₁ z) T))
               (symω
                (relenv-ext
                 (λ l₂ x →
                    step-≡
                    (REext ρ
                     (Tsub ρ* T′ ,
                      subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                      (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                     l₂ x)
                    (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))
               (subst CValue (trans eq₁ (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) ρ*)) v₂)
           ∎)
    --------------------------------------------------
           (begin
             E⟦ e ⟧ η γ (⟦ Tsub ρ* T′ ⟧ [])
           ≡⟨ sym (dcong (E⟦ e ⟧ η γ) (sym (subst-preserves ρ* T′))) ⟩
             subst (λ z → ⟦ T ⟧ (z ∷ η)) (sym (subst-preserves ρ* T′))
               (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))
           ≡⟨ subst-∘ {P = id}{f = (λ z → ⟦ T ⟧ (z ∷ η))} (sym (subst-preserves ρ* T′)) ⟩
             subst id (cong (λ z → ⟦ T ⟧ (z ∷ η)) (sym (subst-preserves ρ* T′)))
               (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))
           ≡⟨ subst-irrelevant {F = id}
                                 (cong (λ z → ⟦ T ⟧ (z ∷ η)) (sym (subst-preserves ρ* T′)))
                                 (congωl ⟦ T ⟧ (conglω (_∷ η) (sym (subst-preserves ρ* T′))))
                                 (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)) ⟩
             subst id (congωl ⟦ T ⟧ (conglω (_∷ η) (sym (subst-preserves ρ* T′)))) (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))
           ≡⟨ subst*-irrelevant (⟨ id , (congωl ⟦ T ⟧ (conglω (_∷ η) (sym (subst-preserves ρ* T′)))) ⟩∷ [])
                                 (⟨ id , (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′))) ⟩∷
                                  ⟨ id , (congωl (λ z → ⟦ T ⟧ (⟦ π₁ z ⟧* []))
                (symω
                 (relenv-ext
                  (λ l₂ x →
                     step-≡
                     (REext ρ
                      (Tsub ρ* T′ ,
                       subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                       (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                      l₂ x)
                     (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))) ⟩∷ [])
                    (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))  ⟩
             subst id
               (congωl (λ z → ⟦ T ⟧ (subst-to-env* (π₁ z) []))
                (symω
                 (relenv-ext
                  (λ l₂ x →
                     step-≡
                     (REext ρ
                      (Tsub ρ* T′ ,
                       subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                       (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                      l₂ x)
                     (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x)))))
               (subst id
                (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
                (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
           ≡⟨ sym (substω-congω id (λ z → ⟦ T ⟧ (subst-to-env* (π₁ z) []))
                                 (symω
                (relenv-ext
                 (λ l₂ x →
                    step-≡
                    (REext ρ
                     (Tsub ρ* T′ ,
                      subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                      (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                     l₂ x)
                    (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))
                    (subst id
                (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
                (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))) ⟩
             substω (λ z → ⟦ T ⟧ (subst-to-env* (π₁ z) []))
               (symω
                (relenv-ext
                 (λ l₂ x →
                    step-≡
                    (REext ρ
                     (Tsub ρ* T′ ,
                      subst (λ ⟦T⟧ → CValue (Tsub ρ* T′) → ⟦T⟧ → Set l)
                      (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                     l₂ x)
                    (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))
               (subst id
                (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
                (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
           ∎)
    --------------------------------------------------
        ⟩
          𝓥⟦ T ⟧ (Tsub-act (Textₛ Tidₛ T′) ρ)
            (subst CValue (trans eq₁ (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) ρ*)) v₂)
            (subst id
             (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
             (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
        ≡⟨ LRVsub T ρ
                  (Textₛ Tidₛ T′)
                  (subst CValue (trans eq₁ (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) ρ*)) v₂)
                  (subst id (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
                            (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
        ⟩
          𝓥⟦ Tsub (Textₛ Tidₛ T′) T ⟧ ρ
            (subst CValue (sym (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) ρ*))
             (subst CValue (trans eq₁ (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) ρ*)) v₂))
            (subst id
             (sym
              (step-≡ (⟦ Tsub (Textₛ Tidₛ T′) T ⟧ η)
               (trans (congωl ⟦ T ⟧ (subst-to-env*-comp (Textₛ Tidₛ T′) ρ* [])) refl)
               (subst-preserves (Textₛ Tidₛ T′) T)))
             (subst id
              (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
              (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))))
        ≡⟨ cong₂ (𝓥⟦ Tsub (Textₛ Tidₛ T′) T ⟧ ρ)
          (subst*-irrelevant (⟨ CValue , (trans eq₁ (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) ρ*)) ⟩∷
                              ⟨ CValue , (sym (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) ρ*)) ⟩∷
                              [])
                             (⟨ CValue , eq₁ ⟩∷
                             []) v₂)
          (subst*-irrelevant (⟨ id , (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′))) ⟩∷
                              ⟨ id , (sym
       (step-≡ (⟦ Tsub (Textₛ Tidₛ T′) T ⟧ η)
        (trans
         (congωl ⟦ T ⟧
          (conglωω _∷_ (sym (subst-preserves ρ* T′))
           (subst-to-env*-comp (Tdropₛ (Textₛ Tidₛ T′)) ρ* [])))
         refl)
        (subst-preserves (Textₛ Tidₛ T′) T))) ⟩∷ [])
                             (⟨ id , (sym
       (trans (subst-preserves (Textₛ Tidₛ T′) T)
        (congωl (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η)))) ⟩∷ [])
                             (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
        ⟩
          𝓥⟦ Tsub (Textₛ Tidₛ T′) T ⟧ ρ
            (subst CValue eq₁ v₂)
            (subst id
             (sym
              (trans (subst-preserves (Textₛ Tidₛ T′) T)
               (congωl
                (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H))
                (subst-to-env*-id η))))
             (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
        ∎)
    in
    subst id eq-sub lrv₂

--------------------------------------------------------------------------------

Tliftₛ-empty : ∀ {l₀} l x → Tliftₛ (λ _ ()) l₀ l x ≡ Tidₛ{Δ = l₀ ∷ []} l x
Tliftₛ-empty l here = refl

Tsub-closed : {T : Type [] l} → T ≡ Tsub (λ l ()) T
Tsub-closed {T = T₁ ⇒ T₂} = cong₂ _⇒_ Tsub-closed  Tsub-closed
Tsub-closed {T = `∀α l₀ , T} = cong (`∀α l₀ ,_)
                                    (sym (trans (cong (λ τ → Tsub τ T) (fun-ext₂ (λ l x → Tliftₛ-empty l x)))
                                                (TidₛT≡T T)))
Tsub-closed {T = `ℕ} = refl

Tsub-[]-is-Tid : ∀ (σ* : TSub [] Δ) → (λ l ()) ≡ σ*
Tsub-[]-is-Tid σ* = fun-ext λ l → fun-ext λ ()

Csub-[]-is-Eid : ∀ (χ : CSub {[]} (λ l ()) ∅) → ς₁ χ ≅ Eidₛ {Γ = ∅}
Csub-[]-is-Eid χ = fun-ext-h-ESub (Tsub-[]-is-Tid Tidₛ) refl λ l T ()

Csub-closed' : {T : Type [] l} (χ : CSub {[]} (λ l ()) ∅) → (e : CExpr T) →
  Csub χ e ≅ e
Csub-closed' {T = T} χ e =
  R.begin
    Csub χ e
  R.≅⟨ refl ⟩
    Esub (λ l ()) (ς₁ χ) e
  R.≅⟨ H.cong₂ {B = λ ■ → ESub ■ ∅ ∅} (λ ■₁ ■₂ → Esub ■₁ ■₂ e)
               (H.≡-to-≅ (Tsub-[]-is-Tid Tidₛ)) (Csub-[]-is-Eid χ) ⟩
    Esub Tidₛ Eidₛ e
  R.≅⟨ H.≡-to-≅ (Eidₛe≡e e) ⟩
    subst (Expr [] ∅) (sym (TidₛT≡T T)) e
  R.≅⟨ H.≡-subst-removable _ _ _ ⟩
    e
  R.∎

--! EmptyEnv
γ₀ : Env [] ∅ []
γ₀ = λ l T ()

--! EmptyRelEnv
ρ₀ : 𝓓⟦ [] ⟧
ρ₀ = λ l ()

--! EmptyCSub
χ₀ : CSub (π₁ ρ₀) ∅
χ₀ l T ()

--! CsubClosed
Csub-closed : ∀ (χ : CSub (π₁ ρ₀) ∅) (e : CExpr T) →
  Csub χ e ≡ subst CExpr Tsub-closed e

Csub-closed χ e =
  H.≅-to-≡ (
    R.begin
      Csub χ e
    R.≅⟨ Csub-closed' χ e ⟩
      e
    R.≅⟨ H.sym (H.≡-subst-removable _ _ _) ⟩
      subst CExpr Tsub-closed e
    R.∎
  )

--! AdequacyType
adequacy : ∀ (e : CExpr `ℕ) (n : ℕ) →
  E⟦ e ⟧ [] γ₀ ≡ n → e ⇓ (# n , V-♯)

--! AdequacyBody
adequacy e n ⟦e⟧≡n with fundamental ∅ `ℕ e ρ₀ χ₀ γ₀ tt
... | ((# .(E⟦ e ⟧ [] γ₀)) , V-♯) , e⇓v , (.(E⟦ e ⟧ [] γ₀) , refl , refl) =
  subst₂ _⇓_ (Csub-closed χ₀ e)
             (cong (λ n → (# n) , V-♯) ⟦e⟧≡n) e⇓v

-}
