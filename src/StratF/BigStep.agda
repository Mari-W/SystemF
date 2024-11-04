module StratF.BigStep where

open import Data.Nat.Base using (suc)

open import StratF.ExpSubstitution
open import StratF.Expressions
open import StratF.TypeEnvironments
open import StratF.Evaluation

--! BigStep >

-- big step semantics
infix 15 _⇓_

--! Semantics
data _⇓_ : Exp₀ T₀ → Val₀ T₀ → Set where
  ⇓-v :  ‵val v₀ ⇓ v₀
  ⇓-s :  e₀ ⇓ # n → ‵suc e₀ ⇓ # suc n
  ⇓-· :  f₀ ⇓ ƛ e → e₀ ⇓ v₀ → e [ ‵val v₀ ]Eₛ ⇓ w₀ → f₀ · e₀ ⇓ w₀
  ⇓-∙ :  e₀ ⇓ Λ l ⇒ e → e [ T₀ ]ETₛ ⇓ v₀ → e₀ ∙ T₀ ⇓ v₀

-- evaluation API

--! evalBig
evalBig : EvalAPI
evalBig = record
            { _↓_ = _⇓_
            ; ↓-s = ⇓-s
            ; ↓-· = ⇓-·
            ; ↓-∙ = ⇓-∙
            ; ↓-v = ⇓-v
            }
