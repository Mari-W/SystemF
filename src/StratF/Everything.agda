module StratF.Everything where

open import StratF.TypeEnvironments
open import StratF.Types
open import StratF.TypeSubstitution
open import StratF.TypeSubstProperties
open import StratF.TypeSubstPropertiesSem

open import StratF.ExpEnvironments
open import StratF.Expressions
open import StratF.ExpSubstitution       -- finished?
open import StratF.ExpSubstProperties    -- blank; what's needed?
open import StratF.ExpSubstPropertiesSem -- TODO: minimal signature of what's needed
-- via two new lemmas ⟦_βƛ_⟧E_, ⟦_βΛ_⟧E_ intended as instances of more general
-- commutation properties `lemmaV`/`lemmaE`, one for `Val` and one for `Exp`

open import StratF.Evaluation
open import StratF.SmallStep
open import StratF.SmallStepSoundness    -- DONE, via ⟦_βƛ_⟧E_, ⟦_βΛ_⟧E_
open import StratF.BigStep
open import StratF.BigEqSmall
open import StratF.BigStepSoundness      -- DONE, via SmallStepSoundness

open import StratF.LogicalRelation
open import StratF.Fundamental

