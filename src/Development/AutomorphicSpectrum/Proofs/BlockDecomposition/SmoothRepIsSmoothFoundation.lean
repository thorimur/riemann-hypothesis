import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import GroundTheory.AutomorphicForms.SmoothRep
import Mathlib.NumberTheory.LocalField.Basic
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SmoothTransfer

theorem isSmooth_found : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → GroundTheory.Automorphic.IsSmooth π := by
  intro k _ _ _ _ N V _ _ π h
  exact h

end GlobalTheory.CompanionTheory.SmoothTransfer
