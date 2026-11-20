import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem ringHom_independent_via_algebraMap :
    ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ],
      Function.Injective (algebraMap O C) → ∀ (S : Finset (Λ →+* O)) (c : (Λ →+* O) → C),
        (∀ a : Λ, ∑ σ ∈ S, c σ * algebraMap O C (σ a) = 0) → ∀ σ ∈ S, c σ = 0 := by
  intro C _ O _ _ Λ _ hinj S c hsum
  classical
  let φ : (Λ →+* O) → (Λ →* C) := fun σ => ((algebraMap O C).comp σ).toMonoidHom
  have hφ : Function.Injective φ := by
    intro σ τ h
    ext a
    apply hinj
    have := congrArg (fun f : Λ →* C => f a) h
    simpa [φ] using this
  have hli := (linearIndependent_monoidHom Λ C).comp φ hφ
  rw [linearIndependent_iff'] at hli
  intro σ hσ
  apply hli S c _ σ hσ
  funext a
  simpa [φ, Finset.sum_apply] using hsum a

end GlobalTheory
