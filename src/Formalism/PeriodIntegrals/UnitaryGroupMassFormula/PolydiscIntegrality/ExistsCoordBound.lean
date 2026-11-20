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

namespace PI.PolydiscIntegrality₂

open Filter Topology

variable {p : ℕ} [Fact p.Prime]

theorem exists_coord_bound {n : ℕ} (S : Finset (Fin n →₀ ℕ)) :
    ∃ B : ℕ, ∀ γ ∈ S, ∀ i, γ i ≤ B := by
  refine ⟨∑ γ ∈ S, ∑ i, γ i, fun γ hγ i => ?_⟩
  calc γ i ≤ ∑ i, γ i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ ∑ γ ∈ S, ∑ i, γ i := Finset.single_le_sum (f := fun γ : Fin n →₀ ℕ => ∑ i, γ i)
        (fun _ _ => Nat.zero_le _) hγ

end PI.PolydiscIntegrality₂
