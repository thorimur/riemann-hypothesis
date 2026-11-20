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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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

namespace GroundTheory.Automorphic.HarishChandra

abbrev Poly (n : ℕ) := MvPolynomial (Fin n × Fin n) ℂ

variable {n : ℕ}

noncomputable def rowOp (i j : Fin n) : Module.End ℂ (Poly n) :=
  ∑ k : Fin n, (LinearMap.mulLeft ℂ (MvPolynomial.X (i, k) : Poly n)) ∘ₗ
    (MvPolynomial.pderiv (j, k) : Derivation ℂ (Poly n) (Poly n)).toLinearMap

theorem rowOp_apply (i j : Fin n) (f : Poly n) :
    rowOp i j f = ∑ k : Fin n, MvPolynomial.X (i, k) * MvPolynomial.pderiv (j, k) f := by
  simp [rowOp, LinearMap.sum_apply]

end GroundTheory.Automorphic.HarishChandra
