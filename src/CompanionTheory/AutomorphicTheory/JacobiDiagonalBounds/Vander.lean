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

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

theorem vander' (Q : ℕ) : ∃ lam : Fin (Q + 1) → Fin (Q + 1) → ℂ, ∀ (E : Type) [AddCommGroup E] [Module ℂ E]
    (a : Fin (Q + 1) → E) (q : Fin (Q + 1)),
    a q = ∑ s : Fin (Q + 1), lam q s • ∑ j : Fin (Q + 1), (((s : ℕ) : ℂ) ^ (j : ℕ)) • a j := by
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ,
      V = Matrix.vandermonde fun s => ((s : ℕ) : ℂ) := ⟨_, rfl⟩
  have hdet : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, hV, Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    simpa [Fin.ext_iff] using hij
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  refine ⟨fun q s => (V⁻¹ : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q s, fun E _ _ a q => ?_⟩
  beta_reduce
  have hrow : ∀ j : Fin (Q + 1),
      ∑ s : Fin (Q + 1), V⁻¹ q s * ((s : ℕ) : ℂ) ^ (j : ℕ) = (1 : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q j := by
    intro j
    rw [← hinv, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [hV, Matrix.vandermonde_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hrow, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

end Formalism.FourierDecayAlt.P.NormalFormRelations
