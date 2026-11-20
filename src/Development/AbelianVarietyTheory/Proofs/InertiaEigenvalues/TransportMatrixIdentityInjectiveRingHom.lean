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
open Matrix

namespace GlobalTheory

theorem transport_matrix_identity_star_alg :
    ∀ {R L : Type} [CommRing R] [CommRing L] (ι : R →+* L), Function.Injective ι →
    ∀ (d N q : ℕ) (p : Fin d → ℕ) (ξ s : R) (Qm Q₁ : Matrix (Fin d) (Fin d) L)
      (X B c V : Matrix (Fin d) (Fin d) R),
      ι s ^ N • Qm = (X * B).map ι → (∀ i j, ι ξ ^ q * Q₁ i j = ι (ξ ^ p j * V i j)) →
      Q₁ = Qm * c.map ι →
      ξ ^ q • (X * B * c) = s ^ N • (V * Matrix.diagonal (fun j => ξ ^ p j)) := by
  intro R L _ _ ι hι d N q p ξ s Qm Q₁ X B c V h1 h2 h3
  have key : (X * B * c).map ι = ι s ^ N • Q₁ := by
    rw [Matrix.map_mul, ← h1, h3, Matrix.smul_mul]
  ext i j
  apply hι
  have e : ι ((X * B * c) i j) = ι s ^ N * Q₁ i j := by
    have := congrFun (congrFun key i) j
    simpa [Matrix.map_apply, Matrix.smul_apply] using this
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, map_mul, map_pow]
  rw [e]
  have h := h2 i j
  simp only [map_mul, map_pow] at h
  calc ι ξ ^ q * (ι s ^ N * Q₁ i j) = ι s ^ N * (ι ξ ^ q * Q₁ i j) := by ring
    _ = ι s ^ N * (ι ξ ^ p j * ι (V i j)) := by rw [h]
    _ = ι s ^ N * (ι (V i j) * ι ξ ^ p j) := by ring

end GlobalTheory
