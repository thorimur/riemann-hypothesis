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

namespace GlobalTheory.DeterminantExpansion

theorem det_mul_expand {V : Type} [inst : CommRing V] {m g : ℕ}
    (M : Matrix (Fin m) (Fin g) V) (C : Matrix (Fin g) (Fin m) V) :
    Matrix.det (M * C) =
      ∑ J : Fin m → Fin g, (∏ i : Fin m, M i (J i)) * Matrix.det (Matrix.submatrix C J id) := by
  classical
  have h : (M * C : Matrix (Fin m) (Fin m) V) = fun i => ∑ k : Fin g, M i k • C k := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  let f : MultilinearMap V (fun _ : Fin m => Fin m → V) V :=
    (Matrix.detRowAlternating : (Fin m → V) [⋀^Fin m]→ₗ[V] V).toMultilinearMap
  have hf : ∀ A : Matrix (Fin m) (Fin m) V, Matrix.det A = f A := fun A => rfl
  rw [hf, h, f.map_sum (fun i k => M i k • C k)]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [f.map_smul_univ (fun i => M i (J i)) (fun i => C (J i)), hf, smul_eq_mul]
  rfl

end GlobalTheory.DeterminantExpansion
