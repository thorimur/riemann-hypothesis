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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem sum_log_norm_embeddings_eq_log_norm (k A : Type) [Field k] [NumberField k] [NormedField A]
    [CharZero A] [IsAlgClosed A] (x : k) (hx : x ≠ 0) :
    ∑ j : k →+* A, Real.log ‖j x‖ = Real.log ‖((Algebra.norm ℚ x : ℚ) : A)‖ := by
  letI : Algebra ℚ A := DivisionRing.toRatAlgebra
  have h1 : algebraMap ℚ A (Algebra.norm ℚ x) = ∏ σ : k →ₐ[ℚ] A, σ x :=
    Algebra.norm_eq_prod_embeddings ℚ A x
  have h2 : ((Algebra.norm ℚ x : ℚ) : A) = ∏ σ : k →ₐ[ℚ] A, σ x := by
    rw [← h1]; simp
  have h3 : ∏ σ : k →ₐ[ℚ] A, σ x = ∏ j : k →+* A, j x :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom (R := k) (S := A)).symm _ _ (fun σ => rfl)
  rw [h2, h3, norm_prod, Real.log_prod]
  intro j _
  exact norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hx)

end GlobalTheory.CompanionTheory.Ar.Fl
