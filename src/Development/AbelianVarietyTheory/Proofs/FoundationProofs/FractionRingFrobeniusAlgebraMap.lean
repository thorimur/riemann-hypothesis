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
import Mathlib.RingTheory.WittVector.Isocrystal
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
import Std.Tactic.BVDecide.Normalize.Prop

noncomputable section

open IsLocalRing QuadraticAlgebra

namespace GlobalTheory.SqrtUnif

section Quadratic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}

end Quadratic

section Squares

end Squares

section Witt

variable (p : ℕ) [hp : Fact p.Prime]

theorem fractionRing_frobenius_algebraMap {k : Type*} [Field k] [CharP k p] [PerfectRing k p]
    (x : WittVector p k) : WittVector.FractionRing.frobenius p k (algebraMap _ _ x) =
      algebraMap _ (FractionRing (WittVector p k)) (WittVector.frobenius x) := by
  simp [WittVector.FractionRing.frobenius]

theorem fractionRing_frobenius_pow {n : ℕ} (hn : n ≠ 0) :
    WittVector.FractionRing.frobenius p (GaloisField p n) ^ n = 1 := by
  have h1 : ∀ (m : ℕ) (x : WittVector p (GaloisField p n)),
      ∃ y : WittVector p (GaloisField p n), (∀ i, y.coeff i = x.coeff i ^ p ^ m) ∧
        (WittVector.FractionRing.frobenius p (GaloisField p n) ^ m) (algebraMap _ _ x) =
          algebraMap _ (FractionRing (WittVector p (GaloisField p n))) y := by
    intro m x
    induction m with
    | zero => exact ⟨x, by simp, rfl⟩
    | succ m ih =>
      obtain ⟨y, hy, h⟩ := ih
      refine ⟨WittVector.frobenius y, fun i => ?_, ?_⟩
      · rw [WittVector.coeff_frobenius_charP, hy, ← pow_mul, pow_succ]
      · rw [pow_succ', RingAut.mul_apply, h, fractionRing_frobenius_algebraMap]
  letI := Fintype.ofFinite (GaloisField p n)
  have hc : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p _ hn]
  refine RingEquiv.toRingHom_injective (IsLocalization.ringHom_ext
    (nonZeroDivisors (WittVector p (GaloisField p n))) (RingHom.ext fun x => ?_))
  obtain ⟨y, hy, h⟩ := h1 n x
  have : y = x := by
    ext i
    rw [hy, ← hc, FiniteField.pow_card]
  exact h.trans (by rw [this]; rfl)

end Witt

end GlobalTheory.SqrtUnif
