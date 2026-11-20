import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.QuadraticAlgebra.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace Formalism.L2.G.Quad

open QuadraticAlgebra

variable {R : Type} [CommRing R] (π : R)

def toRes : QuadraticAlgebra R π 0 →+* R ⧸ Ideal.span {π} where
  toFun z := Ideal.Quotient.mk _ z.re
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    have h : Ideal.Quotient.mk (Ideal.span {π}) π = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)
    simp [h]

theorem toRes_apply (z : QuadraticAlgebra R π 0) : toRes π z = Ideal.Quotient.mk _ z.re := rfl

theorem toRes_surjective : Function.Surjective (toRes π) := by
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨⟨r, 0⟩, rfl⟩

theorem mem_span_om (z : QuadraticAlgebra R π 0) :
    z ∈ Ideal.span {(ω : QuadraticAlgebra R π 0)} ↔ π ∣ z.re := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.im, by simp⟩
  · rintro ⟨d, hd⟩
    refine ⟨⟨z.im, d⟩, ?_⟩
    ext <;> simp [hd]

theorem ker_toRes : RingHom.ker (toRes π) = Ideal.span {(ω : QuadraticAlgebra R π 0)} := by
  ext z
  rw [RingHom.mem_ker, toRes_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    mem_span_om]

def resEquiv : (QuadraticAlgebra R π 0 ⧸ Ideal.span {(ω : QuadraticAlgebra R π 0)}) ≃+* (R ⧸ Ideal.span {π}) :=
  (Ideal.quotEquivOfEq (ker_toRes π).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toRes_surjective π))

theorem card_res :
    Nat.card (QuadraticAlgebra R π 0 ⧸ Ideal.span {(ω : QuadraticAlgebra R π 0)}) =
      Nat.card (R ⧸ Ideal.span {π}) :=
  Nat.card_congr (resEquiv π).toEquiv

theorem algebraMap_finite : (algebraMap R (QuadraticAlgebra R π 0)).Finite := by
  rw [RingHom.finite_algebraMap]
  infer_instance

theorem algebraMap_injective : Function.Injective (algebraMap R (QuadraticAlgebra R π 0)) := by
  intro x y h
  simpa [Algebra.algebraMap_eq_smul_one] using congrArg QuadraticAlgebra.re h

end Formalism.L2.G.Quad
