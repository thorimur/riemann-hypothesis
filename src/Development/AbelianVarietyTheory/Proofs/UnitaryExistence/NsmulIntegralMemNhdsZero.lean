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
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.IntegralNeighbourhoodZero

open IsDedekindDomain NumberField

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem fun _ => Valued.isOpen_valuationSubring _

theorem nsmul_integral_mem_nhds_zero (F : Type) [Field F] [NumberField F] (M : ℕ) (hM : 0 < M) :
    {c : FiniteAdeleRing (RingOfIntegers F) F |
      ∃ a : FiniteAdeleRing (RingOfIntegers F) F,
        (∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F) ∧
          c = M • a} ∈ nhds (0 : FiniteAdeleRing (RingOfIntegers F) F) := by
  obtain ⟨m, hm⟩ : ∃ m : FiniteAdeleRing (RingOfIntegers F) F, m = algebraMap F _ ((M : F)⁻¹) := ⟨_, rfl⟩
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hmM : (M : FiniteAdeleRing (RingOfIntegers F) F) * m = 1 := by
    rw [hm, ← map_natCast (algebraMap F (FiniteAdeleRing (RingOfIntegers F) F)), ← map_mul,
      mul_inv_cancel₀ hMF, map_one]
  have hopen : IsOpen ((fun c => m * c) ⁻¹' {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F}) :=
    (isOpen_integral F).preimage (continuous_const.mul continuous_id)
  have h0 : (0 : FiniteAdeleRing (RingOfIntegers F) F) ∈ (fun c => m * c) ⁻¹'
      {a : FiniteAdeleRing (RingOfIntegers F) F |
        ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F} := by
    intro v
    change (m * 0) v ∈ _
    rw [mul_zero]
    exact zero_mem _
  refine Filter.mem_of_superset (hopen.mem_nhds h0) ?_
  intro c hc
  refine ⟨m * c, hc, ?_⟩
  rw [nsmul_eq_mul, ← mul_assoc, hmM, one_mul]

end GlobalTheory.IntegralNeighbourhoodZero
