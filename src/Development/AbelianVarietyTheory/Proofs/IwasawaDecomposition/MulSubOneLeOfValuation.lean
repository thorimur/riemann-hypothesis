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
import Mathlib.RingTheory.PiTensorProduct
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

namespace GlobalTheory.MulSubOneValuation

theorem mul_sub_one_le_of_valuation {K Γ : Type*} [CommRing K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} {γ : Γ} (hγ : γ ≤ 1) {A B : Matrix (Fin n) (Fin n) K}
    (hA : ∀ r s, v (A r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ)
    (hB : ∀ r s, v (B r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ) (r s : Fin n) :
    v ((A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ := by

  have hM : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  have he : (A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s =
      (A - 1) r s + (B - 1) r s + ((A - 1) * (B - 1)) r s := by
    simpa [Matrix.sub_apply, Matrix.add_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) K => M r s) hM
  rw [he, Matrix.mul_apply]
  refine v.map_add_le (v.map_add_le (hA r s) (hB r s)) (v.map_sum_le fun k _ => ?_)
  calc v ((A - 1) r k * (B - 1) k s) = v ((A - 1) r k) * v ((B - 1) k s) := map_mul v _ _
    _ ≤ γ * γ := mul_le_mul' (hA r k) (hB k s)
    _ ≤ γ := mul_le_of_le_one_right' hγ

theorem mul_sub_one_le {E : Type} [Field E] [NumberField E]
    {P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)} {n N : ℕ}
    {A B : Matrix (Fin n) (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)}
    (hA : ∀ r s : Fin n, (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) (A r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (hB : ∀ r s : Fin n, (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) (B r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (r s : Fin n) :
    (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) ((A * B) r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  have hγ : WithZero.exp (-(N : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  exact mul_sub_one_le_of_valuation Valued.v hγ hA hB r s

end GlobalTheory.MulSubOneValuation
