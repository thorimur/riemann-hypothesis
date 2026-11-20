import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem isTotallyComplex_of_primitiveRoot (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ)
    (hζ : IsPrimitiveRoot ζ m) (hm : 3 ≤ m) : NumberField.IsTotallyComplex K := by
  rw [NumberField.isTotallyComplex_iff]
  intro v
  by_contra hc
  have hr : v.IsReal := InfinitePlace.not_isComplex_iff_isReal.mp hc
  set ψ : K →+* ℝ := InfinitePlace.embedding_of_isReal hr
  have hψ : IsPrimitiveRoot (ψ ζ) m := hζ.map_of_injective ψ.injective
  have hm0 : m ≠ 0 := by omega
  have h1 : ψ ζ ^ m = 1 := hψ.pow_eq_one
  have h2 : ψ ζ ^ 2 = 1 := by
    rcases (pow_eq_one_iff_of_ne_zero hm0).mp h1 with h | ⟨h, _⟩ <;> rw [h] <;> norm_num
  have h3 : ψ (ζ ^ 2) = ψ 1 := by rw [map_pow, h2, map_one]
  have h4 : ζ ^ 2 = 1 := ψ.injective h3
  have h5 : m ∣ 2 := hζ.pow_eq_one_iff_dvd 2 |>.mp h4
  have := Nat.le_of_dvd (by norm_num) h5
  omega

theorem tcroot : ∀ (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ), IsPrimitiveRoot ζ m → 3 ≤ m →
    NumberField.IsTotallyComplex K :=
  fun K _ _ ζ m hζ hm => isTotallyComplex_of_primitiveRoot K ζ m hζ hm

end GlobalTheory
