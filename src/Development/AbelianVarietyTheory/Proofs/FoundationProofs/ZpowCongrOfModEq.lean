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

open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.KummerEisensteinGalois

lemma zpow_congr_of_modEq {K : Type} [Field K] {ζ : K} {M : ℕ} (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M)
    {u v : ℤ} (h : u ≡ v [ZMOD M]) : ζ ^ u = ζ ^ v := by
  have h0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have h1 : ζ ^ (u - v) = 1 := (hζ.zpow_eq_one_iff_dvd (u - v)).2 (Int.ModEq.dvd h.symm)
  calc ζ ^ u = ζ ^ (v + (u - v)) := by rw [add_sub_cancel]
    _ = ζ ^ v * ζ ^ (u - v) := zpow_add₀ h0 _ _
    _ = ζ ^ v := by rw [h1, mul_one]

end GlobalTheory.KummerEisensteinGalois
