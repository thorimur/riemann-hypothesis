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

namespace GlobalTheory

theorem finset_mem_range_of_away_dvd (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (F : Finset (Localization.AtPrime 𝔭)) :
    ∃ s ∉ 𝔭, ∀ (c : R), s ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭,
      κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) →
        ∀ x ∈ F, x ∈ κ.range := by
  classical
  choose p hp using fun x : Localization.AtPrime 𝔭 =>
    IsLocalization.mk'_surjective 𝔭.primeCompl x
  let sx : Localization.AtPrime 𝔭 → 𝔭.primeCompl := fun x => (p x).2
  refine ⟨((∏ x ∈ F, sx x : 𝔭.primeCompl) : R), (∏ x ∈ F, sx x).2, ?_⟩
  intro c hc κ hκ x hx
  have hdvd : ((sx x : 𝔭.primeCompl) : R) ∣ c := by
    refine dvd_trans ?_ hc
    rw [Submonoid.coe_finset_prod]
    exact Finset.dvd_prod_of_mem (fun y => ((sx y : 𝔭.primeCompl) : R)) hx
  obtain ⟨m, hm⟩ := hdvd
  have hκa : ∀ r : R, κ (algebraMap R (Localization.Away c) r) =
      algebraMap R (Localization.AtPrime 𝔭) r := fun r => by
    rw [← RingHom.comp_apply, hκ]
  refine ⟨algebraMap R _ (p x).1 * algebraMap R _ m * IsLocalization.Away.invSelf c, ?_⟩
  have hinv : algebraMap R (Localization.AtPrime 𝔭) c *
      κ (IsLocalization.Away.invSelf (S := Localization.Away c) c) = 1 := by
    rw [← hκa, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  refine (?_ : _ = IsLocalization.mk' (Localization.AtPrime 𝔭) (p x).1 (p x).2).trans (hp x)
  rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, map_mul, hκa, hκa]
  calc algebraMap R (Localization.AtPrime 𝔭) (p x).1 * algebraMap R _ m *
        κ (IsLocalization.Away.invSelf c) * algebraMap R _ ((p x).2 : R)
      = algebraMap R (Localization.AtPrime 𝔭) (p x).1 *
        (algebraMap R _ (((p x).2 : R) * m) * κ (IsLocalization.Away.invSelf c)) := by
        rw [map_mul]; ring
    _ = algebraMap R (Localization.AtPrime 𝔭) (p x).1 := by
        rw [← hm, hinv, mul_one]

end GlobalTheory
