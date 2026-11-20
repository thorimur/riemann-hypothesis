import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem idem_germ_eq_of_isUnit_iff {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : a * a = a) (hb : b * b = b) (h : IsUnit a ↔ IsUnit b) : a = b := by
  have key : ∀ c : R, c * c = c → (IsUnit c → c = 1) ∧ (¬ IsUnit c → c = 0) := by
    intro c hc
    refine ⟨fun hu => ?_, fun hn => ?_⟩
    · obtain ⟨u, rfl⟩ := hu
      have : (u : R) * u = u * 1 := by rw [mul_one]; exact hc
      exact (Units.mul_right_inj u).mp this
    · rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h1 | h1
      · exact absurd h1 hn
      · have : (1 - c) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
        obtain ⟨u, hu⟩ := h1
        rw [← hu] at this
        simpa using this
  by_cases hau : IsUnit a
  · rw [(key a ha).1 hau, (key b hb).1 (h.mp hau)]
  · rw [(key a ha).2 hau, (key b hb).2 (fun hbu => hau (h.mpr hbu))]

theorem idempotent_eq_of_basicOpen_eq : ∀ (X : Scheme.{0}) (e e' : Γ(X, ⊤)), e * e = e → e' * e' = e' →
    X.basicOpen e = X.basicOpen e' → e = e' := by
  intro X e e' he he' hb
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ e e' (fun x hx => ?_)
  change X.presheaf.germ ⊤ x hx e = X.presheaf.germ ⊤ x hx e'
  apply idem_germ_eq_of_isUnit_iff (R := X.presheaf.stalk x)
  · rw [← map_mul, he]
  · rw [← map_mul, he']
  · rw [← X.mem_basicOpen e x hx, ← X.mem_basicOpen e' x hx, hb]

end GlobalTheory
