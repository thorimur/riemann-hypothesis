import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.exists_finite_etale_restrict_clopen :
    ∀ (Y Z : Scheme.{0}) (c : Y ⟶ Z) (V : Z.Opens) (W : Y.Opens), IsClosed (W : Set Y) → W ≤ c ⁻¹ᵁ V → IsFinite c → Etale c → ∃ c' : W.toScheme ⟶ V.toScheme, c' ≫ V.ι = W.ι ≫ c ∧ IsFinite c' ∧ Etale c' := by
  intro Y Z c V W hWc hWV hfin het
  haveI := het
  haveI := hfin
  refine ⟨c.resLE V W hWV, c.resLE_comp_ι hWV, ?_, inferInstance⟩
  haveI hWι : IsClosedImmersion W.ι := .of_isPreimmersion _ (by simpa using hWc)
  haveI h1 : IsClosedImmersion (Y.homOfLE hWV ≫ (c ⁻¹ᵁ V).ι) := by
    rw [Scheme.homOfLE_ι]
    exact hWι
  haveI h2 : IsClosedImmersion (Y.homOfLE hWV) := .of_comp _ ((c ⁻¹ᵁ V).ι)
  haveI h3 : IsFinite (c ∣_ V) := by infer_instance
  show IsFinite (Y.homOfLE hWV ≫ c ∣_ V)
  infer_instance
