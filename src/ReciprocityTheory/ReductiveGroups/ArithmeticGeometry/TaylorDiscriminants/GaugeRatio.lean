import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.Exp
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

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.TB

abbrev GLet (T : Type) (rk : T → ℕ) : Type := Σ σ : T, Fin (rk σ)

def scaleBy {O k T : Type} [CommRing O] [CommRing k] {rk : T → ℕ} (χ : T → O →+* k) (a : O) :
    MvPowerSeries (GLet T rk) k →+* MvPowerSeries (GLet T rk) k :=
  MvPowerSeries.rescale (fun l => χ l.1 a)

def GaugeRatioSt : Prop :=
  ∀ (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] (T : Type) [Fintype T]
    (rk : T → ℕ) (χ : T → O →+* k) (cc : T → T),
    (∀ σ a, χ (cc σ) a = χ σ (star a)) →
    (∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a)) →
    ∀ r : MvPowerSeries (GLet T rk) k, constantCoeff r = 1 →
    (∀ a : O, scaleBy χ (1 + a * star a) r = scaleBy χ a r ^ 2 * r * scaleBy χ (a * star a) r) →
    ∃ q : MvPowerSeries (GLet T rk) k, constantCoeff q = 0 ∧
      (∀ m, coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ l l' : GLet T rk, coeff (Finsupp.single l 1 + Finsupp.single l' 1) q ≠ 0 → l'.1 = cc l.1) ∧
      r = PowerSeries.subst q (PowerSeries.exp k)

end ReciprocityTheory.ChartRestriction.G.TB
