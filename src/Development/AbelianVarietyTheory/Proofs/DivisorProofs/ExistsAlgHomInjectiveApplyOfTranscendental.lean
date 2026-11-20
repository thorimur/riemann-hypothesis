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
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem algebraicIndependent_update_pow {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [DecidableEq ι] {x : ι → A} (hx : AlgebraicIndependent R x) (i₀ : ι) {n : ℕ} (hn : 0 < n) :
    AlgebraicIndependent R (Function.update x i₀ (x i₀ ^ n)) := by
  let e := Equiv.optionSubtypeNe i₀
  have key : ∀ y : ι → A, y ∘ e = fun o => o.elim (y i₀) (fun b => y b.1) := by
    intro y; funext o; cases o <;> rfl
  rw [← algebraicIndependent_equiv e, key] at hx
  rw [← algebraicIndependent_equiv e, key]
  obtain ⟨h1, h2⟩ := AlgebraicIndependent.option_iff.1 hx
  have hrest : (fun b : {b // b ≠ i₀} => Function.update x i₀ (x i₀ ^ n) b.1) =
      fun b => x b.1 := by
    funext b; exact Function.update_of_ne b.2 _ _
  rw [hrest, Function.update_self]
  exact AlgebraicIndependent.option_iff.2 ⟨h1, h2.pow hn⟩

end GlobalTheory
