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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc :
    ∀ (F k L : Type) [Field F] [Field k] [Field L] [Algebra F k] [Algebra F L] (α : k →+* L)
      (j : L →+* RatFunc k) (d : ℕ), α.comp (algebraMap F k) = algebraMap F L →
      j.comp α = algebraMap k (RatFunc k) → Algebra.trdeg F k = d →
      Algebra.trdeg F L ≤ (d + 1 : ℕ) := by
  intro F k L _ _ _ _ _ α j d hα hj hd
  let jF : L →ₐ[F] RatFunc k :=
    { j with
      commutes' := fun x => by
        show j (algebraMap F L x) = algebraMap k (RatFunc k) (algebraMap F k x)
        rw [← hα, ← hj]; rfl }
  have h1 : Algebra.trdeg F L ≤ Algebra.trdeg F (RatFunc k) :=
    trdeg_le_of_injective jF j.injective
  have hR : Algebra.trdeg k (RatFunc k) = 1 := by
    have : Algebra.IsAlgebraic (Polynomial k) (RatFunc k) :=
      IsLocalization.isAlgebraic (RatFunc k) (nonZeroDivisors (Polynomial k))
    rw [← trdeg_add_eq k (Polynomial k), trdeg_eq_zero (R := Polynomial k) (A := RatFunc k),
      add_zero, Polynomial.trdeg_of_isDomain]
  have h2 := trdeg_add_eq F k (A := RatFunc k)
  calc Algebra.trdeg F L ≤ Algebra.trdeg F (RatFunc k) := h1
    _ = ((d + 1 : ℕ) : Cardinal) := by rw [← h2, hR, hd]; push_cast; rfl
