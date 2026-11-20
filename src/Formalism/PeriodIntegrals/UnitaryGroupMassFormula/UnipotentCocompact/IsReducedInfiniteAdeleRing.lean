import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.NumberTheory.NumberField.AdeleRing
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

open NumberField IsDedekindDomain
open scoped RestrictedProduct

namespace PI.UnipCocptD

open PI.UnipApproxD

instance isReduced_finiteAdeleRing (F : Type) [Field F] [NumberField F] :
    IsReduced (FiniteAdeleRing (𝓞 F) F) := by
  have : IsReduced (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]) := by
    refine ⟨fun x ⟨k, hk⟩ => ?_⟩
    apply RestrictedProduct.ext
    intro v
    have h2 : (x v) ^ k = 0 := by
      rw [← RestrictedProduct.pow_apply, hk]
      rfl
    rw [IsReduced.eq_zero (x v) ⟨k, h2⟩]
    rfl
  exact this

instance isReduced_infiniteAdeleRing (F : Type) [Field F] [NumberField F] :
    IsReduced (InfiniteAdeleRing F) :=
  inferInstanceAs (IsReduced ((v : InfinitePlace F) → v.Completion))

instance isReduced_adeleRing (F : Type) [Field F] [NumberField F] :
    IsReduced (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (IsReduced (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end PI.UnipCocptD
