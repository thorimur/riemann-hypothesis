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

namespace Bl.FirstBlockLemmaG

theorem goal1 :
  ∀ {O : Type} [inst : CommRing.{0} O] [inst_1 : IsLocalRing.{0} O] {a m : O},
  IsUnit.{0} a → Membership.mem.{0, 0} (IsLocalRing.maximalIdeal.{0} O) m → IsUnit.{0} (HSub.hSub.{0, 0, 0} a m) := by
  intro O _ _ a m ha hm
  by_contra h
  have h1 : a - m ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal (a - m)).mpr (mem_nonunits_iff.mpr h)
  have h2 : a ∈ IsLocalRing.maximalIdeal O := by
    have h3 := Ideal.add_mem _ h1 hm
    rwa [sub_add_cancel] at h3
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal a).mp h2)) ha

end Bl.FirstBlockLemmaG
