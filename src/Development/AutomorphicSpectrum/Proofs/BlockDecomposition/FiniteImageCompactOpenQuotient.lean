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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.Topology

theorem finite_image_mk_of_isOpen_of_isCompact :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      (H : AddSubgroup G) (K : Set G), IsOpen (H : Set G) → IsCompact K →
      (QuotientAddGroup.mk '' K : Set (G ⧸ H)).Finite := by
  intro G _ _ _ H K hH hK
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : G => (fun y => x + y) '' (H : Set G))
    (fun x => (Homeomorph.addLeft x).isOpenMap _ hH)
    (fun x _ => Set.mem_iUnion.2 ⟨x, 0, H.zero_mem, add_zero x⟩)
  refine (t.finite_toSet.image (QuotientAddGroup.mk : G → G ⧸ H)).subset ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨x, hx, hxk⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨h, hh, rfl⟩ := hxk
  refine ⟨x, hx, ?_⟩
  exact QuotientAddGroup.eq.2 (by simpa using hh)

end GlobalTheory.CompanionTheory.Topology
