import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.Exact
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
import Mathlib.RepresentationTheory.Coinduced
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

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem exists_free_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (A : Rep k G), ∃ (ι : Type) (K : Rep k G) (i : K ⟶ Rep.free k G ι) (e : Rep.free k G ι ⟶ A) (h : i ≫ e = 0), (ShortComplex.mk i e h).ShortExact := by
  intro k G _ _ A
  let e : Rep.free k G A ⟶ A := Rep.freeLift k G A (fun x => x)
  have he : Epi e := (Rep.epi_iff_surjective e).2 fun x =>
    ⟨Finsupp.single x (MonoidAlgebra.single 1 1), by
      simp [e, Representation.freeLift_single_single]⟩
  exact ⟨A, kernel e, kernel.ι e, e, kernel.condition e,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel e) inferInstance he⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exists_free_resolution_short_exact : ∀ (k G : Type) [CommRing k] [Group G] (A : Rep k G), ∃ (ι : Type) (K : Rep k G) (i : K ⟶ Rep.free k G ι) (e : Rep.free k G ι ⟶ A) (h : i ≫ e = 0), (ShortComplex.mk i e h).ShortExact := by
  first
  | exact @GlobalTheory.HomStab.exists_free_shortExact
end
