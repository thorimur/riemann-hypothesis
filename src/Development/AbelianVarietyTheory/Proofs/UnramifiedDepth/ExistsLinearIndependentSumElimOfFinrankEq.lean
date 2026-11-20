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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory

theorem exists_linearIndependent_sumElim_of_finrank_eq {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {n₀ n' : ℕ} (hV : Module.finrank k V = n₀ + n')
    (v : Fin n₀ → V) (hv : LinearIndependent k v) :
    ∃ w : Fin n' → V, LinearIndependent k (Sum.elim v w) := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (Submodule.span k (Set.range v))
  have h1 := Submodule.finrank_add_eq_of_isCompl hQ
  rw [finrank_span_eq_card hv, Fintype.card_fin, hV] at h1
  have h2 : Module.finrank k Q = n' := by omega
  let b := Module.finBasisOfFinrankEq k Q h2
  refine ⟨fun j => (b j : V), hv.sum_type (b.linearIndependent.map' Q.subtype Q.ker_subtype) ?_⟩
  refine hQ.disjoint.mono_right ?_
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact (b j).2

end GlobalTheory
