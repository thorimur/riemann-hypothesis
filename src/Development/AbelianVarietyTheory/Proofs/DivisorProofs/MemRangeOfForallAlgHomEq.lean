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
open scoped TensorProduct

namespace GlobalTheory

open Polynomial in

theorem mem_range_of_forall_algHom_eq :
    ∀ (F K₀ : Type) [Field F] [CharZero F] [Field K₀] [Algebra F K₀], Algebra.IsAlgebraic F K₀ →
      ∀ t : K₀, (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (φ₁ φ₂ : K₀ →ₐ[F] Ω), φ₁ t = φ₂ t) →
        t ∈ Set.range (algebraMap F K₀) := by
  intro F K₀ _ _ _ _ halg t ht
  classical
  have hint : IsIntegral F t := (Algebra.IsAlgebraic.isAlgebraic t).isIntegral
  set Ω := AlgebraicClosure K₀
  have hsep : (minpoly F t).Separable := (minpoly.irreducible hint).separable
  have hsplit : Splits ((minpoly F t).map (algebraMap F Ω)) := IsAlgClosed.splits _
  have hcard := card_rootSet_eq_natDegree (K := Ω) hsep hsplit
  by_contra hnot
  have h1 : (minpoly F t).natDegree ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp h
    exact hnot ⟨c, hc⟩
  have hpos := minpoly.natDegree_pos hint
  have hlt : 1 < Fintype.card ((minpoly F t).rootSet Ω) := by omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hlt
  have hK' : ∀ s : K₀, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F Ω)) :=
    fun s => ⟨(Algebra.IsAlgebraic.isAlgebraic s).isIntegral, IsAlgClosed.splits _⟩
  have ha : aeval (a : Ω) (minpoly F t) = 0 :=
    (mem_rootSet.mp a.2).2
  have hb : aeval (b : Ω) (minpoly F t) = 0 :=
    (mem_rootSet.mp b.2).2
  obtain ⟨φa, hφa⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hK' ha
  obtain ⟨φb, hφb⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hK' hb
  apply hab
  apply Subtype.ext
  rw [← hφa, ← hφb]
  exact ht Ω φa φb

end GlobalTheory
