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
import Mathlib.RingTheory.OrderOfVanishing.Basic
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

open IsDedekindDomain Function

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R]

theorem isFiniteLength_of_isTorsion [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {X : Type*} [AddCommGroup X] [Module R X] [Module.Finite R X] (hX : Module.IsTorsion R X) :
    IsFiniteLength R X := by
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hX
  have hr' : Module.IsTorsionBySet R X (Ideal.span {r}) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    exact fun x ↦ Submodule.mem_annihilator.mp hr x trivial
  letI := hr'.module
  haveI : Module.Finite (R ⧸ Ideal.span {r}) X := Module.Finite.of_restrictScalars_finite R _ _
  haveI : IsArtinian R (R ⧸ Ideal.span {r}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_span_singleton R hr0)).2
  haveI : IsArtinianRing (R ⧸ Ideal.span {r}) := isArtinian_of_tower R inferInstance
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance,
    isArtinian_of_surjective_algebraMap (R := R ⧸ Ideal.span {r}) Ideal.Quotient.mk_surjective⟩

section Submodules

variable (T : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S]

variable {V : Type*} [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

end Submodules

end General

section Dedekind

variable {O : Type*} [CommRing O] [IsDedekindDomain O]

section Torsion

variable {X : Type*} [AddCommGroup X] [Module O X] [Module.Finite O X]

variable [Ring.HasFiniteQuotients O]

variable [Module.Free ℤ O]

end Torsion

section Lattices

variable [Ring.HasFiniteQuotients O] [Module.Free ℤ O]

end Lattices

end Dedekind

end GlobalTheory
