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

open scoped TensorProduct

namespace GlobalTheory

theorem isBezout_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W] [IsBezout W]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : IsBezout B := by
  refine ⟨fun J hJ => ?_⟩
  have hfin : Module.Finite B J := Module.Finite.iff_fg.2 hJ
  have htB : Submodule.torsion W B = ⊥ :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.1 inferInstance
  have hW : Module.Flat W J := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have hx : (x : B) ∈ Submodule.torsion W B := ⟨a, congrArg Subtype.val ha⟩
    rw [htB, Submodule.mem_bot] at hx
    exact (Submodule.mem_bot W).2 (Subtype.ext hx)
  have hB : Module.Flat B J := Algebra.FormallyUnramified.flat_of_restrictScalars W B J
  have hfree : Module.Free B J := Module.free_of_flat_of_isLocalRing
  rw [← Submodule.rank_le_one_iff_isPrincipal]
  exact (Submodule.rank_le J).trans (Module.rank_self B).le

theorem isAlgebraic_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W]
    [CommRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : Algebra.IsAlgebraic W B := by
  let K := FractionRing W
  have hfin : Module.Finite K (K ⊗[W] B) := Algebra.FormallyUnramified.finite_of_free K _
  have halg : Algebra.IsAlgebraic K (K ⊗[W] B) := inferInstance
  have hK : Algebra.IsAlgebraic W K := IsLocalization.isAlgebraic K (nonZeroDivisors W)
  have halgW : Algebra.IsAlgebraic W (K ⊗[W] B) := Algebra.IsAlgebraic.trans W K _
  exact Algebra.IsAlgebraic.of_injective
    (Algebra.TensorProduct.includeRight (R := W) (A := K) (B := B))
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective W K))

theorem valuationRing_of_flat_of_formallyUnramified :
    ∀ (W B : Type) [CommRing W] [IsDomain W] [ValuationRing W] [CommRing B] [IsDomain B]
      [IsLocalRing B] [Algebra W B] [Module.Flat W B] [Algebra.EssFiniteType W B]
      [Algebra.FormallyUnramified W B], ValuationRing B ∧ Algebra.IsAlgebraic W B := by
  intro W B _ _ _ _ _ _ _ _ _ _
  have := isBezout_of_flat_of_formallyUnramified W B
  exact ⟨inferInstance, isAlgebraic_of_flat_of_formallyUnramified W B⟩

end GlobalTheory
