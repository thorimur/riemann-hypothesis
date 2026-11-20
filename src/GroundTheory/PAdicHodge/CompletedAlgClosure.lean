import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Dense
import Mathlib.Analysis.Normed.Field.Instances
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
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

def SpectralAlgClosure : Type _ := AlgebraicClosure K

namespace SpectralAlgClosure

instance : Field (SpectralAlgClosure K) := inferInstanceAs (Field (AlgebraicClosure K))

instance : Algebra K (SpectralAlgClosure K) := inferInstanceAs (Algebra K (AlgebraicClosure K))

instance : IsAlgClosed (SpectralAlgClosure K) := inferInstanceAs (IsAlgClosed (AlgebraicClosure K))

instance : Algebra.IsAlgebraic K (SpectralAlgClosure K) :=
  inferInstanceAs (Algebra.IsAlgebraic K (AlgebraicClosure K))

instance : NormedField (SpectralAlgClosure K) := spectralNorm.normedField K (SpectralAlgClosure K)

instance : NormedAlgebra K (SpectralAlgClosure K) :=
  spectralNorm.normedAlgebra K (SpectralAlgClosure K)

instance : IsUltrametricDist (SpectralAlgClosure K) := IsUltrametricDist.of_normedAlgebra K

theorem norm_eq_spectralNorm (x : SpectralAlgClosure K) :
    ‖x‖ = spectralNorm K (SpectralAlgClosure K) x :=
  rfl

end SpectralAlgClosure

abbrev CompletedAlgClosure : Type _ := UniformSpace.Completion (SpectralAlgClosure K)

namespace CompletedAlgClosure

instance : IsUltrametricDist (CompletedAlgClosure K) := IsUltrametricDist.of_normedAlgebra K

instance : NontriviallyNormedField (CompletedAlgClosure K) where
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    exact ⟨algebraMap K _ x, by rw [norm_algebraMap']; exact hx⟩

instance [CharZero K] : IsAlgClosed (CompletedAlgClosure K) := by
  have : CharZero (CompletedAlgClosure K) :=
    (RingHom.charZero_iff (algebraMap K (CompletedAlgClosure K)).injective).mp inferInstance
  exact IsAlgClosed.of_denseRange (K := SpectralAlgClosure K) UniformSpace.Completion.denseRange_coe

variable (L : Type*) [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]

def embedding : L →ₐ[K] CompletedAlgClosure K :=
  (IsScalarTower.toAlgHom K (SpectralAlgClosure K) (CompletedAlgClosure K)).comp
    (IsAlgClosed.lift : L →ₐ[K] SpectralAlgClosure K)

theorem norm_embedding (x : L) : ‖embedding K L x‖ = ‖x‖ := by
  set ι : L →ₐ[K] SpectralAlgClosure K := IsAlgClosed.lift
  have h1 : ‖embedding K L x‖ = ‖ι x‖ := by
    change ‖((ι x : SpectralAlgClosure K) : CompletedAlgClosure K)‖ = _
    exact UniformSpace.Completion.norm_coe _
  rw [h1, SpectralAlgClosure.norm_eq_spectralNorm]
  have h2 : spectralNorm K (SpectralAlgClosure K) (ι x) = spectralNorm K L x := by
    simp only [spectralNorm, minpoly.algHom_eq ι ι.injective x]
  rw [h2]
  exact (spectralNorm_unique_field_norm_ext (f := NormedField.toAbsoluteValue L)
    (fun k => norm_algebraMap' L k) x).symm

end CompletedAlgClosure

end GroundTheory.PAdicHodge
