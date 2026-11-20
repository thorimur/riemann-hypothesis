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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

def TorsionFreeQuotientLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (r : ℕ),
      Module.rank R M = r → ∀ a : R, a ≠ 0 →
        Module.length R (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) ≤
          (r : ℕ∞) * Module.length R (R ⧸ Ideal.span {a})

def KrullAkizukiQuotientLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
      [IsScalarTower R K L] (S : Subalgebra R L) (b : R), b ≠ 0 →
        IsFiniteLength R (S ⧸ Ideal.span {algebraMap R S b})

end GroundTheory.Heights₂.Heights.Model
