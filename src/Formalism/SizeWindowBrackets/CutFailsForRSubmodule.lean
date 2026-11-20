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

namespace Formalism.LFunctionChainParameters.DiagonalSublatticeLength

open scoped Pointwise

section defs

variable {R K W : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup W] [Module K W] [Module R W]
  [IsScalarTower R K W]

def latV (M : Submodule R W) (V : Submodule K W) : Submodule R W :=
  M ⊓ V.restrictScalars R

def cutN (ϖ : R) (τ : ℕ) (M N : Submodule R W) (V : Submodule K W) : Submodule R W :=
  N ⊓ ϖ ^ τ • M ⊓ V.restrictScalars R

end defs

def LemmaC : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (W : Type) [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W] [FiniteDimensional K W]
    (d : ℕ) (M : Submodule R W) (b : Module.Basis (Fin d) R M), Submodule.span K (M : Set W) = ⊤ →
  ∀ (e : Fin d → ℕ) (N : Submodule R W), N = Submodule.span R (Set.range fun i => ϖ ^ e i • (b i : W)) →
  ∀ (τ : ℕ) (V : Submodule K W),
    cutN ϖ τ M N V ≤ ϖ ^ τ • latV M V ∧
    (ϖ ^ τ • M) ⊓ V.restrictScalars R = ϖ ^ τ • latV M V ∧
    Module.length R (latV M V ⧸ (cutN ϖ τ M N V).comap (latV M V).subtype) ≤
      ((Module.finrank R (latV M V) * τ + ∑ i, (e i - τ) : ℕ) : ℕ∞)

def ClaimC : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (W : Type) [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W] [FiniteDimensional K W]
    (d : ℕ) (M : Submodule R W) (b : Module.Basis (Fin d) R M), Submodule.span K (M : Set W) = ⊤ →
  ∀ (e : Fin d → ℕ) (N : Submodule R W), N = Submodule.span R (Set.range fun i => ϖ ^ e i • (b i : W)) →
  ∀ (τ : ℕ) (V : Submodule K W),
    Module.length R ((ϖ ^ τ • latV M V : Submodule R W) ⧸
        (cutN ϖ τ M N V).comap (ϖ ^ τ • latV M V : Submodule R W).subtype) ≤ ((∑ i, (e i - τ) : ℕ) : ℕ∞) ∧
    Module.length R (latV M V ⧸ (ϖ ^ τ • latV M V).comap (latV M V).subtype) =
      ((Module.finrank R (latV M V) * τ : ℕ) : ℕ∞)

def CutFailsForRSubmodule : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K],
    let M : Submodule R K := Submodule.span R {1}
    let V : Submodule R K := Submodule.span R {algebraMap R K ϖ}
    ϖ • M ⊓ V ≠ ϖ • (M ⊓ V)

end Formalism.LFunctionChainParameters.DiagonalSublatticeLength
