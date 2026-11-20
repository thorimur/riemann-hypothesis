import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
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

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

def WFixed {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R) : Prop :=
  constantCoeff w = 0 ∧
  w = X ^ 3 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * X * w ^ 2
      + C W.a₆ * w ^ 3

def WSeriesUnique : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R), ∃! w : PowerSeries R, WFixed W w

def WSeriesLead : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R), WFixed W w →
    coeff 0 w = 0 ∧ coeff 1 w = 0 ∧ coeff 2 w = 0 ∧ coeff 3 w = 1

section Points

variable {K : Type u} [Field K] {σ : Type}

def xOf (w : PowerSeries K) (s : MvPowerSeries σ K) : FractionRing (MvPowerSeries σ K) :=
  algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s /
    algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)

def yOf (w : PowerSeries K) (s : MvPowerSeries σ K) : FractionRing (MvPowerSeries σ K) :=
  -1 / algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)

end Points

def WPoint : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∀ (σ : Type) [Finite σ] (s : MvPowerSeries σ K), MvPowerSeries.constantCoeff s = 0 → s ≠ 0 →
      (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
        (xOf w s) (yOf w s)

def WFormalGroup : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∃ F : FormalGroup K,
      (∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F.toPowerSeries ∈
        Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) ∧
      let z₁ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0
      let z₂ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1
      let W' := (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine
      let ℓ := (yOf w z₁ - yOf w z₂) / (xOf w z₁ - xOf w z₂)
      xOf w F.toPowerSeries = W'.addX (xOf w z₁) (xOf w z₂) ℓ ∧
      yOf w F.toPowerSeries = W'.addY (xOf w z₁) (xOf w z₂) (yOf w z₁) ℓ

end Formalism.ELL
