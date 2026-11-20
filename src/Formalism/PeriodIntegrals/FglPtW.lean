import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PowerSeries.Substitution
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

noncomputable section

namespace PI.FglPtW

def SerOver {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (F : MvPowerSeries σ K) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ S

def PtOver {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (a : MvPowerSeries σ K) : Prop :=
  SerOver S a ∧ MvPowerSeries.constantCoeff a = 0

def AddGen : Prop :=
  ∀ (K : Type) [CommRing K] (S : Subring K) (l ex : PowerSeries K),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    SerOver S (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex) →
    ∀ (σ : Type) (a b : MvPowerSeries σ K), PtOver S a → PtOver S b →
      PtOver S (PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex)

def MulGen : Prop :=
  ∀ (K : Type) [CommRing K] (S : Subring K) (l ex : PowerSeries K),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    ∀ c : K, SerOver S (PowerSeries.subst
      (MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex) →
    ∀ (σ : Type) (a : MvPowerSeries σ K), PtOver S a →
      PtOver S (PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex)

def LinGen : Prop :=
  ∀ (K : Type) [CommRing K] (S : Subring K) (l ex : PowerSeries K),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    SerOver S (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex) →
    ∀ (ι : Type) [Fintype ι] (c : ι → K),
    (∀ j, SerOver S (PowerSeries.subst
      (MvPowerSeries.C (c j) * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex)) →
    ∀ (σ : Type) (a : ι → MvPowerSeries σ K), (∀ j, PtOver S (a j)) →
      PtOver S (PowerSeries.subst (∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) ex)

end PI.FglPtW

end
