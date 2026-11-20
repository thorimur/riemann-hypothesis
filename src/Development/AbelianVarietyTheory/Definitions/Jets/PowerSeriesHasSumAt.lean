import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
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

namespace GlobalTheory.ConvSer

def Intg {σ K : Type*} [NormedField K] (S : MvPowerSeries σ K) : Prop :=
  ∀ ν, ‖MvPowerSeries.coeff ν S‖ ≤ 1

def Bdd {σ K : Type*} [NormedField K] (S : MvPowerSeries σ K) : Prop :=
  ∃ C : ℝ, ∀ ν, ‖MvPowerSeries.coeff ν S‖ ≤ C

def Small {σ K : Type*} [NormedField K] (s : MvPowerSeries σ K) : Prop :=
  Intg s ∧ ‖MvPowerSeries.constantCoeff s‖ < 1

def HS {σ K : Type*} [Fintype σ] [NormedField K] (S : MvPowerSeries σ K) (x : σ → K) (a : K) : Prop :=
  HasSum (fun ν : σ →₀ ℕ => MvPowerSeries.coeff ν S * ∏ i, x i ^ ν i) a

def PowerSeriesHasSumAt {K : Type*} [NormedField K] (f : PowerSeries K) (t a : K) : Prop :=
  HasSum (fun n : ℕ => PowerSeries.coeff n f * t ^ n) a

def ev {σ K : Type*} [Fintype σ] [NormedField K] (S : MvPowerSeries σ K) (x : σ → K) : K :=
  ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S * ∏ i, x i ^ ν i

def ev1 {K : Type*} [NormedField K] (f : PowerSeries K) (t : K) : K :=
  ∑' n : ℕ, PowerSeries.coeff n f * t ^ n

def csub {σ τ K : Type*} [Fintype σ] [NormedField K] (s : σ → MvPowerSeries τ K)
    (S : MvPowerSeries σ K) : MvPowerSeries τ K :=
  fun μ => ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i)

def csub1 {τ K : Type*} [NormedField K] (s : MvPowerSeries τ K) (f : PowerSeries K) :
    MvPowerSeries τ K :=
  fun μ => ∑' n : ℕ, PowerSeries.coeff n f * MvPowerSeries.coeff μ (s ^ n)

def shift1 {K : Type*} [NormedField K] (F : MvPowerSeries (Fin 2) K) (y : K) : PowerSeries K :=
  PowerSeries.mk fun a => ∑' b : ℕ,
    MvPowerSeries.coeff (Finsupp.single 0 a + Finsupp.single 1 b) F * y ^ b

def ChordRel {R : Type*} [CommRing R] (u₁ w₁ u₂ w₂ u₃ w₃ : R) : Prop :=
  u₃ * (u₁ * w₂ - u₂ * w₁) ^ 2 * w₁ * w₂ =
      w₃ * ((w₁ - w₂) ^ 2 * w₁ * w₂ - (u₁ * w₂ + u₂ * w₁) * (u₁ * w₂ - u₂ * w₁) ^ 2) ∧
    w₁ * (u₁ * w₂ - u₂ * w₁) = (w₁ - w₂) * (u₃ * w₁ - u₁ * w₃) - w₃ * (u₁ * w₂ - u₂ * w₁)

def IsW {R : Type*} [CommRing R] (a b : R) (w : PowerSeries R) : Prop :=
  PowerSeries.constantCoeff w = 0 ∧
    w = PowerSeries.X ^ 3 + PowerSeries.C a * PowerSeries.X * w ^ 2 + PowerSeries.C b * w ^ 3

def uP (L : PeriodPair) (z : ℂ) : ℂ := -(2 * L.weierstrassP z) / L.derivWeierstrassP z

def wP (L : PeriodPair) (z : ℂ) : ℂ := -2 / L.derivWeierstrassP z

def nMul {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) : PowerSeries R :=
  Nat.rec (motive := fun _ => PowerSeries R) 0
    (fun _ g => MvPowerSeries.subst (![g, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries) n

theorem nMul_zero {R : Type*} [CommRing R] (F : FormalGroup R) : nMul F 0 = 0 := rfl

theorem nMul_succ {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    nMul F (n + 1) = MvPowerSeries.subst
      (![nMul F n, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries := rfl

end GlobalTheory.ConvSer
