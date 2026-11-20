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

noncomputable section

namespace PI.ScalDeg

abbrev FrV (T : Type) (N : ℕ) : Type := T × Fin N × Fin N

abbrev Idx (T : Type) (N N' : ℕ) : Type := T × Fin N' × Fin N

def polD {T : Type} {N N' : ℕ} (s : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (y' : T → Matrix (Fin N') (Fin N') ℂ) : MvPolynomial (Idx T N N') ℂ :=
  MvPolynomial.aeval (fun k : FrV T N => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx T N N')) Q

def sclP {T : Type} {N N' : ℕ} (s : T → ℂ) (P : MvPolynomial (Idx T N N') ℂ) : MvPolynomial (Idx T N N') ℂ :=
  MvPolynomial.aeval (fun k : Idx T N N' => MvPolynomial.C (s k.1) * MvPolynomial.X k) P

open Classical in

def HomDeg {T : Type} {N : ℕ} (Qp : MvPolynomial (FrV T N) ℂ) (dg : T → ℕ) : Prop :=
  ∀ α ∈ Qp.support, ∀ τ, (α.sum fun k n => if k.1 = τ then n else 0) = dg τ

def ScalDeg : Prop :=
  ∀ (T : Type) [Fintype T] (N N' : ℕ) (s s' : T → ℂ) (Qp : MvPolynomial (FrV T N) ℂ) (dg : T → ℕ), HomDeg Qp dg →
    ∀ (y' : T → Matrix (Fin N') (Fin N') ℂ),
      polD (fun τ => s τ * s' τ) Qp y' = MvPolynomial.C (∏ τ, s τ ^ dg τ) * polD s' Qp y' ∧
      sclP s (polD s' Qp y') = polD (fun τ => s τ * s' τ) Qp y'

end PI.ScalDeg
