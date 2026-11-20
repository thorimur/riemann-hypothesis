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
import Mathlib.LinearAlgebra.Matrix.PosDef
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

open Matrix
open scoped ComplexOrder

namespace PI

def UnitaryDense : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ),
    (∀ u : Matrix (Fin n) (Fin n) ℂ, uᴴ * u = 1 →
      MvPolynomial.eval (fun x : Fin n × Fin n => u x.1 x.2) P = 0) → P = 0

def FramesDense : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (G τ).PosDef) →
    ∀ P : MvPolynomial (ι × Fin n × Fin n) ℂ,
      (∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * G τ * y τ = 1) →
        MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P = 0) → P = 0

def FramesDenseDet : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (G τ).PosDef) →
    ∀ (s t : ι → ℤ) (P Q : MvPolynomial (ι × Fin n × Fin n) ℂ),
      (∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * G τ * y τ = 1) →
        (∏ τ, (y τ).det ^ s τ) * MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P =
        (∏ τ, (y τ).det ^ t τ) * MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) Q) →
      ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ).det ≠ 0) →
        (∏ τ, (y τ).det ^ s τ) * MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P =
        (∏ τ, (y τ).det ^ t τ) * MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) Q

end PI
