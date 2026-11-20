import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.DedekindZeta
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

open NumberField

noncomputable section

namespace PI.Residue

def idealZeta (E : Type) [Field E] [NumberField E] (s : ℝ) : ℝ :=
  ∑' I : {I : Ideal (𝓞 E) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ) ^ (-s)

def zetaR (s : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-s)

def ZetaLePow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (s : ℝ), 1 < s →
    Summable (fun I : {I : Ideal (𝓞 E) // I ≠ ⊥} => (Ideal.absNorm I.1 : ℝ) ^ (-s)) ∧
      idealZeta E s ≤ zetaR s ^ Module.finrank ℚ E

def ZetaRLe : Prop := ∀ s : ℝ, 1 < s → zetaR s ≤ 1 + 1 / (s - 1)

def HeckeLower : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (s : ℝ), 1 < s →
    Summable (fun I : {I : Ideal (𝓞 E) // I ≠ ⊥} => (Ideal.absNorm I.1 : ℝ) ^ (-s)) →
    dedekindZeta_residue E ≤
      (4 : ℝ) ^ s * (2 * Real.pi) ^ Module.finrank ℚ E * ((|discr E| : ℤ) : ℝ) ^ ((s - 1) / 2) * idealZeta E s

def Optimise : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (m : ℕ) (D : ℝ), 2 ≤ m → 4 / 9 * (3 * Real.pi / 4) ^ m ≤ D →
    ∃ s : ℝ, 1 < s ∧
      (4 : ℝ) ^ s * (2 * Real.pi) ^ m * D ^ ((s - 1) / 2) * (1 + 1 / (s - 1)) ^ m ≤
        (C * Real.log (D ^ ((1 : ℝ) / m))) ^ m

end PI.Residue
