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

namespace Formalism.FourierDecayAlt.X

open Matrix

def MinorScale : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (κ : K) (l : ℕ) (hl : l ≤ n),
    ((Matrix.of (fun a b : Fin n => κ ^ ((a : ℕ) + (b : ℕ)) * Z a b)).submatrix
        (Fin.castLE hl) (Fin.castLE hl)).det =
      κ ^ (l * (l - 1)) * (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def MinorScaleGen : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (α β : Fin n → K) (l : ℕ) (hl : l ≤ n),
    ((Matrix.of (fun a b : Fin n => α a * β b * Z a b)).submatrix
        (Fin.castLE hl) (Fin.castLE hl)).det =
      (∏ i : Fin l, α (Fin.castLE hl i) * β (Fin.castLE hl i)) *
        (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def ScaleExponents : Prop :=
  (∀ l : ℤ, l * (l - 1) - (l - 1) * (l - 2) = 2 * l - 2) ∧
  (∀ i s : ℤ, (i - 1 + s) * (i - 2 + s) - (i - 1) * (i - 2) = s * (2 * i + s - 3))

def GermPowers : Prop :=
  ∀ s : ℚ, -2 * ((s - 1) * (s + 2) / 2) + 3 * (s - 1) = -(s - 1) ^ 2 ∧
    -2 * (s - 1) + (s - 1) + s * (s - 1) = (s - 1) ^ 2

def SlicePowers : Prop :=
  ∀ s M : ℤ, 2 * (s - 1) * (M + s - 2) - 2 * (s - 1) * (M - 2) - 2 * (s - 1) = 2 * (s - 1) ^ 2

def WeightExponent : Prop :=
  ∀ k r j s : ℤ,
    (k + 2 * r + 1 - 2 * (j - 1)) = k + 1 + 2 * (r - j + 1) ∧
    (k + 2 * r + 1 - 2 * ((r + 1) - 1)) = k + 1 ∧
    2 * s * (k - 1) + 4 * s * (r + 1 - j) + 2 * s * (s - 1) =
      2 * s * ((k + 2 * r + 1 - 2 * (j - 1)) + s - 3)

end Formalism.FourierDecayAlt.X
