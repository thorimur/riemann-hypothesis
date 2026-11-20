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

open MeasureTheory

namespace PositivityTheory.KB.StokesSlices

def Δ (m : ℕ) : Set (Fin m → ℝ) := {t | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1}

def StokesSimplexSubdivision : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (q : ℕ) (f : V [⋀^Fin q]→L[ℝ] ℝ)
    (v : Fin (q + 1) → V),
    f (fun j => v j.succ - v 0) = ∑ i : Fin (q + 1), (-1 : ℝ) ^ (i : ℕ) * f (i.removeNth v)

def SubHyp : Prop :=
  ∀ (m : ℕ) (G : (Fin (m + 1) → ℝ) → ℝ) (i : Fin (m + 1)),
    ∫ s in Δ m, G (i.insertNth (1 - ∑ j, s j) s) = ∫ s in Δ m, G (Fin.cons (1 - ∑ j, s j) s)

def SubSlice : Prop :=
  ∀ (m : ℕ) (i : Fin (m + 1)) (G D : (Fin (m + 1) → ℝ) → ℝ) (W : Set (Fin (m + 1) → ℝ)),
    IsOpen W → Δ (m + 1) ⊆ W → ContinuousOn G W → ContinuousOn D W →
    (∀ t ∈ W, HasDerivAt (fun x => G (Function.update t i x)) (D t) (t i)) →
    ∫ t in Δ (m + 1), D t =
      (∫ s in Δ m, G (i.insertNth (1 - ∑ j, s j) s)) - ∫ s in Δ m, G (i.insertNth 0 s)

end PositivityTheory.KB.StokesSlices
