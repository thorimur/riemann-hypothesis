import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

namespace ZetaZeros.D.EllReg

open scoped ContDiff

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def ev {d : ℕ} (j : Fin d) : E d := EuclideanSpace.single j (1 : ℝ)

noncomputable def dw {d : ℕ} : List (Fin d) → (E d → ℂ) → E d → ℂ
  | [], f => f
  | j :: w, f => fun x => fderiv ℝ (dw w f) x (ev j)

noncomputable def trOp {d : ℕ} (m : ℕ) (b : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (φ : E d → ℂ)
    (x : E d) : ℂ :=
  ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
    (-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * φ y) x

structure Sys (d : ℕ) (ι : Type) where
  ord : ι → ℕ
  a : ι → (n : ℕ) → (Fin n → Fin d) → E d → ℂ

noncomputable def Sys.tr {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι) (φ : E d → ℂ) (x : E d) : ℂ :=
  trOp (P.ord i) (P.a i) φ x

noncomputable def Sys.symb {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι) (x ξ : E d) : ℂ :=
  ∑ w : Fin (P.ord i) → Fin d, P.a i (P.ord i) w x * ∏ l, ((ξ (w l) : ℝ) : ℂ)

def WeakSol {d : ℕ} {ι : Type} (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ) : Prop :=
  ∀ (i : ι) (φ : E d → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x, u x * P.tr i φ x = 0

def Hyp {d : ℕ} {ι : Type} (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ) : Prop :=
  IsOpen U ∧ (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) ∧
    (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) ∧ ContinuousOn u U ∧ WeakSol P U u

def Internal : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ),
    Hyp P U u → ContDiffOn ℝ ∞ u U

end ZetaZeros.D.EllReg
