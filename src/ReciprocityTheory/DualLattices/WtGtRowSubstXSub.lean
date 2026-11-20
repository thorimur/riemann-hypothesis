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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

def vw (p : Fin ν × ι) : ℕ := 2 ^ (ν - 1 - (p.1 : ℕ))

def wt (A : Fin ν × ι →₀ ℕ) : ℕ := A.sum fun p e => e * vw p

theorem wt_add (A B : Fin ν × ι →₀ ℕ) : wt (A + B) = wt A + wt B := by
  unfold wt
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

def tor (s : ℂ) : Matrix (Fin ν) (Fin ν) ℂ := Matrix.diagonal fun k => s ^ (2 ^ (ν - 1 - (k : ℕ)))

def comp (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : MvPolynomial (Fin ν × ι) ℂ :=
  ∑ A ∈ P.support.filter (fun A => wt A = d), monomial A (coeff A P)

def WtGe (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : Prop := ∀ A ∈ P.support, d ≤ wt A

def WtGt (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : Prop := ∀ A ∈ P.support, d < wt A

theorem WtGt.ge {d : ℕ} {P : MvPolynomial (Fin ν × ι) ℂ} (h : WtGt d P) : WtGe d P :=
  fun A hA => le_of_lt (h A hA)

theorem WtGt.add {d : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGt d P) (h2 : WtGt d Q) :
    WtGt d (P + Q) := by
  intro A hA
  rcases Finset.mem_union.mp (MvPolynomial.support_add hA) with h | h
  exacts [h1 A h, h2 A h]

theorem WtGe.add {d : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGe d P) (h2 : WtGe d Q) :
    WtGe d (P + Q) := by
  intro A hA
  rcases Finset.mem_union.mp (MvPolynomial.support_add hA) with h | h
  exacts [h1 A h, h2 A h]

theorem WtGe.mul {d e : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGe d P) (h2 : WtGe e Q) :
    WtGe (d + e) (P * Q) := by
  intro A hA
  obtain ⟨B, hB, B', hB', rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hA)
  rw [wt_add]
  have := h1 B hB
  have := h2 B' hB'
  omega

end ReciprocityTheory.PGsh
