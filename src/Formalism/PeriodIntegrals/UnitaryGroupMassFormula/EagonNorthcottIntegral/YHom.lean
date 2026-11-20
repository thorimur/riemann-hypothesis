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

namespace PI.EagonNorthcottZ

open MvPolynomial

def sgn {D : ℕ} (i : Fin D) (J : Finset (Fin D)) : ℤ := (-1) ^ (J.filter (· < i)).card

abbrev P (D : ℕ) : Type := MvPolynomial (Fin D ⊕ Fin D) ℤ

abbrev S (D : ℕ) : Type := MvPolynomial (Fin D) ℤ

abbrev W (D : ℕ) : Type := Finset (Fin D) → P D

def K {D : ℕ} (t : Fin D → P D) (ω : W D) : W D :=
  fun J => ∑ i ∈ Jᶜ, (sgn i J : P D) * t i * ω (insert i J)

def ct {D : ℕ} (i : Fin D) (ω : W D) : W D :=
  fun J => if i ∈ J then 0 else (sgn i J : P D) * ω (insert i J)

def xs {D : ℕ} : Fin D → P D := fun i => X (Sum.inl i)

def ys {D : ℕ} : Fin D → P D := fun i => X (Sum.inr i)

def YHom {D : ℕ} (a : ℕ) (f : P D) : Prop := ∀ m ∈ f.support, ∑ i, m (Sum.inr i) = a

def Gr {D : ℕ} (a j : ℕ) (ω : W D) : Prop := (∀ J, J.card ≠ j → ω J = 0) ∧ ∀ J, YHom a (ω J)

def inx {D : ℕ} : S D →ₐ[ℤ] P D := rename Sum.inl

def mu {D : ℕ} : P D →ₐ[ℤ] S D := aeval (Sum.elim X X)

def Dop {D : ℕ} (ι : Fin D → Fin D ⊕ Fin D) (i : Fin D) : P D →ₗ[ℤ] P D :=
  (basisMonomials (Fin D ⊕ Fin D) ℤ).constr ℤ fun m =>
    if 0 < m (ι i) ∧ ∀ l, l < i → m (ι l) = 0 then monomial (m - Finsupp.single (ι i) 1) (1 : ℤ) else 0

def hom {D : ℕ} (ι : Fin D → Fin D ⊕ Fin D) (ω : W D) : W D :=
  fun J => if h : J.Nonempty then Dop ι (J.min' h) (ω (J.erase (J.min' h))) else 0

end PI.EagonNorthcottZ
