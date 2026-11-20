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
import Mathlib.RingTheory.SimpleRing.Principal
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

open Polynomial

noncomputable section

namespace PI.SqfLab

def Exc (g d ℓ : ℕ) : Prop := ℓ.Prime ∧ g ^ d < ℓ ^ (4 * padicValNat ℓ (g ^ d - 1))

def BB (N g : ℕ) : Set ℕ := {g} ∪ {ℓ | ∃ d, 1 ≤ d ∧ d ≤ N ∧ Exc g d ℓ}

def primeToPart (ℓ : ℕ) {M : Type*} [Monoid M] (x : M) : M :=
  x ^ (ℓ ^ (orderOf x).factorization ℓ *
    (((ℓ ^ (orderOf x).factorization ℓ : ℕ) :
      ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ))⁻¹).val)

abbrev Fbar (g : ℕ) [Fact g.Prime] : Type := AlgebraicClosure (ZMod g)

def rootsBar {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : Multiset (Fbar g) :=
  (f.map (algebraMap (ZMod g) (Fbar g))).roots

def IsLab (g r : ℕ) (f : (ZMod g)[X]) : Prop :=
  f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0

def Eii (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  IsLab g r f ∧ Squarefree f ∧ ¬ (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ BB r g →
    ∀ x ∈ rootsBar f, ∀ y ∈ rootsBar f, primeToPart ℓ x = primeToPart ℓ y → x = y)

def Eiii (g r : ℕ) [Fact g.Prime] (c : (ZMod g)ˣ) (f : (ZMod g)[X]) : Prop :=
  IsLab g r f ∧ Squarefree f ∧ ¬ (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ g → ∀ x ∈ rootsBar f,
    primeToPart ℓ x ≠ primeToPart ℓ (algebraMap (ZMod g) (Fbar g) (c : ZMod g)))

def Eiv (g r a : ℕ) (f : (ZMod g)[X]) : Prop :=
  IsLab g r f ∧ Squarefree f ∧ ∃ q : (ZMod g)[X], q ∣ f ∧ q.natDegree = a

def Ev (g r : ℕ) (f : (ZMod g)[X]) : Prop :=
  IsLab g r f ∧ Squarefree f ∧ ¬ ∃ q : (ZMod g)[X], Irreducible q ∧ q ∣ f ∧ q.natDegree.Prime ∧
    r < 2 * q.natDegree ∧ q.natDegree + 3 ≤ r

end PI.SqfLab
