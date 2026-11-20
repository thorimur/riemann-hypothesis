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

namespace KStar.Schema

variable {A B G : Type*} [CommRing A] [CommRing B]

def IsCost (ℓ : A) (E : G → A) : Prop :=
  ∀ I : Ideal A, (∀ g, E g - 1 ∈ I) → ℓ ∈ I

def IsCost' (ℓ : A) (E : G → A) : Prop :=
  ℓ ∈ Ideal.span (Set.range fun g => E g - 1)

theorem IsCost.of_dvd {ℓ ℓ' : A} {E : G → A} (h : IsCost ℓ E) (hd : ℓ ∣ ℓ') : IsCost ℓ' E :=
  fun I hI => I.mem_of_dvd hd (h I hI)

theorem IsCost.map {ℓ : A} {E : G → A} (h : IsCost ℓ E) (φ : A →+* B) :
    IsCost (φ ℓ) (fun g => φ (E g)) := by
  intro I hI
  exact h (I.comap φ) fun g => by simpa [Ideal.mem_comap] using hI g

theorem isCost_of_dvd {ℓ : A} {E : G → A} (g : G) (h : E g - 1 ∣ ℓ) : IsCost ℓ E :=
  fun I hI => I.mem_of_dvd h (hI g)

theorem IsCost.dvd_of_forall {ℓ a : A} {E : G → A} (h : IsCost ℓ E) (ha : ∀ g, a ∣ E g - 1) :
    a ∣ ℓ :=
  Ideal.mem_span_singleton.mp (h _ fun g => Ideal.mem_span_singleton.mpr (ha g))

example : IsCost (2 : ℤ) (fun _ : Unit => (3 : ℤ)) := isCost_of_dvd () (by norm_num)

example : ¬ IsCost (1 : ℤ) (fun _ : Unit => (3 : ℤ)) := fun h => by
  have := h.dvd_of_forall (a := 2) fun _ => by norm_num
  norm_num at this

end KStar.Schema
