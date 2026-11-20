import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Instances
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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open NumberField

instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

def logIdeal {O A : Type} [CommRing O] [NormedField A] (ι : O →+* A) (I : Ideal O) : ℝ :=
  Real.log (⨆ a : I, ‖ι (a : O)‖)

structure LogNorms (k : Type) [Field k] where

  inf : (k →+* ℂ) → ℝ

  fin : ∀ p : Nat.Primes, (k →+* ℂ_[p]) → ℝ

namespace LogNorms

variable {k : Type} [Field k] [NumberField k]

def finSum (N : LogNorms k) (p : Nat.Primes) : ℝ := ∑ ι : k →+* ℂ_[p], N.fin p ι

def IsAdelic (N : LogNorms k) : Prop := {p : Nat.Primes | ∃ ι, N.fin p ι ≠ 0}.Finite

def deg (N : LogNorms k) : ℝ := -((∑ s : k →+* ℂ, N.inf s) + ∑ᶠ p, N.finSum p) / Module.finrank ℚ k

def ofElt (x : k) : LogNorms k := ⟨fun s => Real.log ‖s x‖, fun _ ι => Real.log ‖ι x‖⟩

def ext {k' : Type} [Field k'] (f : k →+* k') (N : LogNorms k) : LogNorms k' :=
  ⟨fun s => N.inf (s.comp f), fun p ι => N.fin p (ι.comp f)⟩

theorem deg_const (t : ℝ) : deg (⟨fun _ => t, fun _ _ => 0⟩ : LogNorms k) = -t := by
  have h : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  simp [deg, finSum, Embeddings.card]
  field_simp

end LogNorms

end GlobalTheory.CompanionTheory.Ar.Fl
