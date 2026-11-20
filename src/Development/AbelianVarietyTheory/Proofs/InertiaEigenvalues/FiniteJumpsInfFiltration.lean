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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Presheaf

namespace GlobalTheory

theorem finite_jumps_inf_filtration (E W : Type) [Field E] [AddCommGroup W] [Module E W]
    (D : Submodule E W) (F : ℤ → Submodule E W) (hD : Module.Finite E ↥D)
    (hF : ∀ a, F (a + 1) ≤ F a) :
    {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  have hanti : Antitone F := antitone_int_of_succ_le hF
  have hfin : ∀ a, Module.Finite E ↥(D ⊓ F a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := D) inf_le_left
  have key : ∀ a b : ℤ, D ⊓ F (a + 1) ≠ D ⊓ F a → a < b →
      Module.finrank E ↥(D ⊓ F b) < Module.finrank E ↥(D ⊓ F a) := by
    intro a b ha hab
    haveI := hfin a
    apply Submodule.finrank_lt_finrank_of_lt
    have h1 : D ⊓ F b ≤ D ⊓ F (a + 1) := inf_le_inf_left _ (hanti (by omega))
    have h2 : D ⊓ F (a + 1) < D ⊓ F a := lt_of_le_of_ne (inf_le_inf_left _ (hF a)) ha
    exact lt_of_le_of_lt h1 h2
  refine Set.Finite.of_injOn (f := fun a => Module.finrank E ↥(D ⊓ F a))
    (t := Set.Iic (Module.finrank E ↥D)) ?_ ?_ (Set.finite_Iic _)
  · intro a _
    exact Submodule.finrank_mono inf_le_left
  · intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (key a b ha h).ne'
    · exact h
    · exact absurd hab (key b a hb h).ne

end GlobalTheory
