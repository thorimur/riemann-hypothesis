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

namespace Formalism.BasicNotions.Examples₂.NZ

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {V : Type*} [AddCommGroup V] [Module R V]

def glue (A : HeightOneSpectrum R → Submodule R V) : Submodule R V := ⨅ w, A w

theorem not_le_of_prod {S : Finset (HeightOneSpectrum R)} (m : HeightOneSpectrum R → ℕ) (w : HeightOneSpectrum R)
    (hw : w ∉ S) : ¬ (∏ v ∈ S, v.asIdeal ^ m v) ≤ w.asIdeal := by
  intro h
  obtain ⟨v, hv, hle⟩ := (w.isPrime.prod_le).mp h
  have h2 : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hle
  have h3 : v.asIdeal = w.asIdeal := (v.isMaximal).eq_of_le w.isPrime.ne_top h2
  exact hw (HeightOneSpectrum.ext h3 ▸ hv)

theorem glue_loc (A : HeightOneSpectrum R → Submodule R V)
    (hsat : ∀ w (s : R), s ∉ w.asIdeal → ∀ x, s • x ∈ A w → x ∈ A w)
    (hfin : ∀ x : V, {w | x ∉ A w}.Finite)
    (habs : ∀ w (x : V), ∃ m : ℕ, ∀ a ∈ w.asIdeal ^ m, a • x ∈ A w)
    (w : HeightOneSpectrum R) (x : V) :
    (∃ s : R, s ∉ w.asIdeal ∧ s • x ∈ glue A) ↔ x ∈ A w := by
  constructor
  · rintro ⟨s, hs, hx⟩
    exact hsat w s hs x ((Submodule.mem_iInf _).mp hx w)
  · intro hx
    classical
    choose m hm using fun v => habs v x
    have hw : w ∉ (hfin x).toFinset := by simpa using hx
    obtain ⟨s, hsI, hsw⟩ := SetLike.not_le_iff_exists.mp (not_le_of_prod m w hw)
    refine ⟨s, hsw, (Submodule.mem_iInf _).mpr fun v => ?_⟩
    by_cases hv : x ∈ A v
    · exact (A v).smul_mem s hv
    · exact hm v s (Ideal.prod_le_inf.trans (Finset.inf_le ((hfin x).mem_toFinset.mpr hv)) hsI)

end Formalism.BasicNotions.Examples₂.NZ
