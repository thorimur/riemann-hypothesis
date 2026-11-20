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
open IsLocalRing Polynomial

namespace GlobalTheory.AbsIntClosedLocal

theorem exists_root_sub_mem_of_eval_mem (T : Type) [CommRing T] [IsLocalRing T] [IsDomain T]
    (hroot : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    ∀ (n : ℕ) (f : T[X]), f.Monic → f.natDegree = n → ∀ a₀ : T, f.eval a₀ ∈ maximalIdeal T →
      ∃ a : T, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal T := by
  intro n
  induction n with
  | zero =>
    intro f hf hdeg a₀ hmem
    have : f = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
      have := hf.coeff_natDegree
      rw [hdeg] at this
      rw [this, map_one]
    rw [this, eval_one] at hmem
    exact absurd ((Ideal.eq_top_iff_one _).2 hmem) (maximalIdeal.isMaximal T).ne_top
  | succ n ih =>
    intro f hf hdeg a₀ hmem
    obtain ⟨r, hr⟩ := hroot f hf (by omega)
    have hrr : f.IsRoot r := hr
    have hdiv := (mul_divByMonic_eq_iff_isRoot (p := f) (a := r)).2 hrr
    set g := f /ₘ (X - C r) with hg
    have hgm : g.Monic := (monic_X_sub_C r).of_mul_monic_left (by rw [hdiv]; exact hf)
    have hgdeg : g.natDegree = n := by
      have := natDegree_divByMonic f (monic_X_sub_C r)
      rw [natDegree_X_sub_C] at this
      rw [hg, this, hdeg]; omega
    have hev : f.eval a₀ = (a₀ - r) * g.eval a₀ := by
      conv_lhs => rw [← hdiv]
      simp [eval_mul]
    rw [hev] at hmem
    rcases (maximalIdeal.isMaximal T).isPrime.mem_or_mem hmem with h | h
    · refine ⟨r, hrr, ?_⟩
      have := (maximalIdeal T).neg_mem h
      simpa using this
    · obtain ⟨a, ha, ha'⟩ := ih g hgm hgdeg a₀ h
      refine ⟨a, ?_, ha'⟩
      rw [← hdiv]
      simp [IsRoot, eval_mul, ha.eq_zero]

theorem henselian_isAlgClosed_pow_surj :
    ∀ (T : Type) [CommRing T] [IsLocalRing T], (IsDomain T ∧ ∀ f : Polynomial T, f.Monic →
      0 < f.natDegree → ∃ x : T, f.eval x = 0) →
      HenselianLocalRing T ∧ IsAlgClosed (ResidueField T) ∧
        ∀ (n : ℕ) (u : Tˣ), 0 < n → ∃ v : Tˣ, v ^ n = u := by
  intro T _ _ ⟨hdom, hroot⟩
  refine ⟨⟨fun f hf a₀ h₁ _ => exists_root_sub_mem_of_eval_mem T hroot _ f hf rfl a₀ h₁⟩, ?_, ?_⟩
  · refine IsAlgClosed.of_exists_root _ (fun p hpm hpirr => ?_)
    have hl : p ∈ lifts (residue T) := (mem_lifts p).2 (map_surjective _ residue_surjective p)
    obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hpm
    obtain ⟨x, hx⟩ := hroot q hqm (by rw [hqd]; exact hpirr.natDegree_pos)
    refine ⟨residue T x, ?_⟩
    rw [← hq, eval_map, eval₂_hom, hx, map_zero]
  · intro n u hn
    obtain ⟨x, hx⟩ := hroot (X ^ n - C (u : T)) (monic_X_pow_sub_C _ hn.ne')
      (by rw [natDegree_X_pow_sub_C]; exact hn)
    have hxn : x ^ n = (u : T) := by
      simp only [eval_sub, eval_pow, eval_X, eval_C] at hx
      exact sub_eq_zero.1 hx
    have hxu : IsUnit x := (isUnit_pow_iff hn.ne').1 (hxn ▸ u.isUnit)
    refine ⟨hxu.unit, Units.ext ?_⟩
    simp [hxn]

end GlobalTheory.AbsIntClosedLocal
