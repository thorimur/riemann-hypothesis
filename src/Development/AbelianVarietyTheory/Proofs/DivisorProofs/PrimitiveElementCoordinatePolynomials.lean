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
import Std.Tactic.BVDecide.Normalize.Prop
open Polynomial

namespace GlobalTheory

theorem commonDenom_finset {k C : Type} [Field k] [Field C] [Algebra k C] {d : ℕ}
    (t : Fin d → C) (F : Finset C)
    (hF : ∀ y ∈ F, y ∈ IntermediateField.adjoin k (Set.range t)) :
    ∃ Δ : MvPolynomial (Fin d) k, MvPolynomial.aeval t Δ ≠ 0 ∧
      ∀ y ∈ F, ∃ r : MvPolynomial (Fin d) k, MvPolynomial.aeval t r = MvPolynomial.aeval t Δ * y := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a F ha ih =>
    obtain ⟨Δ₀, hΔ₀, hF₀⟩ := ih (fun y hy => hF y (Finset.mem_insert_of_mem hy))
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_range_iff k t a).1
      (hF a (Finset.mem_insert_self a F))
    by_cases hs : MvPolynomial.aeval t s = 0
    · refine ⟨Δ₀, hΔ₀, ?_⟩
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · refine ⟨0, ?_⟩
        rw [hrs, hs, div_zero]; simp
      · exact hF₀ y hy
    · refine ⟨Δ₀ * s, by simp [hΔ₀, hs], ?_⟩
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · refine ⟨Δ₀ * r, ?_⟩
        rw [hrs, map_mul, map_mul]
        field_simp
      · obtain ⟨r', hr'⟩ := hF₀ y hy
        refine ⟨r' * s, ?_⟩
        rw [map_mul, map_mul, hr']; ring

theorem commonDenominator :
    ∀ (k C : Type) [Field k] [Field C] [Algebra k C] (d m : ℕ) (t : Fin d → C) (θ : C)
      (x : Fin m → C), IsAlgebraic (IntermediateField.adjoin k (Set.range t)) θ →
      (∀ j, x j ∈ IntermediateField.adjoin (IntermediateField.adjoin k (Set.range t)) {θ}) →
      ∃ (Δ : MvPolynomial (Fin d) k) (Q : Fin m → Polynomial (MvPolynomial (Fin d) k)),
        MvPolynomial.aeval t Δ ≠ 0 ∧
        ∀ j, Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) =
          MvPolynomial.aeval t Δ * x j := by
  intro k C _ _ _ d m t θ x hθ hx
  classical
  set K0 := IntermediateField.adjoin k (Set.range t) with hK0
  have hp : ∀ j, ∃ p : K0[X], Polynomial.aeval θ p = x j := by
    intro j
    have h := hx j
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθ,
      Algebra.adjoin_singleton_eq_range_aeval] at h
    obtain ⟨p, hp⟩ := h
    exact ⟨p, hp⟩
  choose p hpx using hp
  let F : Finset C := Finset.univ.biUnion
    (fun j => (p j).support.image (fun i => (((p j).coeff i : K0) : C)))
  have hF : ∀ y ∈ F, y ∈ K0 := by
    intro y hy
    simp only [F, Finset.mem_biUnion, Finset.mem_image] at hy
    obtain ⟨j, -, i, -, rfl⟩ := hy
    exact ((p j).coeff i).2
  obtain ⟨Δ, hΔ, hΔF⟩ := commonDenom_finset t F hF
  have hQ : ∀ j, ∃ Q : Polynomial (MvPolynomial (Fin d) k),
      Q.map (MvPolynomial.aeval t).toRingHom =
        Polynomial.C (MvPolynomial.aeval t Δ) * (p j).map K0.val.toRingHom := by
    intro j
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
    by_cases hn : n ∈ (p j).support
    · obtain ⟨r, hr⟩ := hΔF _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
        Finset.mem_image.2 ⟨n, hn, rfl⟩⟩)
      exact ⟨r, by simpa using hr⟩
    · rw [Polynomial.notMem_support_iff.1 hn]
      exact ⟨0, by simp⟩
  choose Q hQ using hQ
  refine ⟨Δ, Q, hΔ, ?_⟩
  intro j
  rw [← Polynomial.eval_map, hQ j, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
    ← hpx j, Polynomial.aeval_def]
  rfl

end GlobalTheory
