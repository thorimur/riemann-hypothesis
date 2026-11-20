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
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

namespace GlobalTheory.CompanionTheory.Congruence

open Matrix

theorem finite_quotient_span_pow (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] (ϖ : R) (m : ℕ) (hϖ : Irreducible ϖ) :
    Finite (R ⧸ Ideal.span {ϖ ^ m}) := by
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) :=
    (inferInstance : Finite (IsLocalRing.ResidueField R))
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) m

theorem finite_cosets_principal_congruence :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Finite (IsLocalRing.ResidueField R)] (n : ℕ) (ϖ : R) (m : ℕ), Irreducible ϖ →
      ∃ s : Finset (Matrix (Fin n) (Fin n) R), ∀ A : Matrix (Fin n) (Fin n) R, IsUnit A.det →
        ∃ g ∈ s, ∃ B : Matrix (Fin n) (Fin n) R, IsUnit g.det ∧
          (∀ i j, B i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
          A = g * B := by
  intro R _ _ _ _ n ϖ m hϖ
  classical
  haveI hQ : Finite (R ⧸ Ideal.span {ϖ ^ m}) := finite_quotient_span_pow R ϖ m hϖ
  haveI : Finite (Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {ϖ ^ m})) :=
    inferInstanceAs (Finite (Fin n → Fin n → R ⧸ Ideal.span {ϖ ^ m}))
  haveI : Fintype (Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {ϖ ^ m})) := Fintype.ofFinite _
  have hch : ∀ M : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {ϖ ^ m}),
      ∃ G : Matrix (Fin n) (Fin n) R,
        (∃ A' : Matrix (Fin n) (Fin n) R,
            IsUnit A'.det ∧ A'.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ m})) = M) →
          IsUnit G.det ∧ G.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ m})) = M := by
    intro M
    by_cases h : ∃ A' : Matrix (Fin n) (Fin n) R,
        IsUnit A'.det ∧ A'.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ m})) = M
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose c hc using hch
  refine ⟨Finset.univ.image c, ?_⟩
  intro A hA
  obtain ⟨hgdet, hgf⟩ := hc (A.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}))) ⟨A, hA, rfl⟩
  set g := c (A.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}))) with hg
  have key : ∀ i j, A i j - g i j ∈ Ideal.span {ϖ ^ m} := by
    intro i j
    have h1 := congrFun (congrFun hgf i) j
    simp only [Matrix.map_apply] at h1
    exact Ideal.Quotient.eq.mp h1.symm
  have hB : g⁻¹ * A - 1 = g⁻¹ * (A - g) := by
    rw [mul_sub, Matrix.nonsing_inv_mul g hgdet]
  refine ⟨g, Finset.mem_image_of_mem c (Finset.mem_univ _), g⁻¹ * A, hgdet, ?_, ?_⟩
  · intro i j
    rw [← Matrix.sub_apply, hB, Matrix.mul_apply]
    exact Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact key k j))
  · rw [← mul_assoc, Matrix.mul_nonsing_inv g hgdet, one_mul]

end GlobalTheory.CompanionTheory.Congruence
