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

theorem UpperTheory.Reformulated.B.Yha6.main :
    ∀ (Λ : Type) [inst : AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : Submodule ℤ Λ),
      (∀ (v : Λ) (n : ℤ), n ≠ (0 : ℤ) → n • v ∈ N → v ∈ N) →
        ∃ (k : ℕ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n),
          Function.Injective f ∧ Submodule.span ℤ (Set.range fun (i : Fin k) ↦ (b : Fin n → Λ) (f i)) = N := by
  intro Λ _ _ _ N hsat
  obtain ⟨k, snf⟩ := Submodule.smithNormalForm (Module.finBasis ℤ Λ) N
  refine ⟨k, _, snf.bM, snf.f, snf.f.injective, ?_⟩
  have ha : ∀ i, snf.a i ≠ 0 := by
    intro i h
    have h1 := snf.snf i
    rw [h, zero_smul] at h1
    exact snf.bN.ne_zero i (Subtype.ext h1)
  have hmem : ∀ i, snf.bM (snf.f i) ∈ N := by
    intro i
    apply hsat _ (snf.a i) (ha i)
    rw [← snf.snf i]
    exact (snf.bN i).2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  · intro x hx
    have hx' : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (Set.range snf.bN) := by
      rw [snf.bN.span_eq]; trivial
    have := Submodule.apply_mem_span_image_of_mem_span N.subtype hx'
    simp only [Submodule.subtype_apply] at this
    refine Submodule.span_le.mpr ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp only [Submodule.subtype_apply, snf.snf i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
