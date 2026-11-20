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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

namespace GlobalTheory.AdaptedFamilyIwasawaDecomposition

theorem exists_adapted_family (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)) (hIL : I ≤ L)
    (hg : Module.finrank ℚ ↥L = g) :
    ∃ rk ≤ g, ∃ (ε : Fin g → Fin r → ℚ), LinearIndependent ℚ ε ∧ (∀ (i : Fin g), ε i ∈ L) ∧
      (∀ (i : Fin g), (↑i : ℕ) < rk → ε i ∈ I) ∧
      ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i : Fin g | (↑i : ℕ) < rk}) := by
  obtain ⟨C₀, hC₀⟩ := I.exists_isCompl
  have hdis : Disjoint I (C₀ ⊓ L) := hC₀.disjoint.mono_right inf_le_left
  have hsup : I ⊔ (C₀ ⊓ L) = L := by
    rw [← sup_inf_assoc_of_le C₀ hIL, hC₀.sup_eq_top, top_inf_eq]
  have hCL : C₀ ⊓ L ≤ L := inf_le_right
  generalize C₀ ⊓ L = C at hdis hsup hCL
  have hdim : Module.finrank ℚ I + Module.finrank ℚ C = g := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq I C
    rw [hsup, hdis.eq_bot, finrank_bot, hg] at h
    omega
  obtain ⟨k, ⟨bI⟩⟩ : ∃ k, Nonempty (Module.Basis (Fin k) ℚ I) := ⟨_, ⟨Module.finBasis ℚ I⟩⟩
  obtain ⟨m, ⟨bC⟩⟩ : ∃ m, Nonempty (Module.Basis (Fin m) ℚ C) := ⟨_, ⟨Module.finBasis ℚ C⟩⟩
  rw [Module.finrank_eq_card_basis bI, Module.finrank_eq_card_basis bC, Fintype.card_fin,
    Fintype.card_fin] at hdim
  clear hg
  subst hdim
  let u : Fin k → Fin r → ℚ := I.subtype ∘ bI
  let v : Fin m → Fin r → ℚ := C.subtype ∘ bC
  have hu : LinearIndependent ℚ u := bI.linearIndependent.map' _ (Submodule.ker_subtype I)
  have hv : LinearIndependent ℚ v := bC.linearIndependent.map' _ (Submodule.ker_subtype C)
  have huI : ∀ i, u i ∈ I := fun i => (bI i).2
  have hvC : ∀ i, v i ∈ C := fun i => (bC i).2
  have hus : Submodule.span ℚ (Set.range u) = I := by
    rw [Set.range_comp, ← Submodule.map_span, bI.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hvs : Submodule.span ℚ (Set.range v) ≤ C := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hvC i
  have hli : LinearIndependent ℚ (Sum.elim u v) :=
    hu.sum_type hv (by rw [hus]; exact hdis.mono_right hvs)
  refine ⟨k, Nat.le_add_right k m, Sum.elim u v ∘ finSumFinEquiv.symm,
    hli.comp _ finSumFinEquiv.symm.injective, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    rcases j with j | j
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using hIL (huI j)
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr] using hCL (hvC j)
  · intro i hi
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    rcases j with j | j
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using huI j
    · simp at hi
  · intro x hx
    rw [← hus] at hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨j, rfl⟩
    refine ⟨finSumFinEquiv (Sum.inl j), ?_, ?_⟩
    · simp
    · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]

end GlobalTheory.AdaptedFamilyIwasawaDecomposition
