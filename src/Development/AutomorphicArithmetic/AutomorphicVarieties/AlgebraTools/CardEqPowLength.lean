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

open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field {A X : Type} [CommRing A] [IsLocalRing A] [AddCommGroup X] [Module A X] [IsSimpleModule A X] : Nonempty (X ≃ ResidueField A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A X)
  have : I = maximalIdeal A := IsLocalRing.eq_maximalIdeal hI
  subst this
  exact ⟨e.toEquiv⟩

private theorem UpperTheory.V.AlgebraTools.card_finite_length_module {A : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] {X : Type} [AddCommGroup X] [Module A X] (h : IsFiniteLength A X) :
    Finite X ∧ Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    refine ⟨Finite.of_subsingleton, ?_⟩
    rw [Module.length_eq_zero]
    simp [Nat.card_eq_one_iff_unique]
  | @of_simple_quotient M _ _ N _ hN ih =>
    obtain ⟨hfin, hcard⟩ := ih
    obtain ⟨e⟩ := UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field (A := A) (X := M ⧸ N)
    have hq : Nat.card (M ⧸ N) = Nat.card (ResidueField A) := Nat.card_congr e
    have hNt : Module.length A N ≠ ⊤ := Module.length_ne_top_iff.mpr hN
    have hlen : Module.length A M = Module.length A N + 1 := by
      rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), Module.length_eq_one A (M ⧸ N)]
    have hc : Nat.card M = Nat.card (M ⧸ N) * Nat.card N :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
    have hq0 : Nat.card (ResidueField A) ≠ 0 := Nat.card_pos.ne'
    have hM : Nat.card M = Nat.card (ResidueField A) ^ ((Module.length A N).toNat + 1) := by
      rw [hc, hq, hcard, pow_succ, mul_comm]
    refine ⟨Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ hq0), ?_⟩
    rw [hM, hlen, ENat.toNat_add hNt ENat.one_ne_top]
    simp

theorem UpperTheory.V.AlgebraTools.card_eq_pow_length :
    ∀ {A X : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] [AddCommGroup X] [Module A X], (Finite X ↔ Module.length A X ≠ ⊤) ∧ (Finite X → Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat) := by
  intro A X _ _ _ _ _
  have key : Finite X → Module.length A X ≠ ⊤ := fun h => by
    haveI := h
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, isArtinian_of_finite⟩)
  refine ⟨⟨key, fun h => (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp h)).1⟩, fun h => ?_⟩
  exact (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp (key h))).2
