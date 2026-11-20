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
import Mathlib.NumberTheory.LocalField.Basic
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
import Mathlib.Topology.UniformSpace.Uniformizable

open ValuativeRel

private lemma UpperTheory.isOpen_of_add_small {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] (s : Set k)
    (hs : ∀ x ∈ s, ∀ z, valuation k z < 1 → x + z ∈ s) : IsOpen s := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨1, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hs x hx z (by simpa using hz)

private lemma UpperTheory.isOpen_valuation_le_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsOpen {x : k | valuation k x ≤ 1} :=
  UpperTheory.isOpen_of_add_small _ fun _ hx _ hz => (valuation k).map_add_le hx hz.le

private lemma UpperTheory.isOpen_setOf_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsOpen {x : k | valuation k x < 1} :=
  UpperTheory.isOpen_of_add_small _ fun _ hx _ hz => (valuation k).map_add_lt hx hz

private lemma UpperTheory.isClosed_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsClosed {x : k | valuation k x < 1} := by
  rw [← isOpen_compl_iff]
  refine UpperTheory.isOpen_of_add_small _ fun x hx z hz h => hx ?_
  have h' : valuation k (x + z - z) < 1 := (valuation k).map_sub_lt h hz
  simpa using h'

theorem UpperTheory.iwahori_subgroup_open :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
        (S : Set (Matrix.GeneralLinearGroup (Fin n) k)),
        (∀ g : Matrix.GeneralLinearGroup (Fin n) k, g ∈ S ↔
          (∀ i j, ValuativeRel.valuation k (g.val i j) ≤ 1) ∧ (∀ i j, ValuativeRel.valuation k ((g⁻¹).val i j) ≤ 1) ∧
            ∀ i j, j < i → ValuativeRel.valuation k (g.val i j) < 1) →
        IsOpen S ∧ IsCompact S := by
  intro k _ _ _ _ n S hS
  have c1 : ∀ i j, Continuous fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have c2 : ∀ i j, Continuous fun g : Matrix.GeneralLinearGroup (Fin n) k => (g⁻¹).val i j :=
    fun i j => Units.continuous_coe_inv.matrix_elem i j
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  constructor
  · have e : S = (⋂ i, ⋂ j, (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x ≤ 1}) ∩
        ((⋂ i, ⋂ j, (fun g : Matrix.GeneralLinearGroup (Fin n) k => (g⁻¹).val i j) ⁻¹'
          {x : k | valuation k x ≤ 1}) ∩
        ⋂ i, ⋂ j, ⋂ (_ : j < i), (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x < 1}) := by
      ext g
      rw [hS]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      rfl
    rw [e]
    refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (UpperTheory.isOpen_valuation_le_one k).preimage (c1 i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (UpperTheory.isOpen_valuation_le_one k).preimage (c2 i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun _ => (UpperTheory.isOpen_setOf_valuation_lt_one k).preimage (c1 i j)
  · let M : Set (Matrix (Fin n) (Fin n) k) :=
      Set.univ.pi fun _ => Set.univ.pi fun _ => {x : k | valuation k x ≤ 1}
    have hM : IsCompact M := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      IsNonarchimedeanLocalField.isCompact_closedBall k 1
    have hP : IsCompact (M ×ˢ (MulOpposite.op '' M)) :=
      hM.prod (hM.image MulOpposite.continuous_op)
    have hK := (Units.isClosedEmbedding_embedProduct
      (α := Matrix (Fin n) (Fin n) k)).isCompact_preimage hP
    have hC : IsClosed (⋂ i, ⋂ j, ⋂ (_ : j < i),
        (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x < 1}) :=
      isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        (UpperTheory.isClosed_valuation_lt_one k).preimage (c1 i j)
    convert hK.inter_right hC using 1
    ext g
    rw [hS]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_prod]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun i _ j _ => h1 i j, (g⁻¹).val, fun i _ j _ => h2 i j, rfl⟩, h3⟩
    · rintro ⟨⟨h1, m, hm, hme⟩, h3⟩
      have hm' : m = (g⁻¹).val := MulOpposite.op_injective hme
      subst hm'
      exact ⟨fun i j => h1 i trivial j trivial, fun i j => hm i trivial j trivial, h3⟩
