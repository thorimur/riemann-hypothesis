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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
open NumberField

namespace GlobalTheory.SumIndex

theorem relIndex_pi_pi_of {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

theorem eq_zero_of_sum_eq_zero {ι R V : Type} [Fintype ι] [DecidableEq ι] [Ring R] [AddCommGroup V]
    [Module R V] (S : ι → Submodule R V) (hS : iSupIndep S) (y : ι → V) (hy : ∀ a, y a ∈ S a)
    (h0 : ∑ a, y a = 0) (b : ι) : y b = 0 := by
  have hb : y b = -∑ a ∈ Finset.univ.erase b, y a := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hmem : y b ∈ ⨆ (a) (_ : a ≠ b), S a := by
    rw [hb]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun a ha => ?_)
    exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase ha) (hy a))
  exact (Submodule.disjoint_def.1 (hS b)) _ (hy b) hmem

theorem relIndex_iSup_map_eq_pow : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : ℕ)
  (M : Fin p → (W →ₗ[K] V)) (ℓ N : Submodule (𝓞 K) W), N ≤ ℓ → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
    (N.toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
  intro K _ _ W V _ _ _ _ _ _ _ _ p M ℓ N hNℓ hinj hind
  classical
  let Φ : (Fin p → W) →ₗ[𝓞 K] V := ∑ a, ((M a).restrictScalars (𝓞 K)).comp (LinearMap.proj a)
  have hΦ : ∀ x, Φ x = ∑ a, M a (x a) := by intro x; simp [Φ]
  have himg : ∀ S : Submodule (𝓞 K) W, (Submodule.pi Set.univ (fun _ : Fin p => S)).map Φ =
      ⨆ a, S.map ((M a).restrictScalars (𝓞 K)) := by
    intro S
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hΦ]
      exact Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ⟨x a, hx a (Set.mem_univ a), rfl⟩
    · refine iSup_le fun a => ?_
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨Pi.single a w, ?_, ?_⟩
      · intro b _
        by_cases h : b = a
        · subst h; simpa using hw
        · simp [Pi.single_apply, h]
      · rw [hΦ, Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
        simp
  let Lp : Submodule (𝓞 K) (Fin p → W) := Submodule.pi Set.univ (fun _ => ℓ)
  let Np : Submodule (𝓞 K) (Fin p → W) := Submodule.pi Set.univ (fun _ => N)
  have hNL : Np ≤ Lp := fun x hx a ha => hNℓ (hx a ha)
  let g : Lp.toAddSubgroup →+ V := Φ.toAddMonoidHom.comp Lp.toAddSubgroup.subtype
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun z hz => ?_
    have h0 : ∑ a, M a (z.1 a) = 0 := by rw [← hΦ]; exact hz
    have hy := eq_zero_of_sum_eq_zero _ hind (fun a => M a (z.1 a))
      (fun a => Submodule.subset_span ⟨z.1 a, z.2 a (Set.mem_univ a), rfl⟩) h0
    exact Subtype.ext (funext fun a => by simpa using hinj a (by simpa using hy a))
  have hL' : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup = (⊤ : AddSubgroup Lp.toAddSubgroup).map g := by
    rw [← himg]
    ext v
    simp [g, Lp]
  have hN' : (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
      (Np.toAddSubgroup.addSubgroupOf Lp.toAddSubgroup).map g := by
    rw [← himg]
    ext v
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map,
      AddSubgroup.mem_addSubgroupOf, Subtype.exists]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hNL hx, hx, rfl⟩
    · rintro ⟨x, _, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hL', hN', AddSubgroup.relIndex_map_map_of_injective _ _ hg, AddSubgroup.relIndex_top_right]
  change Np.toAddSubgroup.relIndex Lp.toAddSubgroup = _
  have e1 : Np.toAddSubgroup = AddSubgroup.pi Set.univ (fun _ : Fin p => N.toAddSubgroup) := by
    ext x; simp [Np, AddSubgroup.mem_pi, Submodule.mem_pi]
  have e2 : Lp.toAddSubgroup = AddSubgroup.pi Set.univ (fun _ : Fin p => ℓ.toAddSubgroup) := by
    ext x; simp [Lp, AddSubgroup.mem_pi, Submodule.mem_pi]
  rw [e1, e2, relIndex_pi_pi_of, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.SumIndex
