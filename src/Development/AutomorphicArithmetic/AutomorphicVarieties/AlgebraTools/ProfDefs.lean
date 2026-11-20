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

noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

variable (l : ℕ) (G : Type) [Group G] [TopologicalSpace G]

def IsProL : Prop := ∀ N : OpenNormalSubgroup G, IsPGroup l (G ⧸ N.toSubgroup)

theorem isProL_iff : IsProL l G ↔ ∀ (N : OpenNormalSubgroup G) (g : G), ∃ k : ℕ, g ^ l ^ k ∈ N.toSubgroup := by
  unfold IsProL
  refine forall_congr' fun N => ?_
  constructor
  · intro h g
    obtain ⟨k, hk⟩ := h (g : G ⧸ N.toSubgroup)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · intro h x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

def proLRes : Subgroup G :=
  ⨅ N : {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ N.toSubgroup)}, N.1.toSubgroup

variable {l G} in
theorem mem_proLRes {g : G} :
    g ∈ proLRes l G ↔ ∀ N : OpenNormalSubgroup G, IsPGroup l (G ⧸ N.toSubgroup) → g ∈ N.toSubgroup := by
  simp only [proLRes, Subgroup.mem_iInf, Subtype.forall]

instance : (proLRes l G).Normal :=
  ⟨fun _ h g => mem_proLRes.2 fun N hN => N.isNormal'.conj_mem _ (mem_proLRes.1 h N hN) g⟩

theorem isClosed_proLRes [ContinuousMul G] : IsClosed (proLRes l G : Set G) := by
  rw [proLRes, Subgroup.coe_iInf]
  exact isClosed_iInter fun N => N.1.toOpenSubgroup.isClosed

variable {G} in

def proLResOf (H : Subgroup G) : Subgroup G := (proLRes l H).map H.subtype

variable {G} in

def TopGen (s : Set G) : Prop := Dense (Subgroup.closure s : Set G)

def TopFG : Prop := ∃ s : Set G, s.Finite ∧ TopGen s

variable {G} in
theorem topGen_iff [IsTopologicalGroup G] (s : Set G) :
    TopGen s ↔ (Subgroup.closure s).topologicalClosure = ⊤ := by
  rw [TopGen, dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, ← Subgroup.coe_top,
    SetLike.coe_set_eq]

variable {G} in

def limKer {ι : Type} (F : Filter ι) (K : ι → Subgroup G) : Subgroup G where
  carrier := {g | ∀ O : OpenNormalSubgroup G, ∀ᶠ i in F, g ∈ K i ⊔ O.toSubgroup}
  mul_mem' ha hb O := ((ha O).and (hb O)).mono fun _ h => mul_mem h.1 h.2
  one_mem' _ := Eventually.of_forall fun _ => one_mem _
  inv_mem' h O := (h O).mono fun _ h => inv_mem h

variable {G} in
theorem mem_limKer {ι : Type} {F : Filter ι} {K : ι → Subgroup G} {g : G} :
    g ∈ limKer F K ↔ ∀ O : OpenNormalSubgroup G, ∀ᶠ i in F, g ∈ K i ⊔ O.toSubgroup := Iff.rfl

variable {G} in
instance limKer_normal {ι : Type} (F : Filter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal] :
    (limKer F K).Normal :=
  ⟨fun _ h g O => (h O).mono fun i hi => by
    haveI := O.isNormal'
    exact (Subgroup.sup_normal (K i) O.toSubgroup).conj_mem _ hi g⟩

end UpperTheory.V.AlgebraTools
