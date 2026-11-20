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
import Mathlib.GroupTheory.Commensurable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
open Matrix

namespace GlobalTheory

theorem relIndex_iInf_fin_ne_zero {G : Type} [Group G] {m : ℕ} (K : Fin m → Subgroup G)
    (L : Subgroup G) (h : ∀ i, (K i).relIndex L ≠ 0) : (⨅ i, K i).relIndex L ≠ 0 := by
  have key : ∀ s : Finset (Fin m), (⨅ i ∈ s, K i).relIndex L ≠ 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iInf_insert]
      exact Subgroup.relIndex_inf_ne_zero (h a) ih
  simpa using key Finset.univ

theorem prod_pi_eq_inf_iInf {A : Type} [Group A] {m : ℕ} {B : Fin m → Type} [∀ i, Group (B i)]
    (H : Subgroup A) (K : ∀ i, Subgroup (B i)) :
    H.prod (Subgroup.pi Set.univ K) =
      H.comap (MonoidHom.fst A ((i : Fin m) → B i)) ⊓
        ⨅ i, (K i).comap ((Pi.evalMonoidHom B i).comp (MonoidHom.snd A ((i : Fin m) → B i))) := by
  ext x
  simp [Subgroup.mem_prod, Subgroup.mem_pi, Subgroup.mem_iInf]

theorem relIndex_prod_pi_ne_zero {A : Type} [Group A] {m : ℕ} {B : Fin m → Type}
    [∀ i, Group (B i)] (H H' : Subgroup A) (K K' : ∀ i, Subgroup (B i))
    (hH : H.relIndex H' ≠ 0) (hK : ∀ i, (K i).relIndex (K' i) ≠ 0) :
    (H.prod (Subgroup.pi Set.univ K)).relIndex (H'.prod (Subgroup.pi Set.univ K')) ≠ 0 := by
  rw [prod_pi_eq_inf_iInf H K]
  apply Subgroup.relIndex_inf_ne_zero
  · rw [Subgroup.relIndex_comap]
    refine mt (Subgroup.relIndex_eq_zero_of_le_right ?_) hH
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_prod.mp hx).1
  · apply relIndex_iInf_fin_ne_zero
    intro i
    rw [Subgroup.relIndex_comap]
    refine mt (Subgroup.relIndex_eq_zero_of_le_right ?_) (hK i)
    rintro _ ⟨x, hx, rfl⟩
    exact ((Subgroup.mem_pi Set.univ).mp (Subgroup.mem_prod.mp hx).2) i (Set.mem_univ i)

theorem map_conj_prod_pi {A : Type} [Group A] {m : ℕ} {B : Fin m → Type} [∀ i, Group (B i)]
    (H : Subgroup A) (K : ∀ i, Subgroup (B i)) (g : A × ((i : Fin m) → B i)) :
    (H.prod (Subgroup.pi Set.univ K)).map (MulAut.conj g).toMonoidHom =
      (H.map (MulAut.conj g.1).toMonoidHom).prod
        (Subgroup.pi Set.univ fun i => (K i).map (MulAut.conj (g.2 i)).toMonoidHom) := by
  ext x
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_prod, Subgroup.mem_pi, Set.mem_univ,
    true_implies, MulAut.conj_symm_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv,
    Prod.snd_inv, Pi.mul_apply, Pi.inv_apply]

theorem commensurable_map_conj_prod_pi : ∀ {A : Type} [Group A] {m : ℕ} {B : Fin m → Type} [∀ i, Group (B i)] (H : Subgroup A) (K : ∀ i, Subgroup (B i)) (g : A × ((i : Fin m) → B i)), Subgroup.Commensurable (H.map (MulAut.conj g.1).toMonoidHom) H → (∀ i, Subgroup.Commensurable ((K i).map (MulAut.conj (g.2 i)).toMonoidHom) (K i)) → Subgroup.Commensurable ((H.prod (Subgroup.pi Set.univ K)).map (MulAut.conj g).toMonoidHom) (H.prod (Subgroup.pi Set.univ K)) := by
  intro A _ m B _ H K g hH hK
  rw [map_conj_prod_pi]
  exact ⟨relIndex_prod_pi_ne_zero _ _ _ _ hH.1 fun i => (hK i).1,
    relIndex_prod_pi_ne_zero _ _ _ _ hH.2 fun i => (hK i).2⟩

end GlobalTheory
