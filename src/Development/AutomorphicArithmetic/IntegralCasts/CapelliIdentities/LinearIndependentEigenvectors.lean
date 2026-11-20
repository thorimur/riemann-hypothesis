import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
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

theorem UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {Ξ P : Type}
    (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ),
    Function.Injective ev →
      ∀ (v : Ξ → V),
        (∀ (ξ : Ξ), v ξ ≠ (0 : V)) → (∀ (ξ : Ξ) (p : P), (T p : V → V) (v ξ) = ev ξ p • v ξ) → LinearIndependent ℂ v := by
  intro V _ _ Ξ P T ev hinj v hv hT
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ i hi; simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : ev i ≠ ev a := fun h => ha (hinj h ▸ hi)
      obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
      have h1 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev j p) • v j = 0 := by
        have h := congrArg (T p) hg
        simpa only [map_add, map_sum, map_smul, map_zero, hT, smul_smul] using h
      have h2 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev a p) • v j = 0 := by
        have h := congrArg (fun x => ev a p • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm] using h
      have h3 : ∑ j ∈ s, (g j * (ev j p - ev a p)) • v j = 0 := by
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        exact add_left_cancel (h1.trans h2.symm)
      have h4 := ih (fun j => g j * (ev j p - ev a p)) h3 i hi
      exact (mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hp)
    have h0 : ∑ j ∈ s, g j • v j = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hs j hj, zero_smul]
    rw [h0, add_zero] at hg
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi
