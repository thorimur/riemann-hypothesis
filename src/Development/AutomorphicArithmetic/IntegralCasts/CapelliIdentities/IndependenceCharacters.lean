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

theorem UpperTheory.Reformulated.B.LinearIndependentOfDistinctEigensystems.indep :
    ∀ {V I J : Type} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℂ V] (T : I → Module.End ℂ V) (v : J → V) (lam : J → I → ℂ),
    (∀ (j : J), v j ≠ (0 : V)) →
      (∀ (j : J) (i : I), (T i : V → V) (v j) = lam j i • v j) → Function.Injective lam → LinearIndependent ℂ v := by
  intro V I J _ _ T v lam hv hT hinj
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ j hj; simp at hj
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ b ∈ s, g b = 0 := by
      intro b hb
      have hne : lam b ≠ lam a := fun h => ha (hinj h ▸ hb)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have h1 : g a • lam a i • v a + ∑ j ∈ s, g j • lam j i • v j = 0 := by
        have := congrArg (T i) hg
        simpa only [map_add, map_sum, map_smul, map_zero, hT] using this
      have h2 : g a • lam a i • v a + ∑ j ∈ s, g j • lam a i • v j = 0 := by
        have := congrArg (fun x => lam a i • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_comm (lam a i)] using this
      have h3 : ∑ j ∈ s, (g j * (lam j i - lam a i)) • v j = 0 := by
        have h4 : ∑ j ∈ s, g j • lam j i • v j = ∑ j ∈ s, g j • lam a i • v j :=
          add_left_cancel (h1.trans h2.symm)
        simp only [mul_smul, sub_smul, smul_sub, Finset.sum_sub_distrib, h4, sub_self]
      have h5 := ih (fun j => g j * (lam j i - lam a i)) h3 b hb
      exact (mul_eq_zero.mp h5).resolve_right (sub_ne_zero.mpr hi)
    have h0 : ∑ j ∈ s, g j • v j = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hs j hj, zero_smul]
    rw [h0, add_zero] at hg
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs j hj
