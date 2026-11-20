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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Monotonicity.Lemmas
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
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_det_ne_zero_of_rows_separating :
    ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K),
      (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) →
      ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  intro K _ σ h M hM
  have hsp : Submodule.span K (Set.range M) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have ha : (fun j => f (fun k => if j = k then 1 else 0)) = 0 := by
      apply hM
      intro s
      have h1 : f (M s) = 0 := hf (Submodule.subset_span ⟨s, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      refine (Finset.sum_congr rfl fun j _ => ?_).trans h1
      rw [smul_eq_mul, mul_comm]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun ha j
    simp only [Pi.zero_apply] at this
    rw [this, smul_zero]
  obtain ⟨b, hbS, hbsp, hli⟩ := exists_linearIndependent K (Set.range M)
  have hsp' : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin h → K)) := by
    rw [Subtype.range_coe, hbsp, hsp]
  let B := Module.Basis.mk hli hsp'
  let e : Fin h ≃ b := (Pi.basisFun K (Fin h)).indexEquiv B
  have hmem : ∀ i, ∃ s, M s = (e i : Fin h → K) := fun i => hbS (e i).2
  choose s hs using hmem
  refine ⟨s, ?_⟩
  have hrows : LinearIndependent K (Matrix.of fun i j => M (s i) j).row := by
    have : (Matrix.of fun i j => M (s i) j).row = (fun x : b => (x : Fin h → K)) ∘ e := by
      funext i j
      simp [Matrix.row, hs]
    rw [this]
    exact hli.comp e e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end GlobalTheory
