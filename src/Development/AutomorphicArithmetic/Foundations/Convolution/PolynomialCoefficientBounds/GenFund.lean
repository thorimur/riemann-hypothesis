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
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
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

open MvPolynomial Filter Topology

private theorem UpperTheory.ConvolutionTheory.FX.gen_fund_block (n : ℕ) (b : Fin n → ℕ) :
    ∃ q : MvPolynomial (Fin n) ℂ, aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) q
      = ∑ σ : Equiv.Perm (Fin n), ∏ i, (X (σ i) : MvPolynomial (Fin n) ℂ) ^ b i := by
  have hs : (∑ σ : Equiv.Perm (Fin n), ∏ i, (X (σ i) : MvPolynomial (Fin n) ℂ) ^ b i).IsSymmetric := by
    intro e
    simp only [map_sum, map_prod, map_pow, rename_X]
    exact Fintype.sum_equiv (Equiv.mulLeft e) _ _ (fun σ => by simp)
  obtain ⟨q, hq⟩ := esymmAlgHom_surjective (σ := Fin n) (R := ℂ) (n := n) (by simp) ⟨_, hs⟩
  refine ⟨q, ?_⟩
  rw [← esymmAlgHom_apply, hq]

theorem UpperTheory.ConvolutionTheory.FX.gen_fund :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ) (β : τ × Fin n → ℕ), ∃ G : MvPolynomial (τ × Fin n) ℂ, aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))) G = ∑ w : τ → Equiv.Perm (Fin n), rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) (∏ u, X u ^ β u) := by
  intro τ _ _ n β
  choose q hq using fun t : τ => UpperTheory.ConvolutionTheory.FX.gen_fund_block n (fun i => β (t, i))
  refine ⟨∏ t, rename (fun j => (t, j)) (q t), ?_⟩
  have h1 : ∀ t : τ, aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1)))
      (rename (fun j => (t, j)) (q t))
      = ∑ σ : Equiv.Perm (Fin n), ∏ i, (X (t, σ i) : MvPolynomial (τ × Fin n) ℂ) ^ β (t, i) := by
    intro t
    have h2 := congrArg (rename (fun j : Fin n => (t, j))) (hq t)
    rw [← AlgHom.comp_apply, comp_aeval] at h2
    rw [aeval_rename]
    simp only [map_sum, map_prod, map_pow, rename_X] at h2
    exact h2
  rw [map_prod]
  simp only [h1]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [map_prod, map_pow, rename_X]
  rw [Fintype.prod_prod_type]
