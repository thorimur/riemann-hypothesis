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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
open MvPolynomial

theorem PositivityTheory.Xgn.finite_nonvanishing_selection : ∀ (σ : Type) [Finite σ] (F : Set (MvPolynomial σ ℤ)), ∃ T : Finset (MvPolynomial σ ℤ), (T : Set (MvPolynomial σ ℤ)) ⊆ F ∧ ∀ z : σ → ℂ, (∃ s ∈ F, eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0) → ∃ s ∈ T, eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0 := by
  intro σ _ F
  have hfg : (Submodule.span (MvPolynomial σ ℤ) F).FG := IsNoetherian.noetherian _
  obtain ⟨T, hTF, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset F).1 hfg
  refine ⟨T, hTF, fun z hz => ?_⟩
  obtain ⟨s, hsF, hs⟩ := hz
  by_contra hall
  push_neg at hall
  let φ : MvPolynomial σ ℤ →+* ℂ := (eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hle : Ideal.span (T : Set (MvPolynomial σ ℤ)) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    intro t ht
    exact RingHom.mem_ker.2 (hall t ht)
  have hsT : s ∈ Submodule.span (MvPolynomial σ ℤ) (T : Set (MvPolynomial σ ℤ)) := by
    rw [← hT]
    exact Submodule.subset_span hsF
  exact hs (RingHom.mem_ker.1 (hle hsT))
