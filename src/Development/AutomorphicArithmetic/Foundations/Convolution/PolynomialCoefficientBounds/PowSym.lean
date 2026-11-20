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

theorem UpperTheory.ConvolutionTheory.FX.esymm_pow :
    ∀ (n f : ℕ) (i : Fin n), ∃ g : MvPolynomial (Fin n) ℂ, aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) g = aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f) (esymm (Fin n) ℂ (i + 1)) := by
  intro n f i
  have hs : (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f)
      (esymm (Fin n) ℂ (i + 1))).IsSymmetric := by
    intro e
    have h : (rename e).comp (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f))
        = (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f)).comp
            (rename e : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ) := by
      apply MvPolynomial.algHom_ext
      intro r
      simp
    have h2 := DFunLike.congr_fun h (esymm (Fin n) ℂ (i + 1))
    simp only [AlgHom.comp_apply] at h2
    rw [h2, esymm_isSymmetric (Fin n) ℂ (i + 1) e]
  obtain ⟨g, hg⟩ := esymmAlgHom_surjective (σ := Fin n) ℂ (n := n) (by simp)
    ⟨_, (mem_symmetricSubalgebra _).2 hs⟩
  refine ⟨g, ?_⟩
  have := congrArg Subtype.val hg
  rw [esymmAlgHom_apply] at this
  exact this
