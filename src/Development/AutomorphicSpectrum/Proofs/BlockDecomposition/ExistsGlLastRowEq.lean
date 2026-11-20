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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
open Matrix

namespace GlobalTheory.CompanionTheory.LinAlg

theorem exists_GL_lastRow_eq : ∀ (K : Type) [Field K] (n : ℕ) (a : Fin (n + 1) → K), a ≠ 0 →
    ∃ m : GL (Fin (n + 1)) K, vecMul (Pi.single (Fin.last n) 1) (m : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = a := by
  intro K _ n a ha
  classical
  set e : Fin (n + 1) → K := Pi.single (Fin.last n) 1 with he_def
  have he : e ≠ 0 := by simp [e]
  let f : (K ∙ e) ≃ₗ[K] (K ∙ a) :=
    (LinearEquiv.toSpanNonzeroSingleton K _ e he).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton K _ a ha
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h1 : (LinearEquiv.toSpanNonzeroSingleton K _ e he).symm
      ⟨e, Submodule.mem_span_singleton_self e⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  have hga : g e = a := by
    have hx := hg ⟨e, Submodule.mem_span_singleton_self e⟩
    rw [← hx]
    simp only [f, LinearEquiv.trans_apply, h1, LinearEquiv.toSpanNonzeroSingleton_one]
  have hdet : IsUnit (LinearMap.toMatrix' (g : (Fin (n + 1) → K) →ₗ[K] Fin (n + 1) → K))ᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' g
  refine ⟨hdet.unit, ?_⟩
  rw [IsUnit.unit_spec, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  simpa using hga

end GlobalTheory.CompanionTheory.LinAlg
