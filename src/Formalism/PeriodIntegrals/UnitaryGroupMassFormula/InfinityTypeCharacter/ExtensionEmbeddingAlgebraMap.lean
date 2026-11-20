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
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
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

noncomputable section

open NumberField

namespace PI.InfTypeCharW

def normalize : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (by exact_mod_cast (norm_ne_zero_iff.mpr z.ne_zero)))
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm]

variable {L : Type} [Field L] [NumberField L]

theorem extensionEmbedding_algebraMap (w : InfinitePlace L) (k : L) :
    InfinitePlace.Completion.extensionEmbedding w (algebraMap L w.Completion k) = w.embedding k := by
  rw [InfinitePlace.Completion.algebraMap_apply]
  exact InfinitePlace.Completion.extensionEmbedding_coe w _

theorem exists_ext (φ : L →+* ℂ) : ∃ ι : (InfinitePlace.mk φ).Completion →+* ℂ,
    Continuous ι ∧ ∀ k : L, ι (algebraMap L _ k) = φ k := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · refine ⟨InfinitePlace.Completion.extensionEmbedding _,
      (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous, fun k => ?_⟩
    rw [extensionEmbedding_algebraMap, h]
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous,
      fun k => ?_⟩
    rw [RingHom.comp_apply, extensionEmbedding_algebraMap, h, ComplexEmbedding.conjugate_coe_eq]
    simp

end PI.InfTypeCharW
