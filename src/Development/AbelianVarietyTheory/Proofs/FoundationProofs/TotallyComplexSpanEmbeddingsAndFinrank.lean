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
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory

open NumberField.InfinitePlace NumberField.mixedEmbedding in

theorem totallyComplex_span_embeddings_and_finrank :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E],
      Submodule.span ℝ (Set.range (Pi.ringHom fun w : InfinitePlace E => w.embedding)) = ⊤ ∧
        Module.finrank ℝ (InfinitePlace E → ℂ) = Module.finrank ℚ E := by
  intro E _ _ _
  constructor
  ·
    let f : mixedSpace E →ₗ[ℝ] (InfinitePlace E → ℂ) :=
      { toFun := fun x w => x.2 ⟨w, IsTotallyComplex.isComplex w⟩
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
    have hf : Function.Surjective f := by
      intro y
      exact ⟨(0, fun w => y w.1), rfl⟩
    have hcomp : ∀ x : E, f (mixedEmbedding E x) = Pi.ringHom (fun w : InfinitePlace E => w.embedding) x := by
      intro x
      funext w
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, mixedEmbedding_apply_isComplex]
      rfl
    have hspan : Submodule.span ℝ (Set.range (mixedEmbedding E)) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← (latticeBasis E).span_eq]
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨_, (latticeBasis_apply E i).symm⟩
    have himg : f '' Set.range (mixedEmbedding E) =
        Set.range (Pi.ringHom fun w : InfinitePlace E => w.embedding) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hcomp)
    rw [← himg, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact hf
  · rw [Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [IsTotallyComplex.finrank, card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    ring

end GlobalTheory
