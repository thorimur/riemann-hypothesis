import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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

open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh1.map_involution_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (φ : G ≃ₜ* G) (hφ : ∀ x, φ (φ x) = x) :
    μ.map φ = μ := by
  have h1 : φ.trans φ = ContinuousMulEquiv.refl G := by
    ext x
    exact hφ x
  have h2 : mulEquivHaarChar φ * mulEquivHaarChar φ = 1 := by
    rw [← mulEquivHaarChar_trans, h1, mulEquivHaarChar_refl]
  have h3 : mulEquivHaarChar φ = 1 := by
    have h : (mulEquivHaarChar φ) ^ 2 = 1 := by rw [sq, h2]
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h
  have h4 := mulEquivHaarChar_smul_map μ φ
  rwa [h3, one_smul] at h4

theorem UpperTheory.Reformulated.B.Qh1.twist_general.{u_1} :
    ∀ {G : Type u_1} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [inst_5 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G)
    [Countable ↥Γ] {F : Set G},
    MeasureTheory.IsFundamentalDomain (↥Γ) F μ →
      ∀ (θ : G →* G),
        Continuous (⇑θ : G → G) →
          (∀ (x : G), (θ : G → G) ((θ : G → G) x) = x) →
            (∀ γ ∈ Γ, (θ : G → G) γ ∈ Γ) →
              ∀ (f : G → ℂ),
                (∀ (γ : ↥Γ) (x : G), f ((↑γ : G) * x) = f x) →
                  MeasureTheory.Integrable f (μ.restrict F) →
                    MeasureTheory.Integrable (fun (x : G) ↦ f ((θ : G → G) x)) (μ.restrict F) ∧
                      ∫ (x : G) in F, f ((θ : G → G) x) ∂μ = ∫ (x : G) in F, f x ∂μ := by
  intro G _ _ _ _ _ _ _ μ _ Γ _ F hF θ hθc hθθ hθΓ f hf hfi
  let φ : G ≃ₜ* G :=
    { toFun := θ
      invFun := θ
      left_inv := hθθ
      right_inv := hθθ
      map_mul' := map_mul θ
      continuous_toFun := hθc
      continuous_invFun := hθc }
  have hmp : MeasureTheory.MeasurePreserving θ μ μ :=
    ⟨hθc.measurable, UpperTheory.Reformulated.B.Qh1.map_involution_eq μ φ hθθ⟩
  have hemb : MeasurableEmbedding (θ : G → G) := φ.toHomeomorph.measurableEmbedding
  let e : Γ → Γ := fun γ => ⟨θ γ, hθΓ γ γ.2⟩
  have he : Function.Involutive e := fun γ => Subtype.ext (hθθ γ)
  have hF' : MeasureTheory.IsFundamentalDomain Γ (θ ⁻¹' F) μ := by
    refine hF.preimage_of_equiv hmp.quasiMeasurePreserving he.bijective ?_
    intro γ x
    change θ (θ γ * x) = γ * θ x
    rw [map_mul, hθθ]
  have hg : ∀ (γ : Γ) (x : G), f (θ (γ • x)) = f (θ x) := by
    intro γ x
    change f (θ (γ * x)) = f (θ x)
    rw [map_mul]
    exact hf (e γ) (θ x)
  refine ⟨?_, ?_⟩
  · have h1 : MeasureTheory.IntegrableOn (fun x => f (θ x)) (θ ⁻¹' F) μ :=
      (hmp.integrableOn_comp_preimage hemb).2 hfi
    exact (hF.integrableOn_iff hF' (f := fun x => f (θ x)) hg).2 h1
  · rw [hF.setIntegral_eq hF' (f := fun x => f (θ x)) hg]
    exact hmp.setIntegral_preimage_emb hemb f F
