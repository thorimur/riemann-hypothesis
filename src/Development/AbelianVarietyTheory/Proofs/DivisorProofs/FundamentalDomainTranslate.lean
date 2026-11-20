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

open MeasureTheory

theorem GlobalTheory.fundamentalDomain_translate_conj {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (Q : Subgroup G) (𝓓 : Set G) (m : G) : IsFundamentalDomain Q 𝓓 μ → IsFundamentalDomain (Q.map (MulAut.conj m⁻¹).toMonoidHom) ((fun g => m⁻¹ * g) '' 𝓓) μ ∧ ∀ φ : G → ENNReal, ∫⁻ g in 𝓓, φ (m⁻¹ * g) ∂μ = ∫⁻ g in (fun g => m⁻¹ * g) '' 𝓓, φ g ∂μ := by
  intro h
  have hmp : MeasurePreserving (fun g => m⁻¹ * g) μ μ := measurePreserving_mul_left μ m⁻¹
  refine ⟨?_, fun φ => hmp.setLIntegral_comp_emb (measurableEmbedding_mulLeft m⁻¹) φ 𝓓⟩
  let e : Q.map (MulAut.conj m⁻¹).toMonoidHom ≃ Q :=
    (Subgroup.equivMapOfInjective Q (MulAut.conj m⁻¹).toMonoidHom (MulAut.conj m⁻¹).injective).symm.toEquiv
  have hq : Measure.QuasiMeasurePreserving (Equiv.mulLeft m⁻¹).symm μ μ := by
    have : MeasurePreserving (fun g => m * g) μ μ := measurePreserving_mul_left μ m
    simpa [Equiv.mulLeft_symm] using this.quasiMeasurePreserving
  have := h.image_of_equiv (Equiv.mulLeft m⁻¹) hq e ?_
  · simpa using this
  · intro γ x
    obtain ⟨γ, hγ⟩ := γ
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hγ
    have he : e ⟨_, hγ⟩ = ⟨q, hq⟩ :=
      (Subgroup.equivMapOfInjective Q (MulAut.conj m⁻¹).toMonoidHom (MulAut.conj m⁻¹).injective).symm_apply_eq.mpr rfl
    show m⁻¹ * ((e ⟨_, hγ⟩ : G) * x) = (MulAut.conj m⁻¹ q) * (m⁻¹ * x)
    rw [he]
    simp [mul_assoc]
