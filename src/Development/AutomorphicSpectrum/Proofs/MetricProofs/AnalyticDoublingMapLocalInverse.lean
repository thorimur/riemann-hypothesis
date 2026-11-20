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
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Metric.FamilyInverse

theorem exists_analytic_family_inverse {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (b₀ : B) (d : B × V → V) (han : AnalyticAt ℂ d (b₀, 0)) (h0 : d (b₀, 0) = 0)
    (hd : HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V) (b₀, 0)) :
    ∃ h : B × V → V, AnalyticAt ℂ h (b₀, 0) ∧ h (b₀, 0) = 0 ∧
      (∀ᶠ p : B × V in 𝓝 (b₀, 0), d (p.1, h p) = p.2) ∧
      (∀ᶠ p : B × V in 𝓝 (b₀, 0), h (p.1, d p) = p.2) := by
  let Φ : B × V → B × V := fun p => (p.1, d p)
  let L : (B × V) →L[ℂ] (B × V) :=
    (ContinuousLinearMap.fst ℂ B V).prod ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V)
  let L' : (B × V) →L[ℂ] (B × V) :=
    (ContinuousLinearMap.fst ℂ B V).prod ((2⁻¹ : ℂ) • ContinuousLinearMap.snd ℂ B V)
  let Le : (B × V) ≃L[ℂ] (B × V) :=
    ContinuousLinearEquiv.equivOfInverse L L'
      (fun p => by simp [L, L', smul_smul]) (fun p => by simp [L, L', smul_smul])
  have hLe : (Le : (B × V) →L[ℂ] (B × V)) = L := rfl
  have hΦan : AnalyticAt ℂ Φ (b₀, 0) := analyticAt_fst.prod han
  have hΦd : HasFDerivAt Φ L (b₀, 0) := hasFDerivAt_fst.prodMk hd
  have hs : HasStrictFDerivAt Φ (Le : (B × V) →L[ℂ] (B × V)) (b₀, 0) := by
    have := hΦan.hasStrictFDerivAt
    rwa [hΦd.fderiv, ← hLe] at this
  have hfix : Φ (b₀, 0) = (b₀, 0) := by simp [Φ, h0]
  let P := hs.toOpenPartialHomeomorph Φ
  have hPc : (P : B × V → B × V) = Φ := hs.toOpenPartialHomeomorph_coe
  have hPan : AnalyticAt ℂ P.symm (P (b₀, 0)) :=
    P.analyticAt_symm' (i := Le) hs.mem_toOpenPartialHomeomorph_source
      (by rw [hPc]; exact hΦan) (by rw [hPc, hΦd.fderiv, hLe])
  have hΨan : AnalyticAt ℂ P.symm (b₀, 0) := by
    have : P (b₀, 0) = (b₀, 0) := by rw [hPc]; exact hfix
    rwa [this] at hPan
  have hright : ∀ᶠ q in 𝓝 (b₀, 0), Φ (P.symm q) = q := by
    have := hs.eventually_right_inverse
    rw [hfix] at this
    exact this
  have hleft : ∀ᶠ p in 𝓝 (b₀, 0), P.symm (Φ p) = p := hs.eventually_left_inverse
  have hΨ0 : P.symm (b₀, 0) = (b₀, 0) := by
    have := hs.localInverse_apply_image
    rw [hfix] at this
    exact this
  refine ⟨fun q => (P.symm q).2, analyticAt_snd.comp hΨan, by simp [hΨ0], ?_, ?_⟩
  · filter_upwards [hright] with q hq
    have e1 := congrArg Prod.fst hq
    have e2 := congrArg Prod.snd hq
    have h1 : (P.symm q).1 = q.1 := e1
    have h2 : d (P.symm q) = q.2 := e2
    have h3 : (q.1, (P.symm q).2) = P.symm q := by rw [← h1]
    rw [h3, h2]
  · filter_upwards [hleft] with p hp
    have e := congrArg Prod.snd hp
    exact e

end GlobalTheory.CompanionTheory.Metric.FamilyInverse
