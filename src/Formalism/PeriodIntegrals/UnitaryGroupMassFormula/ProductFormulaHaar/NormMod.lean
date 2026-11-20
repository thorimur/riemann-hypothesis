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
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

open MeasureTheory ValuativeRel

namespace PI.ProdFormulaE

open scoped Classical in

def modF (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    (a : K) : ℝ :=
  if h : a = 0 then 0 else ((distribHaarChar K (Units.mk0 a h) : NNReal) : ℝ)

section

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

theorem modF_zero : modF K 0 = 0 := by
  unfold modF
  rw [dif_pos rfl]

theorem modF_of_ne {a : K} (h : a ≠ 0) :
    modF K a = ((distribHaarChar K (Units.mk0 a h) : NNReal) : ℝ) := by
  unfold modF
  rw [dif_neg h]

theorem modF_pos {a : K} (h : a ≠ 0) : 0 < modF K a := by
  rw [modF_of_ne h]
  have hu : IsUnit (distribHaarChar K (Units.mk0 a h)) := (Group.isUnit (Units.mk0 a h)).map (distribHaarChar K)
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu.ne_zero)

theorem modF_mul (a b : K) : modF K (a * b) = modF K a * modF K b := by
  by_cases ha : a = 0
  · subst ha; simp [modF_zero]
  by_cases hb : b = 0
  · subst hb; simp [modF_zero]
  rw [modF_of_ne (mul_ne_zero ha hb), modF_of_ne ha, modF_of_ne hb]
  have hu : Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb := by
    ext; simp
  rw [hu, map_mul, NNReal.coe_mul]

theorem modF_one : modF K 1 = 1 := by
  rw [modF_of_ne one_ne_zero]
  have hu : Units.mk0 (1 : K) one_ne_zero = 1 := by
    ext; simp
  rw [hu, map_one, NNReal.coe_one]

theorem modF_div (a b : K) : modF K (a / b) = modF K a / modF K b := by
  by_cases hb : b = 0
  · subst hb; simp [modF_zero]
  have hm : modF K (a / b) * modF K b = modF K a := by
    rw [← modF_mul, div_mul_cancel₀ a hb]
  rw [eq_div_iff (modF_pos hb).ne']
  exact hm

end

def IndexFormula : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (t : 𝒪[K]), t ≠ 0 →
      modF K (t : K) * (Nat.card (𝒪[K] ⧸ Ideal.span {t}) : ℝ) = 1

open IsDedekindDomain NumberField in

def CardStep : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K), DenseRange ι → (∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) →
    ∀ (a : 𝓞 F), a ≠ 0 → ∀ t : 𝒪[K], (t : K) = ι (a : F) →
      Nat.card (𝒪[K] ⧸ Ideal.span {t}) = Ideal.absNorm (p.maxPowDividing (Ideal.span {a}))

end PI.ProdFormulaE
