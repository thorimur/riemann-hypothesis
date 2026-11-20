import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Filter Topology in
theorem UpperTheory.Reformulated.B.GaloisBoundFirst.main :
    ∀ (B : ℂ → ℂ),
      Differentiable ℂ B →
        (∃ (z : ℂ), B z ≠ (0 : ℂ)) →
          ∀ (a : ℂ), ∃ (k : ℕ) (v : ℂ → ℂ), Differentiable ℂ v ∧ v a ≠ (0 : ℂ) ∧ ∀ (z : ℂ), B z = (z - a) ^ k * v z := by
  rintro B hB ⟨z0, hz0⟩ a
  have han : AnalyticOnNhd ℂ B Set.univ := hB.differentiableOn.analyticOnNhd isOpen_univ
  have hnot : ¬ ∀ᶠ z in 𝓝 a, B z = 0 := fun h => hz0
    (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
      (Set.mem_univ z0))
  obtain ⟨k, g, hg, hga, hev⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff (han a (Set.mem_univ a))).2 hnot
  have hev' : ∀ᶠ z in 𝓝 a, z ≠ a → B z / (z - a) ^ k = g z := by
    filter_upwards [hev] with z hz hne
    have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hne)
    rw [hz, smul_eq_mul]
    field_simp
  let v : ℂ → ℂ := fun z => if z = a then g a else B z / (z - a) ^ k
  have hva : v a = g a := by simp [v]
  have hvne : ∀ z, z ≠ a → v z = B z / (z - a) ^ k := fun z hz => by simp [v, hz]
  refine ⟨k, v, ?_, by rwa [hva], ?_⟩
  · intro z
    by_cases hz : z = a
    · subst hz
      have : v =ᶠ[𝓝 z] g := by
        filter_upwards [hev'] with w hw
        by_cases hwz : w = z
        · rw [hwz, hva]
        · rw [hvne w hwz, hw hwz]
      exact (hg.differentiableAt.congr_of_eventuallyEq this)
    · have hd : DifferentiableAt ℂ (fun w => B w / (w - a) ^ k) z :=
        (hB z).div (((differentiableAt_id).sub (differentiableAt_const a)).pow k)
          (pow_ne_zero _ (sub_ne_zero.2 hz))
      have : v =ᶠ[𝓝 z] fun w => B w / (w - a) ^ k := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        exact hvne w hw
      exact hd.congr_of_eventuallyEq this
  · intro z
    by_cases hz : z = a
    · subst hz
      have hB0 : B z = (z - z) ^ k * g z := by
        simpa [smul_eq_mul] using hev.self_of_nhds
      rw [hva]; exact hB0
    · rw [hvne z hz]
      have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz)
      field_simp
