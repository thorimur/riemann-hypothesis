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
open scoped TensorProduct

theorem GlobalTheory.derivation_normalise_family : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∀ (d : ℕ) (x : Fin d → A) (D : Fin d → Derivation k A A), (∀ i j, ε (D i (x j)) = if i = j then 1 else 0) → ∃ E : Fin d → Derivation k A A, ∀ i j, E i (x j) = if i = j then 1 else 0 := by
  intro k A _ _ _ ε hnil d x D hD
  let M : Matrix (Fin d) (Fin d) A := Matrix.of fun i j => D i (x j)
  have hε : (ε : A →+* k).mapMatrix M = 1 := by
    ext i j
    simp [M, hD, Matrix.one_apply]
  have hdet : ε M.det = 1 := by
    have h := RingHom.map_det (ε : A →+* k) M
    rw [hε, Matrix.det_one] at h
    simpa using h
  have hunit : IsUnit M.det := by
    obtain ⟨n, hn⟩ := hnil
    have hmem : M.det - 1 ∈ RingHom.ker ε := by simp [RingHom.mem_ker, hdet]
    have hN : IsNilpotent (M.det - 1) := ⟨n, by
      have h : (M.det - 1) ^ n ∈ (RingHom.ker ε) ^ n := Ideal.pow_mem_pow hmem n
      rw [hn] at h
      simpa using h⟩
    have h := hN.isUnit_one_add
    simpa using h
  refine ⟨fun i => ∑ l, (M⁻¹ i l) • D l, fun i j => ?_⟩
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have h := congrFun (congrFun hinv i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]
  have hev := map_sum (AddMonoidHom.mk' (fun δ : Derivation k A A => δ (x j)) (fun a b => rfl))
    (fun l => M⁻¹ i l • D l) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hev
  rw [hev]
  simp [M]
