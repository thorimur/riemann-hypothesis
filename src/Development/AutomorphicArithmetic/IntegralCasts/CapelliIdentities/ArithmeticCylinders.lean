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
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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

theorem UpperTheory.Reformulated.B.ArithmeticCylinders.eigen_pow_eq_one :
    ∀ {L : Type} [inst : Field L] {d : Type} [inst_1 : Fintype d] [inst_2 : DecidableEq d]
    (M : Matrix d d L) (n : ℕ), M ^ n = (1 : Matrix d d L) → ∀ (μ : L), M.charpoly.IsRoot μ → μ ^ n = (1 : L) := by
  intro L _ d _ _ M n hM μ hμ
  have h1 : μ ∈ spectrum L M := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hμ
  have h2 : μ ^ n ∈ spectrum L (M ^ n) := spectrum.pow_mem_pow M n h1
  rw [hM, spectrum.mem_iff] at h2
  by_contra hne
  apply h2
  have hu : IsUnit (μ ^ n - 1) := (sub_ne_zero.mpr hne).isUnit
  have h3 := hu.map (algebraMap L (Matrix d d L))
  rwa [map_sub, map_one] at h3
