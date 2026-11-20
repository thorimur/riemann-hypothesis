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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyNu.{u_1} :
    {L : Type u_1} → [NormedField L] → Multiset L → ℝ :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦
      (Multiset.map (fun (z : L) ↦ ‖z‖) (Multiset.filter (fun (z : L) ↦ (1 : ℝ) ≤ ‖z‖) R)).prod

noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyF.{u_1} :
    {L : Type u_1} → [inst : NormedField L] → Multiset L → Polynomial L :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦
      (Multiset.map (fun (z : L) ↦ Polynomial.X - (Polynomial.C : L → Polynomial L) z) R).prod

noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyP.{u_1} :
    {L : Type u_1} → [NormedField L] → Multiset L → Multiset L :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦ Multiset.filter (fun (z : L) ↦ ‖z‖ < (1 : ℝ)) R

private theorem UpperTheory.Reformulated.B.AuxiliaryNormPrimes.norm_sub_le_max' {L : Type*} [NormedField L] [IsUltrametricDist L]
    (x y : L) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.norm_add_le_max x (-y)
  rwa [norm_neg, ← sub_eq_add_neg] at h
