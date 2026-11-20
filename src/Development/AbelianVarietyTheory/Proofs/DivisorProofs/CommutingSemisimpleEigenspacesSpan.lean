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
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem iSup_jointEigenspace_eq_top_of_separable : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : Type) [AddCommGroup V] [Module C V] [FiniteDimensional C V] (I : Type) (T : I → Module.End C V), (∀ a b, Commute (T a) (T b)) → (∀ a, ∃ f : Polynomial C, f.Separable ∧ Polynomial.aeval (T a) f = 0) → (⨆ χ : I → C, ⨅ a : I, Module.End.eigenspace (T a) (χ a)) = ⊤ := by
  intro C _ _ V _ _ _ I T hc hs
  have hmax : ∀ a μ, (T a).maxGenEigenspace μ = (T a).eigenspace μ := by
    intro a μ
    obtain ⟨f, hf, h0⟩ := hs a
    exact (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf.squarefree h0).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hcomm : Pairwise fun i j => Commute (T i) (T j) := fun i j _ => hc i j
  have hdiag : ∀ a, ⨆ μ, (T a).maxGenEigenspace μ = ⊤ := fun a =>
    Module.End.iSup_maxGenEigenspace_eq_top (T a)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T hcomm hdiag
  simpa only [hmax] using htop

end GlobalTheory
