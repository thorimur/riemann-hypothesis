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

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Topology
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.BlockD

variable {L : Type} [Field L] [NumberField L]

theorem isOpen_ker_of_pow_eq_one {G : Type*} [Group G] [TopologicalSpace G] (χ : G →* ℂˣ)
    (hχ : Continuous χ) {n : ℕ} (hn : 0 < n) (h : χ ^ n = 1) : IsOpen (χ.ker : Set G) := by
  have hF : {z : ℂˣ | z ^ n = 1}.Finite := by
    refine ((Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.preimage
      Units.val_injective.injOn).subset ?_
    intro z hz
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_nthRoots hn]
    have := congrArg Units.val (show z ^ n = 1 from hz)
    simpa using this
  have hC : IsClosed ({z : ℂˣ | z ^ n = 1} \ {1}) := (hF.subset Set.sdiff_subset).isClosed
  have hpow : ∀ g, χ g ^ n = 1 := fun g ↦ by
    have := congrArg (fun f : G →* ℂˣ ↦ f g) h
    simpa using this
  have heq : (χ.ker : Set G) = χ ⁻¹' ({z : ℂˣ | z ^ n = 1} \ {1})ᶜ := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, not_not]
    exact ⟨fun h1 _ ↦ h1, fun h1 ↦ h1 (hpow g)⟩
  rw [heq]
  exact hC.isOpen_compl.preimage hχ

end GroundTheory.BlockD
