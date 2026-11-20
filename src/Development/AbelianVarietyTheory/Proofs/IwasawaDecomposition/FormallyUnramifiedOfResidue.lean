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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RingHom.Unramified
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
open IsLocalRing

namespace GlobalTheory

theorem formallyUnramified_of_finite_map_maximalIdeal
    {A B R : Type} [CommRing A] [CommRing B] [IsLocalRing B] [CommRing R] [IsLocalRing R]
    (ι : A →+* B) (ψ : B →+* R) (hψ : ψ.Finite) (hm : (maximalIdeal B).map ψ = maximalIdeal R)
    (hu : ((residue R).comp (ψ.comp ι)).FormallyUnramified) : ψ.FormallyUnramified := by
  have hloc : IsLocalHom ψ := by
    refine ⟨fun b hb => ?_⟩
    by_contra h
    have hb' : b ∈ maximalIdeal B := (mem_maximalIdeal b).2 h
    have : ψ b ∈ maximalIdeal R := hm ▸ Ideal.mem_map_of_mem ψ hb'
    exact (mem_maximalIdeal _).1 this hb
  algebraize [ψ, ι, ψ.comp ι]
  have h1 : Algebra.FormallyUnramified A (ResidueField R) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    exact hu
  have h2 : Algebra.FormallyUnramified B (ResidueField R) := .of_restrictScalars A _ _
  have h3 : Algebra.FormallyUnramified (ResidueField B) (ResidueField R) := .of_restrictScalars B _ _
  have h4 : Algebra.EssFiniteType B (ResidueField R) := .comp _ R _
  have h5 : Algebra.EssFiniteType (ResidueField B) (ResidueField R) := .of_comp B _ _
  have h6 : Algebra.IsSeparable (ResidueField B) (ResidueField R) :=
    Algebra.FormallyUnramified.isSeparable _ _
  have h7 : Algebra.FormallyUnramified B R := Algebra.FormallyUnramified.of_map_maximalIdeal hm
  exact RingHom.formallyUnramified_algebraMap.2 h7

end GlobalTheory
