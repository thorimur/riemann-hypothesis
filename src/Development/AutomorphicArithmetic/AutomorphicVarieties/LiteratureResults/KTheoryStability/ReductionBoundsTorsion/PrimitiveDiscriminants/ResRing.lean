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

open Matrix
open scoped Kronecker

namespace PositivityTheory.KB.LargePrimeDiscriminant

variable {R S : Type} [CommRing R] [CommRing S]

noncomputable def resRing (d n : ℕ) (ρ : S →+* Matrix (Fin d) (Fin d) R) :
    Matrix (Fin n) (Fin n) S →+* Matrix (Fin (d * n)) (Fin (d * n)) R :=
  ((Matrix.reindexAlgEquiv R R ((Equiv.prodComm (Fin n) (Fin d)).trans finProdFinEquiv)).toRingEquiv.toRingHom.comp
    (Matrix.compRingEquiv (Fin n) (Fin d) R).toRingHom).comp ρ.mapMatrix

noncomputable def res (d n : ℕ) (ρ : S →+* Matrix (Fin d) (Fin d) R) :
    GL (Fin n) S →* GL (Fin (d * n)) R :=
  Units.map (resRing d n ρ).toMonoidHom

end PositivityTheory.KB.LargePrimeDiscriminant
