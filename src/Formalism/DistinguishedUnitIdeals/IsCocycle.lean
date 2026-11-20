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
import Mathlib.RingTheory.PowerSeries.Basic
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

noncomputable section

namespace Formalism.ExponentWindows.E

structure Base (O : Type) [CommRing O] where
  ℓ : ℕ
  φ : PowerSeries O →ₐ[O] PowerSeries O
  γ : PowerSeries O →ₐ[O] PowerSeries O
  comm : ∀ a, φ (γ a) = γ (φ a)

def Base.q {O : Type} [CommRing O] (B : Base O) : PowerSeries O :=
  PowerSeries.X + PowerSeries.C (B.ℓ : O)

def Base.p {O : Type} [CommRing O] (B : Base O) (s : ℕ) : PowerSeries O := (⇑B.φ)^[s] B.q

structure Lat {O : Type} [CommRing O] (B : Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] where

  φ : ZMod n → V →+ V

  γ : ZMod n → V →+ V
  φ_semi : ∀ i (a : PowerSeries O) (v : V), φ i (a • v) = B.φ a • φ i v
  γ_semi : ∀ i (a : PowerSeries O) (v : V), γ i (a • v) = B.γ a • γ i v
  comm : ∀ i (v : V), φ i (γ (i - 1) v) = γ i (φ i v)

  N : ZMod n → Submodule (PowerSeries O) V

section
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

def Lat.phiIt (L : Lat B n V) (i : ZMod n) : ℕ → V → V
  | 0, v => v
  | k + 1, v => L.φ (i + (k + 1 : ℕ)) (Lat.phiIt L i k v)

def Lat.pull (L : Lat B n V) (i : ZMod n) (k : ℕ) : Submodule (PowerSeries O) V :=
  Submodule.span (PowerSeries O) (L.phiIt i k '' (L.N i : Set V))

def sm (a : PowerSeries O) (S : Submodule (PowerSeries O) V) : Submodule (PowerSeries O) V :=
  S.map (LinearMap.lsmul (PowerSeries O) V a)

def dv (a : PowerSeries O) (S : Submodule (PowerSeries O) V) : Submodule (PowerSeries O) V :=
  S.comap (LinearMap.lsmul (PowerSeries O) V a)

def Lat.Ic (L : Lat B n V) (c : ZMod n) (w : V) : Prop :=
  L.γ c w - w ∈ sm PowerSeries.X (L.N c)

def Lat.dφ (L : Lat B n V) (m : ZMod n → V) : ZMod n → V := fun i => L.φ i (m (i - 1)) - m i

def Lat.dγ (L : Lat B n V) (m : ZMod n → V) : ZMod n → V := fun i => L.γ i (m i) - m i

def Lat.IsCocycle (L : Lat B n V) (y z : ZMod n → V) : Prop := L.dγ y = L.dφ z

def Lat.IsCobound (L : Lat B n V) (y z : ZMod n → V) : Prop :=
  ∃ m : ZMod n → V, y = L.dφ m ∧ z = L.dγ m

end

structure LatHom {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V V' : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] [AddCommGroup V'] [Module (PowerSeries O) V']
    (L : Lat B n V) (L' : Lat B n V') where
  f : V →ₗ[PowerSeries O] V'
  φ_comm : ∀ i v, f (L.φ i v) = L'.φ i (f v)
  γ_comm : ∀ i v, f (L.γ i v) = L'.γ i (f v)
  map_N : ∀ i v, v ∈ L.N i → f v ∈ L'.N i

end Formalism.ExponentWindows.E
