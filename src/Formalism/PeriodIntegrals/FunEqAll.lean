import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Instances
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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPowerSeries.Substitution
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

open Classical

namespace PI.FunEqAll

def JetTdeg {σ : Type*} (m : σ →₀ ℕ) : ℕ := m.sum (fun _ k => k)

def jetLogG (l d : ℕ) [Fact l.Prime] {β : Type*} (v : ZMod d × β) : MvPowerSeries (ZMod d × β) ℂ_[l] :=
  fun m => ∑ e ∈ Finset.range (JetTdeg m + 1),
    if m = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2) ((l ^ 2) ^ e) then (((l : ℂ_[l]) ^ e)⁻¹) else 0

def NonzeroIndexPlace {l : ℕ} [Fact l.Prime] (c : ℂ_[l]) : Prop :=
  c ∈ closure {x : ℂ_[l] | ∃ m : ℕ, 0 < m ∧ Nat.Coprime m l ∧ ∃ (ζ : ℂ_[l]) (a : Fin m → ℚ_[l]),
    ζ ^ m = 1 ∧ x = ∑ k, algebraMap ℚ_[l] ℂ_[l] (a k) * ζ ^ (k : ℕ)}

def InW {l : ℕ} [Fact l.Prime] (c : ℂ_[l]) : Prop := NonzeroIndexPlace c ∧ ‖c‖ ≤ 1

def zL (l d : ℕ) [Fact l.Prime] (s : ZMod d) : MvPowerSeries (ZMod d × Unit) ℂ_[l] :=
  jetLogG l d (s, ())

def zC (l d : ℕ) [Fact l.Prime] (c : Fin 3) (s : ZMod d) : MvPowerSeries (Fin 3 × ZMod d) ℂ_[l] :=
  MvPowerSeries.subst (fun k : ZMod d × Unit => (MvPowerSeries.X (c, k.1) : MvPowerSeries (Fin 3 × ZMod d) ℂ_[l]))
    (zL l d s)

def ExistsIntegralAdditionSeries (l d : ℕ) [Fact l.Prime] : Prop :=
  ∃ Fg : ZMod d → MvPowerSeries (Fin 3 × ZMod d) ℂ_[l],
    (∀ s n, InW (MvPowerSeries.coeff n (Fg s))) ∧
    ∀ s, MvPowerSeries.subst (fun k : ZMod d × Unit => Fg k.1) (zL l d s) = zC l d 0 s + zC l d 1 s

def Target : Prop := ∀ (l d : ℕ) [Fact l.Prime] [NeZero d], ExistsIntegralAdditionSeries l d

end PI.FunEqAll
