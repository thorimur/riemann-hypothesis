import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Topology.Instances.ZMod

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Et.TrivTors

abbrev triv (n : ℕ) (V : Scheme.{0}) : Scheme.{0} := ∐ fun _ : ZMod n => V

abbrev proj (n : ℕ) (V : Scheme.{0}) : triv n V ⟶ V := Sigma.desc fun _ => 𝟙 V

def shift (n : ℕ) (V : Scheme.{0}) (k : ZMod n) : triv n V ⟶ triv n V :=
  Sigma.desc fun h => Sigma.ι (fun _ : ZMod n => V) (h + k)

def idx (n : ℕ) (V : Scheme.{0}) : C(↥(triv n V), ZMod n) :=
  ⟨fun x => ((sigmaMk (fun _ : ZMod n => V)).symm x).1,
    (continuous_sigma fun _ => continuous_const).comp (sigmaMk (fun _ : ZMod n => V)).symm.continuous⟩

variable {n : ℕ} {V : Scheme.{0}}

@[reassoc (attr := simp)]
theorem ι_shift (k h : ZMod n) :
    Sigma.ι (fun _ : ZMod n => V) h ≫ shift n V k = Sigma.ι (fun _ : ZMod n => V) (h + k) := by
  simp [shift]

@[reassoc (attr := simp)]
theorem shift_proj (k : ZMod n) : shift n V k ≫ proj n V = proj n V := by
  ext h
  simp [shift]

@[simp]
theorem idx_ι (h : ZMod n) (x : V) : idx n V ((Sigma.ι (fun _ : ZMod n => V) h).base x) = h := by
  have e := sigmaMk_mk (fun _ : ZMod n => V) h x
  change ((sigmaMk (fun _ : ZMod n => V)).symm ((Sigma.ι (fun _ : ZMod n => V) h).base x)).1 = h
  have e' : (sigmaMk (fun _ : ZMod n => V)).symm ((Sigma.ι (fun _ : ZMod n => V) h).base x) = ⟨h, x⟩ :=
    (sigmaMk (fun _ : ZMod n => V)).symm_apply_eq.mpr e.symm
  rw [e']

end GlobalTheory.Et.TrivTors

end
