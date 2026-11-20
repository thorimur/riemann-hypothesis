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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace Formalism.L2.SG.Pf.Lem3Mass

open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnitaryGroupLocal
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

section Trace

variable (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hfix : ∀ y : E, σ y = y → y ∈ (algebraMap F E).range)

def trF (y : E) : F :=
  Classical.choose (hfix (y + σ y) (by rw [map_add, hσ, add_comm]))

theorem trF_spec (y : E) : algebraMap F E (trF σ hσ hfix y) = y + σ y :=
  Classical.choose_spec (hfix (y + σ y) (by rw [map_add, hσ, add_comm]))

theorem trF_add (y z : E) : trF σ hσ hfix (y + z) = trF σ hσ hfix y + trF σ hσ hfix z := by
  apply (algebraMap F E).injective
  rw [map_add, trF_spec, trF_spec, trF_spec, map_add]
  abel

theorem trF_smul (c : F) (y : E) : trF σ hσ hfix (c • y) = c * trF σ hσ hfix y := by
  apply (algebraMap F E).injective
  rw [map_mul, trF_spec, trF_spec, Algebra.smul_def, map_mul, AlgHom.commutes, mul_add]

def trA : E ⊗[F] v.adicCompletion F →ₗ[F] v.adicCompletion F :=
  TensorProduct.lift (LinearMap.mk₂ F (fun (e : E) (r : v.adicCompletion F) => trF σ hσ hfix e • r)
    (fun e e' r => by rw [trF_add, add_smul])
    (fun c e r => by rw [trF_smul, mul_smul])
    (fun e r r' => by rw [smul_add])
    (fun c e r => by rw [smul_comm]))

end Trace

section D1

variable (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hfix : ∀ y : E, σ y = y → y ∈ (algebraMap F E).range)

theorem coe_algebraMap_int (t : 𝓞 F) :
    algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t) = algebraMap F E (t : F) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]

end D1

end Formalism.L2.SG.Pf.Lem3Mass
