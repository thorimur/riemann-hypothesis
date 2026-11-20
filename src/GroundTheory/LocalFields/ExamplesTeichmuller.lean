import Mathlib.Algebra.CharP.Subring
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
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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

namespace GroundTheory.LocalField

open ValuativeRel Polynomial IsLocalRing

namespace EqualChar

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]

instance charP_integer : CharP 𝒪[K] p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (Subtype.ext (by simp))

instance charP_residueField : CharP 𝓀[K] p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (residue 𝒪[K]), CharP.cast_eq_zero, map_zero])

theorem exists_card_residueField_eq : ∃ n : ℕ, 0 < n ∧ Nat.card 𝓀[K] = p ^ n := by
  let := Fintype.ofFinite 𝓀[K]
  obtain ⟨n, -, h⟩ := FiniteField.card 𝓀[K] p
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, h]⟩

noncomputable def residueExponent : ℕ := (exists_card_residueField_eq K p).choose

theorem residueExponent_pos : 0 < residueExponent K p :=
  (exists_card_residueField_eq K p).choose_spec.1

theorem card_residueField : Nat.card 𝓀[K] = p ^ residueExponent K p :=
  (exists_card_residueField_eq K p).choose_spec.2

theorem one_lt_card_residueField : 1 < p ^ residueExponent K p :=
  Nat.one_lt_pow (residueExponent_pos K p).ne' hp.out.one_lt

theorem pow_card_residueField (a : 𝓀[K]) : a ^ p ^ residueExponent K p = a := by
  let := Fintype.ofFinite 𝓀[K]
  rw [← card_residueField, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card a

noncomputable def teichmullerSubring : Subring 𝒪[K] :=
  (iterateFrobenius 𝒪[K] p (residueExponent K p)).eqLocus (RingHom.id _)

theorem mem_teichmullerSubring {x : 𝒪[K]} :
    x ∈ teichmullerSubring K p ↔ x ^ p ^ residueExponent K p = x := Iff.rfl

theorem eq_zero_of_mem_teichmullerSubring {x : 𝒪[K]} (hx : x ∈ teichmullerSubring K p)
    (h0 : residue 𝒪[K] x = 0) : x = 0 := by
  by_contra hne
  have hv0 : 0 < valuation K (x : K) := by
    rw [zero_lt_iff, ne_eq, map_eq_zero]
    exact fun h => hne (Subtype.ext h)
  have hv1 : valuation K (x : K) < 1 := by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h0
    exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one).mp h0
  have h := pow_lt_self_of_lt_one₀ hv0 hv1 (one_lt_card_residueField K p)
  rw [← map_pow, ← Subring.coe_pow, (mem_teichmullerSubring K p).mp hx] at h
  exact lt_irrefl _ h

theorem exists_mem_teichmullerSubring_residue_eq (a : 𝓀[K]) :
    ∃ x ∈ teichmullerSubring K p, residue 𝒪[K] x = a := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  set q := p ^ residueExponent K p with hqdef
  have hq : 1 < q := one_lt_card_residueField K p
  have hq0 : ((q : ℕ) : 𝒪[K]) = 0 :=
    (CharP.cast_eq_zero_iff 𝒪[K] p q).mpr (dvd_pow_self p (residueExponent_pos K p).ne')
  obtain ⟨a₀, rfl⟩ := residue_surjective a
  set f : 𝒪[K][X] := X ^ q - X with hf
  have hmonic : f.Monic := monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hq)
  have hroot : f.eval a₀ ∈ maximalIdeal 𝒪[K] := by
    rw [← residue_eq_zero_iff]
    simp [f, hqdef, pow_card_residueField]
  have hder : IsUnit (Ideal.Quotient.mk (maximalIdeal 𝒪[K]) (f.derivative.eval a₀)) := by
    have : f.derivative.eval a₀ = -1 := by
      simp [f, derivative_X_pow, hq0]
    rw [this, map_neg, map_one]
    exact isUnit_one.neg
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian f hmonic a₀ hroot hder
  refine ⟨x, ?_, ?_⟩
  · rw [mem_teichmullerSubring]
    simpa [f, IsRoot, sub_eq_zero] using hx
  · rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hxa

noncomputable def teichmullerEquiv : teichmullerSubring K p ≃+* 𝓀[K] :=
  RingEquiv.ofBijective ((residue 𝒪[K]).comp (teichmullerSubring K p).subtype)
    ⟨(injective_iff_map_eq_zero _).mpr fun x hx =>
        Subtype.ext (eq_zero_of_mem_teichmullerSubring K p x.2 hx),
      fun a => by
        obtain ⟨x, hx, h⟩ := exists_mem_teichmullerSubring_residue_eq K p a
        exact ⟨⟨x, hx⟩, h⟩⟩

noncomputable def teichmullerHom : 𝓀[K] →+* 𝒪[K] :=
  (teichmullerSubring K p).subtype.comp (teichmullerEquiv K p).symm.toRingHom

theorem residue_teichmullerHom (a : 𝓀[K]) : residue 𝒪[K] (teichmullerHom K p a) = a :=
  (teichmullerEquiv K p).apply_symm_apply a

end EqualChar

end GroundTheory.LocalField
