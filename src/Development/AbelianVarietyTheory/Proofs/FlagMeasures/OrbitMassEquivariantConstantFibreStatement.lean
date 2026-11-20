import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEquivariantConstantFibre
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_mass_equivariant_constant_fibre : ∀ {G : Type} [Group G] (Γ : Subgroup G) (Y Z : Type) [MulAction G Y] [MulAction G Z] (f : Y → Z) (S : Set Z) (n : ℕ), (∀ (g : G) (y : Y), f (g • y) = g • f y) → (∀ (g : G) (z : Z), z ∈ S → g • z ∈ S) → (∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n) → (∀ z, z ∉ S → IsEmpty {y // f y = z}) → (∑' o : MulAction.orbitRel.Quotient Γ Y, ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) = (n : ℝ≥0∞) * ∑' o : MulAction.orbitRel.Quotient Γ Z, if o.out ∈ S then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0 := by
  first | exact @GlobalTheory.MassFibre.mass_fibre | exact GlobalTheory.MassFibre.mass_fibre | (intros; apply GlobalTheory.MassFibre.mass_fibre <;> assumption)
