import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_derivative_at_zero_isTangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → (∀ w v, IsDerivAt0 (fun z => (F.ex k P z).left) w v → IsTanAt (F.u k P) v) ∧ (∀ w, ∃! v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsDerivAt0 (fun z => (F.ex k P z).left) w v) ∧ ∀ v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsTanAt (F.u k P) v → ∃! w, IsDerivAt0 (fun z => (F.ex k P z).left) w v := by
  first | exact @GlobalTheory.isDerivAt0_ex_isTanAt | exact GlobalTheory.isDerivAt0_ex_isTanAt | (intros; apply GlobalTheory.isDerivAt0_ex_isTanAt <;> assumption)
