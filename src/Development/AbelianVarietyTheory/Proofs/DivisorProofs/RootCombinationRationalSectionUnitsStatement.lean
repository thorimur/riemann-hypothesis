import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootCombinationRationalSectionUnits
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts GlobalTheory.ShFam.Pad
open CategoryTheory AlgebraicGeometry GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.Cartier
open scoped Classical
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_combination_rational_section_units : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (W : O.LatModel ∅ c) (τ : D.what₂.Tau), ∃ r : ((GlobalTheory.ArInt.comb (fun i : Fin O.N => W.root ∅ (τ, i)) (fun _ => 1)).B.pull W.V.j).ι → W.V.G.functionFieldˣ, GlobalTheory.Cartier.IsRatSec ((GlobalTheory.ArInt.comb (fun i : Fin O.N => W.root ∅ (τ, i)) (fun _ => 1)).B.pull W.V.j) r ∧ ∀ i, ∀ x ∈ ((GlobalTheory.ArInt.comb (fun i : Fin O.N => W.root ∅ (τ, i)) (fun _ => 1)).B.pull W.V.j).U i, UnitAt x (r i : W.V.G.functionField) := by
  first | exact @GlobalTheory.FlatRat.exists_unit_ratSec_comb_root | exact GlobalTheory.FlatRat.exists_unit_ratSec_comb_root | (intros; apply GlobalTheory.FlatRat.exists_unit_ratSec_comb_root <;> assumption)
