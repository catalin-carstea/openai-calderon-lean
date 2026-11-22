module

public import Proof.CalderonN.BallRegularity.SpatialJetFields
public import Proof.CalderonN.FiniteJetBoundCalculus

/-! From ParameterSpatialJetBounds in the checked Proposition 5.3 release f308cb9d. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open CalderonN.SpatialJetFields

variable {P E V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma norm_iteratedFDeriv_of_iteratedFDeriv (f : E → V) (x : E) (n j : ℕ) :
    ‖iteratedFDeriv ℝ n (iteratedFDeriv ℝ j f) x‖ = ‖iteratedFDeriv ℝ (n+j) f x‖ := by
  induction j generalizing n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp,LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    simp only [Nat.add_zero]
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    have hIso := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜:=ℝ) (E:=E)
      (F:=E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => E) V)
      (G:=ContinuousMultilinearMap ℝ (fun _ : Fin (j+1) => E) V)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) V).symm
      (fderiv ℝ (iteratedFDeriv ℝ j f)) x n
    rw [hIso,norm_iteratedFDeriv_fderiv,ih]
    exact congrArg (fun k : ℕ => ‖iteratedFDeriv ℝ k f x‖) (show n+1+j = n+(j+1) by omega)

lemma norm_iteratedFDeriv_left_slice_le (f : P × E → V) (hf : ContDiff ℝ ∞ f)
    (p : P) (x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q => f (q,x)) p‖ ≤ ‖iteratedFDeriv ℝ n f (p,x)‖ := by
  let g := fun z : P × E => f ((0,x)+z)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have hEq : (fun q => f (q,x)) = g ∘ ContinuousLinearMap.inl ℝ P E := by
    funext q
    simp only [g,Function.comp_def,ContinuousLinearMap.inl_apply,Prod.mk_add_mk,zero_add,add_zero]
  rw [hEq,(ContinuousLinearMap.inl ℝ P E).iteratedFDeriv_comp_right hg p (by simp)]
  have hNorm := (iteratedFDeriv ℝ n g ((ContinuousLinearMap.inl ℝ P E) p)).norm_compContinuousLinearMap_le
    (fun _ => ContinuousLinearMap.inl ℝ P E)
  have hProd : (∏ _ : Fin n,‖ContinuousLinearMap.inl ℝ P E‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inl_le_one ℝ P E)
  have hN := hNorm.trans (mul_le_of_le_one_right (norm_nonneg _) hProd)
  have hShift : iteratedFDeriv ℝ n g ((ContinuousLinearMap.inl ℝ P E) p) =
      iteratedFDeriv ℝ n f (p,x) := by
    dsimp only [g]
    rw [iteratedFDeriv_comp_add_left]
    simp only [ContinuousLinearMap.inl_apply,Prod.mk_add_mk,zero_add,add_zero]
  rw [hShift] at hN ⊢
  exact hN

lemma norm_iteratedFDeriv_spatialJetField_le (f : P × E → V) (hf : ContDiff ℝ ∞ f)
    (p : P × E) (n j : ℕ) :
    ‖iteratedFDeriv ℝ n (spatialJetField j f) p‖ ≤ ‖iteratedFDeriv ℝ (n+j) f p‖ := by
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (F:=V)
    (fun _ : Fin j => ContinuousLinearMap.inr ℝ P E)
  have hL : ‖L‖ ≤ 1 :=
    (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le V _).trans
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ P E))
  have hComp := norm_iteratedFDeriv_clm_comp_le L (iteratedFDeriv ℝ j f) p
    (hf.iteratedFDeriv_right (m:=∞) (by simp)).contDiffAt n
  have hBound := hComp.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))
  rw [norm_iteratedFDeriv_of_iteratedFDeriv] at hBound
  exact hBound

/-- The mixed jets required by native multiplier calculus are contractions
    of the full joint coefficient jet, with no dimension or cutoff loss. -/
theorem norm_iteratedFDeriv_parameter_spatial_jet_le (f : P × E → V) (hf : ContDiff ℝ ∞ f)
    (p : P) (x : E) (n j : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q => iteratedFDeriv ℝ j (fun z => f (q,z)) x) p‖ ≤
      ‖iteratedFDeriv ℝ (n+j) f (p,x)‖ := by
  have hEq : (fun q => iteratedFDeriv ℝ j (fun z => f (q,z)) x) =
      fun q => spatialJetField j f (q,x) := by
    funext q
    exact (spatialJetField_eq_iteratedFDeriv j f hf q x).symm
  rw [hEq]
  exact (norm_iteratedFDeriv_left_slice_le (spatialJetField j f) (contDiff_spatialJetField j f hf) p x n).trans
    (norm_iteratedFDeriv_spatialJetField_le f hf (p,x) n j)

end ShrinkingSpheres
