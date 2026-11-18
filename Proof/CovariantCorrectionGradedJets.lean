import Proof.BoundedCorrectionStrongHalf
import Proof.ActualFrameCorrectionGraded
import Proof.ActualCorrectionProductBudget

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_radialCorrectionAdjointSobolevL_grade_le (s : ℝ) (q : X →L[ℝ] ℝ) :
    ‖radialCorrectionAdjointSobolevL s q‖ ≤ 6*‖q‖*radialDriftSobolevBound (-s) := by
  have h := norm_sphereSobolevRadialDriftAdjointL_le sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics s (radialCorrectionVector q)
  have hSum : (2*∑ j : I,|(radialCorrectionVector q) j|) ≤ 6*‖q‖ :=
    (mul_le_mul_of_nonneg_left (radialCorrectionVector_coordinate_sum_le q) (by norm_num)).trans_eq (by ring)
  exact h.trans (mul_le_mul_of_nonneg_right hSum (zero_le_one.trans (le_max_left _ _)))

/-- The same actual bounded covariant correction jet at every genuine grade. -/
def firstFrameAdjointCovariantJetAtL (s : ℝ) (d : Data) (y a : X) (j : I) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  firstAdjointCorrectionSobolevL s (firstDensityCovariantDerivativeL d y a)
      (scaledFrameLogRadius d.radius d.frame j y) j+
    scaledFrameLogRadiusCovariant d.γ d.radius d.frame y a j •
      radialCorrectionAdjointSobolevL s (firstDensityLogCovector d y)

lemma firstFrameAdjointCovariantJetAtL_zero (d : Data) (y a : X) (j : I) :
    firstFrameAdjointCovariantJetAtL 0 d y a j=firstFrameAdjointCovariantJetL d y a j := by
  simp only [firstFrameAdjointCovariantJetAtL,firstAdjointCorrectionSobolevL,
    radialCorrectionAdjointSobolevL_zero,firstFrameAdjointCovariantJetL,
    firstRadialCoefficientCovariantJetL,firstRadialCorrectionL_eq_covector]

lemma firstFrameAdjointCovariantJetAtL_inclusion (s t : ℝ) (hst : t ≤ s)
    (d : Data) (y a : X) (j : I) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hst (firstFrameAdjointCovariantJetAtL s d y a j u)=
      firstFrameAdjointCovariantJetAtL t d y a j (sphereSobolevInclusionL s t hst u) := by
  have h1 := firstAdjointCorrectionSobolevL_inclusion s t hst (firstDensityCovariantDerivativeL d y a)
    (scaledFrameLogRadius d.radius d.frame j y) j u
  have h2 := sphereSobolevInclusionL_radialDriftAdjoint sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics s t hst (radialCorrectionVector (firstDensityLogCovector d y)) u
  simpa only [firstFrameAdjointCovariantJetAtL,ContinuousLinearMap.comp_apply,
    _root_.add_apply,_root_.smul_apply,map_add,map_smul,radialCorrectionAdjointSobolevL] using
      congrArg₂ (fun v w => v+scaledFrameLogRadiusCovariant d.γ d.radius d.frame y a j • w) h1 h2

theorem uniform_first_frame_covariant_grade_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (s : ℝ) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
        ‖firstFrameAdjointCovariantJetAtL s d y (d.frame y i) j‖ ≤ C := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let D := K*((K*M2+K^2*M1^2)+(K*M1)*(243*K*M1))
  let BQ := K^2*M1
  let Bs := radialDriftSobolevBound s
  let Bn := radialDriftSobolevBound (-s)
  let A := 2*(Bs+Bn)+1
  let C := 6*(D*K)*Bn*A+(|Cj 2|+1)*(6*BQ*Bn)
  have hK0 := zero_le_one.trans hK
  have hD : 0 ≤ D := by dsimp only [D,M1,M2];positivity
  have hBQ : 0 ≤ BQ := by dsimp only [BQ,M1];positivity
  have hBs : 0 ≤ Bs := zero_le_one.trans (le_max_left _ _)
  have hBn : 0 ≤ Bn := zero_le_one.trans (le_max_left _ _)
  have hA : 0 ≤ A := by dsimp only [A];positivity
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hε1 d hd y hy i j
  have hyΩ := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hyΩ
  have hE : ‖d.frame y i‖ ≤ K := by
    have hh := (frameVectorLinear d.frame y).le_opNorm (axis i)
    rw [frameVectorLinear_apply,frameVector_axis,norm_axis,mul_one] at hh
    exact hh.trans (hd.1.1.norm_frameVectorLinear_le hK hyΩ d.frame hFrame)
  have hCov : ‖firstDensityCovariantDerivativeL d y (d.frame y i)‖ ≤ D*K := by
    rw [hd.1.firstDensityCovariantDerivativeL_eq hΩ (zero_lt_one.trans_le hK) hyΩ]
    have hh := hd.1.norm_firstDensityCovariantLinearL_le hΩ hK hm hyΩ (d.frame y i)
    exact hh.trans (mul_le_mul_of_nonneg_left hE hD)
  have hBase : ‖firstDensityLogCovector d y‖ ≤ BQ := hd.1.norm_firstDensityLogCovector_le hΩ hK hm hyΩ
  have ht : |scaledFrameLogRadius d.radius d.frame j y| ≤ 1 := hd.scaled_frame_logRadius_bound hf hε hε1 hy j
  have hdt : |scaledFrameLogRadiusCovariant d.γ d.radius d.frame y (d.frame y i) j| ≤ |Cj 2|+1 :=
    hd.scaledFrameLogRadiusCovariant_frame_le hY hε1 hy i j
  have hFirst : ‖firstAdjointCorrectionSobolevL s (firstDensityCovariantDerivativeL d y (d.frame y i))
      (scaledFrameLogRadius d.radius d.frame j y) j‖ ≤ 6*(D*K)*Bn*A :=
    (norm_firstAdjointCorrectionSobolevL_le s _ _ j).trans (by dsimp only [Bn,A,Bs];gcongr)
  have hRadial : ‖radialCorrectionAdjointSobolevL s (firstDensityLogCovector d y)‖ ≤ 6*BQ*Bn :=
    (norm_radialCorrectionAdjointSobolevL_grade_le s _).trans (by dsimp only [Bn];gcongr)
  have hLast : ‖scaledFrameLogRadiusCovariant d.γ d.radius d.frame y (d.frame y i) j •
      radialCorrectionAdjointSobolevL s (firstDensityLogCovector d y)‖ ≤ (|Cj 2|+1)*(6*BQ*Bn) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hdt hRadial (norm_nonneg _) (by positivity)
  exact (norm_add_le _ _).trans (add_le_add hFirst hLast)

def physicalFirstCorrectionCovariantJetAtL (s : ℝ) (d : Data) (y a b : X) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  (∑ j : I,frameCoordinateLinear d.γ d.frame y j b • firstFrameAdjointCovariantJetAtL s d y a j)+
  (∑ j : I,frameCoordinateLinear d.γ d.frame y j (connection d.γ y a b) • firstFrameAdjointCorrectionAtL s d y j)

lemma physicalFirstCorrectionCovariantJetAtL_zero (d : Data) (y a b : X) :
    physicalFirstCorrectionCovariantJetAtL 0 d y a b=physicalFirstCorrectionBoundedCovariantJetL d y a b := by
  simp only [physicalFirstCorrectionCovariantJetAtL,physicalFirstCorrectionBoundedCovariantJetL,
    firstFrameAdjointCovariantJetAtL_zero,firstFrameAdjointCorrectionAtL_zero]

lemma physicalFirstCorrectionCovariantJetAtL_inclusion (s t : ℝ) (hst : t ≤ s)
    (d : Data) (y a b : X) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hst (physicalFirstCorrectionCovariantJetAtL s d y a b u)=
      physicalFirstCorrectionCovariantJetAtL t d y a b (sphereSobolevInclusionL s t hst u) := by
  simp only [physicalFirstCorrectionCovariantJetAtL,_root_.add_apply,_root_.sum_apply,_root_.smul_apply,
    map_add,map_sum,map_smul,firstFrameAdjointCovariantJetAtL_inclusion,firstFrameAdjointCorrectionAtL_inclusion]

theorem uniform_physical_correction_covariant_grade_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (s : ℝ) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i b : I,
        ‖physicalFirstCorrectionCovariantJetAtL s d y (d.frame y i) (axis b)‖ ≤ C := by
  obtain ⟨CT,hCT,hFrameBound⟩ := uniform_first_frame_covariant_grade_bound hY hΩ s hm K ρ c₀ M Cj hK
  let CC := 9*|M 0| *K
  let CG := 243*K*|M ⟨1,by omega⟩|
  let CΓ := CC*(CG*K)
  let CF := firstCorrectionGradeBound s K (M ⟨1,by omega⟩)
  let C := 3*K*CT+3*CΓ*CF
  have hK0 := zero_le_one.trans hK
  have hCC : 0 ≤ CC := by dsimp only [CC];positivity
  have hCG : 0 ≤ CG := by dsimp only [CG];positivity
  have hCΓ : 0 ≤ CΓ := mul_nonneg hCC (mul_nonneg hCG hK0)
  have hCF : 0 ≤ CF := firstCorrectionGradeBound_nonneg _ _ _
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hε1 d hd y hy i b
  have hyΩ := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hyΩ
  have hE : ‖d.frame y i‖ ≤ K := by
    have hh := (frameVectorLinear d.frame y).le_opNorm (axis i)
    rw [frameVectorLinear_apply,frameVector_axis,norm_axis,mul_one] at hh
    exact hh.trans (hd.1.1.norm_frameVectorLinear_le hK hyΩ d.frame hFrame)
  have hΓ : ‖connectionBilinear d.γ y‖ ≤ CG := hd.1.connection_budget (zero_lt_one.trans_le hK) (by omega) hyΩ
  have hConn : ‖connection d.γ y (d.frame y i) (axis b)‖ ≤ CG*K := by
    rw [← connectionBilinear_apply]
    calc
      _ ≤ ‖connectionBilinear d.γ y‖*‖d.frame y i‖*‖axis b‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ CG*K*1 := by rw [norm_axis];gcongr
      _ = _ := mul_one _
  have hCof (j : I) : ‖frameCoordinateLinear d.γ d.frame y j‖ ≤ CC :=
    hd.1.1.norm_frameCoordinateLinear_le hK hyΩ d.frame hFrame |M 0| (abs_nonneg _)
      (fun a c => (hd.1.reference_entry_bound hyΩ a c).trans (le_abs_self _)) j
  have hc (j : I) : |frameCoordinateLinear d.γ d.frame y j (axis b)| ≤ K := by
    rw [frameCoordinateLinear_apply]
    exact hd.1.1.frame_coordinate_abs_bound hK d.frame hyΩ hFrame b j
  have hcΓ (j : I) : |frameCoordinateLinear d.γ d.frame y j (connection d.γ y (d.frame y i) (axis b))| ≤ CΓ := by
    have hh := ((frameCoordinateLinear d.γ d.frame y j).le_opNorm _).trans
      (mul_le_mul (hCof j) hConn (norm_nonneg _) hCC)
    simpa only [Real.norm_eq_abs] using hh
  have hF (j : I) : ‖firstFrameAdjointCorrectionAtL s d y j‖ ≤ CF :=
    hd.norm_firstFrameAdjointCorrectionAtL_le hΩ hm hK hf hε hε1 s hy j
  exact norm_coframe_covariant_tensor_jet_le d y (d.frame y i) (axis b)
    (fun j => firstFrameAdjointCorrectionAtL s d y j)
    (fun j => firstFrameAdjointCovariantJetAtL s d y (d.frame y i) j)
    hK0 hCΓ hc hcΓ hF (hFrameBound floor hf ε hε hε1 d hd y hy i)

end ShrinkingSpheres
