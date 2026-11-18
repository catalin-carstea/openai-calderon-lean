import Proof.ModelDefectFirstCoefficientForm
import Proof.FirstCovariantCoordinateAdjoint
import Proof.ModelAdjointDefectSectionApplication
import Proof.AmbientHigherSobolevSection
import Proof.CanonicalScalarModelDefectSecondPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def ambientModelAdjointDefectSection (d : Data) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G)
    (x : X) : SphereSobolev 2 :=
  modelAdjointDefectSobolevL 3 d x (ambientHigherSobolevSection 3 (by norm_num) G hG x)

def firstModelDefectRealForm (d : Data) (B : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (b : I) (y : X) : ℝ :=
  ⟪sphereSobolevInclusionL 2 0 (by norm_num) (ambientSobolevSection 2 (by norm_num) G hG y),
    B y (highSectionCovariantDerivative d (ambientModelAdjointDefectSection d G hG) y (axis b))⟫_ℝ

def firstModelDefectBudget (K C2 CB : ℝ) : ℝ :=
  CB*((∑ i : I,‖flatLoweringSobolevL (1/2:ℝ) i‖)+modelAdjointDefectFirstAxisBudget K C2)

lemma firstModelDefectBudget_nonneg (K C2 CB : ℝ) (hK : 1 ≤ K) (hCB : 0 ≤ CB) :
    0 ≤ firstModelDefectBudget K C2 CB := by
  have hCJ : 0 ≤ modelAdjointDefectFirstAxisBudget K C2 := by
    dsimp only [modelAdjointDefectFirstAxisBudget]
    positivity
  exact mul_nonneg hCB (add_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _)) hCJ)

theorem canonical_first_model_defect_form_bound {Y Ω : Set X}
    (hY : IsOpen Y) (d : Data) {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hf : 1 ≤ floor)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (P : PhysicalPrincipalData Y d CF CT) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G)
    {y : X} (hy : y ∈ Y) (b : I)
    (A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hA : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp A=
      (P.firstCovariantCoordinateHalfL b y).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (CB : ℝ) (hCB : 0 ≤ CB) (hε : 0 ≤ ε)
    (hAN : ‖A‖ ≤ CB*ε/beta d.γ d.radius y) :
    |firstModelDefectRealForm d (P.firstCovariantCoordinateCoarseL b) G hG b y| ≤
      firstModelDefectBudget K (Cj 2) CB*ε*
        halfCovariantDirectionEnergy d (ambientSobolevSection (3/2:ℝ) (by norm_num) G hG) y
          (beta d.γ d.radius y) (axis b) := by
  let U := ambientSobolevSection 2 (by norm_num) G hG
  let UH := ambientSobolevSection (3/2:ℝ) (by norm_num) G hG
  let V := ambientHigherSobolevSection 3 (by norm_num) G hG
  have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hUV (x : X) : sphereSobolevInclusionL 3 2 (by norm_num) (V x)=U x :=
    ambientHigherSobolevSection_inclusion 3 2 (by norm_num) (by norm_num) (by norm_num) G hG x
  have hUH : sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (U y)=UH y :=
    ambientSobolevSection_inclusion 2 (3/2:ℝ) (by norm_num) (by norm_num) (by norm_num) G hG y
  have hMass : sphereSobolevInclusionL 2 1 (by norm_num) (U y)=
      sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (UH y) := by
    rw [←hUH,sphereSobolevInclusionL_trans_apply]
  have hMass0 : sphereSobolevInclusionL 2 0 (by norm_num) (U y)=
      sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (UH y) := by
    rw [←hUH,sphereSobolevInclusionL_trans_apply]
  have hD := highSectionCovariantDerivative_modelAdjointDefect_three_coarse hY d hg
    (zero_lt_one.trans_le hK) he hFrame hlog U V hUV hy
    ((contDiff_ambientSobolevSection 2 (by norm_num) G hG).differentiable (by simp) y)
    ((contDiff_ambientHigherSobolevSection 3 (by norm_num) G hG).differentiable (by simp) y) (axis b)
  have hD' : sphereSobolevInclusionL 1 0 (by norm_num)
      (highSectionCovariantDerivative d (ambientModelAdjointDefectSection d G hG) y (axis b))=
      modelAdjointDefectCoarseL d y (highSectionCovariantDerivative d U y (axis b))+
        modelAdjointDefectFirstCoarseL d (axis b) y
          (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (UH y)) := by
    calc
      _ = modelAdjointDefectFirstCoarseL d (axis b) y (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+
          modelAdjointDefectCoarseL d y (highSectionCovariantDerivative d U y (axis b)) := hD
      _ = modelAdjointDefectFirstCoarseL d (axis b) y
          (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (UH y))+
          modelAdjointDefectCoarseL d y (highSectionCovariantDerivative d U y (axis b)) :=
        congrArg (fun z => modelAdjointDefectFirstCoarseL d (axis b) y z+
          modelAdjointDefectCoarseL d y (highSectionCovariantDerivative d U y (axis b))) hMass
      _ = _ := add_comm _ _
  have hβ : 0 < beta d.γ d.radius y := zero_lt_one.trans_le
    (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hCJ : 0 ≤ modelAdjointDefectFirstAxisBudget K (Cj 2) := by
    dsimp only [modelAdjointDefectFirstAxisBudget]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hK)) (abs_nonneg _))
      (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  have hF := hd.2.2.2.2.1.norm_modelAdjointDefectFirstCoarseL_axis_le hY d hg hK hy (hFrame y hy) b
  have hh := model_defect_first_coefficient_form_bound d y (hFrame y hy)
    (P.firstCovariantCoordinateCoarseL b y) (P.firstCovariantCoordinateHalfL b y) A
    (modelAdjointDefectFirstCoarseL d (axis b) y)
    (P.firstCovariantCoordinate_coarse_half_compatible hd hY hy b) hA CB
    (modelAdjointDefectFirstAxisBudget K (Cj 2)) ε hCB hCJ hε hβ hAN hF (UH y)
    (highSectionCovariantDerivative d (ambientModelAdjointDefectSection d G hG) y (axis b))
    (highSectionCovariantDerivative d U y (axis b)) hD'
  have hHalf := canonical_half_covariant_section_eq d G hG y (axis b)
  rw [←hMass0] at hh
  simpa only [firstModelDefectRealForm,firstModelDefectBudget,halfCovariantDirectionEnergy,hHalf,U,UH] using hh

lemma contDiffOn_ambientModelAdjointDefectSection {Y : Set X} (hY : IsOpen Y)
    (d : Data) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y) :
    ContDiffOn ℝ ∞ (ambientModelAdjointDefectSection d G hG) Y :=
  (contDiffOn_modelAdjointDefectSobolevL hY 3 d hlog he).clm_apply
    (contDiff_ambientHigherSobolevSection 3 (by norm_num) G hG).contDiffOn

end ShrinkingSpheres
