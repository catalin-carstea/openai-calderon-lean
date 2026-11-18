import Proof.ScalarModelDefectSecondReduction
import Proof.ModelAdjointDefectPairing
import Proof.ScalarModelDefectFourFormBound
import Proof.CanonicalCoarseTripleEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

def modelAdjointDefectFirstAxisBudget (K C2 : ℝ) : ℝ :=
  3*K*|C2| *(∑ i : I,‖flatOneLoweringL i‖)

def scalarModelDefectSecondBudget (K C2 A A1 : ℝ) : ℝ :=
  A*(∑ i : I,‖flatLoweringSobolevL (1/2:ℝ) i‖)+A*modelAdjointDefectFirstAxisBudget K C2+
    A1*(∑ i : I,‖flatRaisingSobolevL (3/2:ℝ) i‖)+A1*modelAdjointDefectFirstAxisBudget K C2

lemma scalarModelDefectSecondBudget_nonneg (K C2 A A1 : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hA1 : 0 ≤ A1) :
    0 ≤ scalarModelDefectSecondBudget K C2 A A1 := by
  dsimp only [scalarModelDefectSecondBudget,modelAdjointDefectFirstAxisBudget]
  positivity

/-- Actual reduced scalar/model-defect contribution on canonical
sections. Genuine half inclusions and the true raising adjoint give the
four required angular forms; only original scalar coefficient weights remain. -/
theorem canonical_scalar_model_defect_second_remainder_bound {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y d.γ d.frame d.radius floor c₀ Cj) (hf : 1 ≤ floor)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (q : X → ℝ)
    (mu A A1 ε : ℝ) (hmu : 0 ≤ mu) (hA : 0 ≤ A) (hA1 : 0 ≤ A1) (hε : 0 ≤ ε)
    {y : X} (hy : y ∈ Y)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (a b : I)
    (hq : |q y| ≤ mu*A*ε/(beta d.γ d.radius y)^2)
    (hdq : |fderiv ℝ q y (axis a)| ≤ mu*A1*ε/beta d.γ d.radius y) :
    |scalarModelDefectSecondRemainder d q (ambientSobolevSection 2 (by norm_num) G hG) (axis a) (axis b) y| ≤
      scalarModelDefectSecondBudget K (Cj 2) A A1*mu*ε*
        (halfCovariantDirectionEnergy d (ambientSobolevSection (3/2:ℝ) (by norm_num) G hG) y
            (beta d.γ d.radius y) (axis a)+
         halfCovariantDirectionEnergy d (ambientSobolevSection (3/2:ℝ) (by norm_num) G hG) y
            (beta d.γ d.radius y) (axis b)) := by
  let U := ambientSobolevSection 2 (by norm_num) G hG
  let H := ambientSobolevSection (3/2:ℝ) (by norm_num) G hG
  let β := beta d.γ d.radius y
  let Da := highSectionCovariantDerivative d U y (axis a)
  let Db := highSectionCovariantDerivative d U y (axis b)
  let Va := halfSectionCovariantDerivativeL d H y (axis a)
  let Vb := halfSectionCovariantDerivativeL d H y (axis b)
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  let I21 := sphereSobolevInclusionL 2 1 (by norm_num)
  let M0 := I21 (U y)
  let M00 := I10 M0
  let Z := modelAdjointDefectCoarseL d y
  let J := modelAdjointDefectFirstCoarseL d (axis b) y
  let CZ := ∑ i : I,‖flatLoweringSobolevL (1/2:ℝ) i‖
  let CZ1 := modelAdjointDefectFirstAxisBudget K (Cj 2)
  let CA := ∑ i : I,‖flatRaisingSobolevL (3/2:ℝ) i‖
  have hCZ : 0 ≤ CZ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hCA : 0 ≤ CA := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hCZ1 : 0 ≤ CZ1 := by dsimp only [CZ1,modelAdjointDefectFirstAxisBudget];positivity
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hp.2 y hy).2.1)
  have hHa : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) Da=Va :=
    (canonical_half_covariant_section_eq d G hG y (axis a)).symm
  have hHb : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) Db=Vb :=
    (canonical_half_covariant_section_eq d G hG y (axis b)).symm
  have hM : M0=sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (H y) := by
    calc
      _ = ambientSobolevSection 1 (by norm_num) G hG y := ambientSobolevSection_inclusion 2 1 (by norm_num) (by norm_num) (by norm_num) G hG y
      _ = _ := (ambientSobolevSection_inclusion (3/2:ℝ) 1 (by norm_num) (by norm_num) (by norm_num) G hG y).symm
  have hM00 : M00=sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (H y) := by
    dsimp only [M00,I10]
    rw [hM,sphereSobolevInclusionL_trans_apply]
  have hMN : ‖M0‖ ≤ ‖H y‖ := hM ▸ norm_sphereSobolevInclusionL_apply_le (3/2:ℝ) 1 (by norm_num) (H y)
  have hM00N : ‖M00‖ ≤ ‖H y‖ := hM00 ▸ norm_sphereSobolevInclusionL_apply_le (3/2:ℝ) 0 (by norm_num) (H y)
  have hDaN : ‖I10 Da‖ ≤ ‖Va‖ := by
    have hh : I10 Da=sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) Va := by
      rw [←hHa,sphereSobolevInclusionL_trans_apply]
    rw [hh]
    exact norm_sphereSobolevInclusionL_apply_le (1/2:ℝ) 0 (by norm_num) Va
  have hJN : ‖J‖ ≤ CZ1*β^2 := hp.norm_modelAdjointDefectFirstCoarseL_axis_le hY d hg hK hy hFrame b
  have hJM : ‖J M0‖ ≤ (CZ1*β^2)*‖H y‖ := (J.le_opNorm M0).trans
    (mul_le_mul hJN hMN (norm_nonneg _) (mul_nonneg hCZ1 (sq_nonneg β)))
  have hx1 : |⟪I10 Da,Z Db⟫_ℝ| ≤ CZ*β*‖Va‖*‖Vb‖ := by
    have hh := abs_modelAdjointDefectCoarseL_form_le_half d y hFrame Da Db
    simpa only [hHa,hHb] using hh
  have hx2 : |⟪I10 Da,J M0⟫_ℝ| ≤ CZ1*β^2*‖Va‖*‖H y‖ :=
    (abs_real_inner_le_norm _ _).trans ((mul_le_mul hDaN hJM (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring))
  have hx3 : |⟪M00,Z Db⟫_ℝ| ≤ CA*β*‖H y‖*‖Vb‖ := by
    rw [hM00]
    have hh := abs_modelAdjointDefectCoarseL_mass_first_bound Q hQ d y hFrame (H y) Db
    simpa only [hHb] using hh
  have hx4 : |⟪M00,J M0⟫_ℝ| ≤ CZ1*β^2*‖H y‖^2 :=
    (abs_real_inner_le_norm _ _).trans ((mul_le_mul hM00N hJM (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring))
  have hh := scalar_model_defect_four_form_bound (q y) (fderiv ℝ q y (axis a))
    ⟪I10 Da,Z Db⟫_ℝ ⟪I10 Da,J M0⟫_ℝ ⟪M00,Z Db⟫_ℝ ⟪M00,J M0⟫_ℝ
    mu A A1 CZ CZ1 CA ε β ‖Va‖ ‖Vb‖ ‖H y‖ hmu hA hA1 hCZ hCZ1 hCA hε hβ
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hq hdq hx1 hx2 hx3 hx4
  have hExpr : scalarModelDefectSecondRemainder d q U (axis a) (axis b) y=
      -q y*(⟪I10 Da,Z Db⟫_ℝ+⟪I10 Da,J M0⟫_ℝ)-
        fderiv ℝ q y (axis a)*(⟪M00,Z Db⟫_ℝ+⟪M00,J M0⟫_ℝ) := by
    simp only [scalarModelDefectSecondRemainder,modelAdjointDefectDerivativeSection,
      inner_add_right,I10,I21,M00,M0,Da,Db,Z,J]
    ring
  rw [hExpr]
  simpa only [scalarModelDefectSecondBudget,halfCovariantDirectionEnergy,CZ,CZ1,CA,Va,Vb,H,β] using hh

end ShrinkingSpheres
