import Proof.FiniteMatrixNormBound
import Proof.PrincipalCovariantNormalForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def principalCovariantPotentialL (d : Data)
    (S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (y : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
    ((firstFrameAdjointCovariantJetL d y (d.frame y i) j).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))+S i j y))

lemma principalCovariantPotentialL_actual (d : Data)
    (S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (U : X → SphereSobolev 2) (y : X) :
    principalCovariantPotentialL d S y (sphereSobolevInclusionL 2 1 (by norm_num) (U y))=
      principalCovariantRemainderSection d S U y := by
  simp only [principalCovariantPotentialL,principalCovariantRemainderSection,
    _root_.smul_apply,_root_.sum_apply,_root_.add_apply,ContinuousLinearMap.comp_apply]

lemma PhysicalPrincipalData.norm_principalCovariantPotentialL_small {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε CF CT : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (D : PhysicalPrincipalData Y d CF CT) (hCT : 0 ≤ CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) :
    ‖principalCovariantPotentialL d D.tensor y‖ ≤ 81*(K+1)*K^2*
      (firstFrameAdjointCovariantBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)+CT)*ε := by
  let B := 9*(K+1)*K^2
  let CJ := firstFrameAdjointCovariantBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
  let F := fun i j => (firstFrameAdjointCovariantJetL d y (d.frame y i) j).comp
    (sphereSobolevInclusionL 1 0 (by norm_num))+D.tensor i j y
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hCJ : 0 ≤ CJ := by dsimp only [CJ,firstFrameAdjointCovariantBudget,firstRadialCovariantBudget];positivity
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hRad := radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2
  have hrβ : d.radius y*beta d.γ d.radius y ≤ 1 := hRad.2.1.trans ((div_le_self hε hf).trans hε1)
  have hT (i j : I) : ‖D.tensor i j y‖ ≤ CT := (D.tensor_bound y hy i j).trans
    (by calc
      _ = CT*(d.radius y*beta d.γ d.radius y) := by ring
      _ ≤ CT*1 := mul_le_mul_of_nonneg_left hrβ hCT
      _ = CT := mul_one CT)
  have hF (i j : I) : ‖F i j‖ ≤ CJ+CT := by
    have hJ := hd.norm_firstFrameAdjointCovariantJetL_le hY hΩ hm hK hf hε hε1 hy i j
    have hComp : ‖(firstFrameAdjointCovariantJetL d y (d.frame y i) j).comp
        (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul hJ (norm_sphereSobolevInclusionL_le _ _ _)
          (norm_nonneg (sphereSobolevInclusionL 1 0 (by norm_num))) hCJ).trans_eq (mul_one _))
    change ‖(firstFrameAdjointCovariantJetL d y (d.frame y i) j).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))+D.tensor i j y‖ ≤ CJ+CT
    exact (norm_add_le ((firstFrameAdjointCovariantJetL d y (d.frame y i) j).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))) (D.tensor i j y)).trans (add_le_add hComp (hT i j))
  have hSum := norm_weighted_matrix_three_le
    (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)) F B (CJ+CT) hB
    (fun i j => (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).2.1) hF
  change ‖d.radius y • (∑ i : I,∑ j : I,
    frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j • F i j)‖ ≤ _
  calc
    _ ≤ d.radius y*‖∑ i : I,∑ j : I,
        frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j • F i j‖ := by
      simpa only [Real.norm_eq_abs,abs_of_pos hr] using
        ContinuousLinearMap.opNorm_smul_le (d.radius y) (∑ i : I,∑ j : I,
          frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j • F i j)
    _ ≤ d.radius y*(9*B*(CJ+CT)) := mul_le_mul_of_nonneg_left hSum hr.le
    _ = (9*B*(CJ+CT))*d.radius y := by ring
    _ ≤ (9*B*(CJ+CT))*ε := mul_le_mul_of_nonneg_left hRad.2.2 (by positivity)
    _ = _ := by dsimp only [B,CJ];ring
end ShrinkingSpheres
