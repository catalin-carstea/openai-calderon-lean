import Proof.PhysicalPrincipalResidual
import Proof.ActualCorrectionProductBudget
import Proof.ActualRadialTaylorEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME order-zero first correction used at a genuine lower endpoint. -/
def firstFrameLowerCorrectionL (d : Data) (y : X) (i : I) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i).comp
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))

lemma firstFrameLowerCorrectionL_actual (d : Data) (y : X) (i : I) (v : SphereSobolev 1) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (firstFrameCorrectionCoarseFamily d i y v)=
      firstFrameLowerCorrectionL d y i (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v) := by
  have h := firstFrameAdjointCorrectionAtL_inclusion 0 (-(1/2:ℝ)) (by norm_num) d y i
    (sphereSobolevInclusionL 1 0 (by norm_num) v)
  simpa only [firstFrameCorrectionCoarseFamily,firstFrameLowerCorrectionL,
    firstFrameAdjointCorrectionAtL_zero,ContinuousLinearMap.comp_apply,
    sphereSobolevInclusionL_trans_apply] using h

namespace ActualFrameErrorEndpointPair
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {CE : ℝ}

/-- Exact coefficient of the first base derivative. Keeping q_ij+q_ji
also makes the physical identification independent of a symmetry rewrite. -/
def principalFirstDerivativeHalfL (E : ActualFrameErrorEndpointPair Y d A G CE) (y : X) (j : I) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  d.radius y • (∑ i : I,
    (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i) •
      (firstFrameLowerCorrectionL d y i+E.low i y))

lemma principal_first_remainder_actual (E : ActualFrameErrorEndpointPair Y d A G CE)
    (U : X → SphereSobolev 2) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (principalFirstRemainderSection d A G U y)=
      ∑ j : I,E.principalFirstDerivativeHalfL y j
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
          (highSectionCovariantDerivative d U y (d.frame y j))) := by
  have hE (i : I) (v : SphereSobolev 1) :
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (actualFrameFirstAdjointErrorFamily d A G i y v)=
      E.low i y (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v) :=
    DFunLike.congr_fun (E.low_coarse i y hy) v
  have hCollect {W : Type} [AddCommGroup W] [Module ℝ W]
      (r : ℝ) (q : I → I → ℝ) (C : I → I → W) :
      r • (∑ i : I,∑ j : I,q i j • (C i j+C j i))=
        ∑ j : I,r • (∑ i : I,(q i j+q j i) • C i j) := by
    have hSwap : (∑ i : I,∑ j : I,q i j • C i j)=∑ j : I,∑ i : I,q i j • C i j := Finset.sum_comm
    simp only [smul_add,add_smul,Finset.sum_add_distrib,← Finset.smul_sum]
    rw [hSwap]
  let C := fun i j => (firstFrameLowerCorrectionL d y i+E.low i y)
    (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
      (highSectionCovariantDerivative d U y (d.frame y j)))
  have h := hCollect (d.radius y) (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)) C
  simpa only [principalFirstRemainderSection,principalFirstDerivativeHalfL,C,
    map_smul,map_sum,map_add,firstFrameLowerCorrectionL_actual,hE,
    _root_.sum_apply,_root_.smul_apply,_root_.add_apply] using h

lemma norm_principalFirstDerivativeHalfL_small {Ω : Set X} (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (E : ActualFrameErrorEndpointPair Y d A G CE) (hCE : 0 ≤ CE)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (j : I) :
    ‖E.principalFirstDerivativeHalfL y j‖ ≤
      54*(K+1)*K^2*(firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)+CE)*ε/beta d.γ d.radius y := by
  let B := 9*(K+1)*K^2
  let C0 := firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)
  let C := C0+CE
  let β := beta d.γ d.radius y
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hC0 : 0 ≤ C0 := firstCorrectionGradeBound_nonneg _ _ _
  have hC : 0 ≤ C := add_nonneg hC0 hCE
  have hr : 0 < d.radius y := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hRadius := radius_bounds (d.radius y) β floor ε hr.le hf (hd.2.2.2.2.1.2 y hy).2.1
    (hd.2.2.2.2.2 y hy).2
  have hr1 : d.radius y ≤ 1 := hRadius.2.2.trans hε1
  have hrβ : d.radius y*β ≤ ε := hRadius.2.1.trans (div_le_self hε hf)
  have hF (i : I) : ‖firstFrameLowerCorrectionL d y i‖ ≤ C0 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 _ hy i)
        (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _) hC0).trans_eq (mul_one _))
  have hLow (i : I) : ‖firstFrameLowerCorrectionL d y i+E.low i y‖ ≤ C := by
    apply (norm_add_le _ _).trans
    exact (add_le_add (hF i) ((E.low_bound i y hy).trans
      ((mul_le_mul_of_nonneg_left hr1 hCE).trans_eq (mul_one _))))
  have hQ (i k : I) : |frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i k| ≤ B :=
    (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i k).2.1
  have hSum : ‖∑ i : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i) • (firstFrameLowerCorrectionL d y i+E.low i y)‖ ≤ 6*B*C := by
    have h := norm_weighted_sum_three_le
      (fun i => frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
        frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i)
      (fun i => firstFrameLowerCorrectionL d y i+E.low i y) (2*B) C (by positivity)
      (fun i => (abs_add_le _ _).trans ((add_le_add (hQ i j) (hQ j i)).trans_eq (by ring))) hLow
    exact h.trans_eq (by ring)
  have hNorm : ‖E.principalFirstDerivativeHalfL y j‖ ≤ 6*B*C*d.radius y := by
    rw [principalFirstDerivativeHalfL,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hSum hr.le).trans_eq (by ring)
  apply (le_div_iff₀ hβ).2
  calc
    _ ≤ (6*B*C*d.radius y)*β := mul_le_mul_of_nonneg_right hNorm hβ.le
    _ = (6*B*C)*(d.radius y*β) := by ring
    _ ≤ (6*B*C)*ε := mul_le_mul_of_nonneg_left hrβ (by positivity)
    _ = _ := by dsimp only [B,C,C0];ring

lemma principalFirstDerivativeHalfL_smooth {Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (E : ActualFrameErrorEndpointPair Y d A G CE)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (j : I) :
    ContDiffOn ℝ ∞ (fun y => E.principalFirstDerivativeHalfL y j) Y := by
  apply hd.2.2.2.2.1.1.smul
  apply ContDiffOn.sum
  intro i _
  apply ((hd.contDiffOn_framePrincipalCoefficient (fun x hx => hd.2.1.center_mem hx) hK i j).add
    (hd.contDiffOn_framePrincipalCoefficient (fun x hx => hd.2.1.center_mem hx) hK j i)).smul
  exact ((hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK (-(1/2:ℝ)) i).clm_comp
    (contDiffOn_const (c:=sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))).add (E.low_smooth i)
end ActualFrameErrorEndpointPair
end ShrinkingSpheres
