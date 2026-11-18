import Proof.ScaledFrameLogRadiusSharp
import Proof.PhysicalPrincipalResidual
import Proof.FrameErrorMatrixRaisingCross
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def principalModelFirstDerivativeL (d : Data) (y : X) (j : I) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (∑ i : I,((frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
    frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i)*scaledFrameLogRadius d.radius d.frame i y) • sphereSobolevDegreeL)+
  (2:ℝ) • (∑ i : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-(if i=j then 1 else 0)) • flatOneRaisingL i)

def principalModelFirstDerivativeHalfL (d : Data) (y : X) (j : I) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (∑ i : I,((frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
    frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i)*scaledFrameLogRadius d.radius d.frame i y) • sphereSobolevShiftedDegreeL (1/2:ℝ))+
  (2:ℝ) • (∑ i : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-(if i=j then 1 else 0)) • flatHalfRaisingL i)

lemma principalModelFirstDerivativeHalfL_actual (d : Data) (y : X) (j : I) (v : SphereSobolev 1) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (principalModelFirstDerivativeL d y j v)=
      principalModelFirstDerivativeHalfL d y j (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v) := by
  simp only [principalModelFirstDerivativeL,principalModelFirstDerivativeHalfL,
    _root_.add_apply,_root_.sum_apply,_root_.smul_apply,map_add,map_sum,map_smul,
    sphereSobolevDegreeL_half,flatOneRaisingL_half]

lemma Admissible.norm_principalModelFirstDerivativeHalfL_small {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (j : I) :
    ‖principalModelFirstDerivativeHalfL d y j‖ ≤
      (108*(K+1)*K^2+540*K^2*radialDriftSobolevBound (-(1/2:ℝ)))*ε/beta d.γ d.radius y := by
  let B := 9*(K+1)*K^2
  let N := 10*radialDriftSobolevBound (-(1/2:ℝ))
  let β := beta d.γ d.radius y
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hN : 0 ≤ N := mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hT (i : I) : |scaledFrameLogRadius d.radius d.frame i y| ≤ ε/β :=
    hd.scaled_frame_logRadius_beta_small hf hy i
  have hQ (i k : I) : |q i k| ≤ B := (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i k).2.1
  have hQS (i : I) : |q i j+q j i| ≤ 2*B :=
    (abs_add_le _ _).trans ((add_le_add (hQ i j) (hQ j i)).trans_eq (by ring))
  have hQT (i : I) : |(q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y| ≤ 2*B*(ε/β) := by
    rw [abs_mul]
    exact mul_le_mul (hQS i) (hT i) (abs_nonneg _) (by positivity)
  have hD : ‖∑ i : I,((q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y) •
      sphereSobolevShiftedDegreeL (1/2:ℝ)‖ ≤ 12*B*ε/β := by
    have h := norm_weighted_sum_three_le (fun i => (q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y)
      (fun _i : I => sphereSobolevShiftedDegreeL (1/2:ℝ)) (2*B*(ε/β)) 2 (by positivity) hQT
      (fun _i => norm_sphereSobolevShiftedDegreeL_le_two _)
    exact h.trans_eq (by ring)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrβ : d.radius y*β ≤ 1 := ((radius_bounds (d.radius y) β floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.1).trans ((div_le_self hε hf).trans hε1)
  have hDiff (i : I) : |q i j-(if i=j then 1 else 0)| ≤ 9*K^2*ε/β := by
    apply (le_div_iff₀ hβ).2
    calc
      _ ≤ (9*K^2*ε*d.radius y)*β := mul_le_mul_of_nonneg_right
        (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).1 hβ.le
      _ = (9*K^2*ε)*(d.radius y*β) := by ring
      _ ≤ (9*K^2*ε)*1 := mul_le_mul_of_nonneg_left hrβ (by positivity)
      _ = _ := mul_one _
  have hA : ‖(2:ℝ) • (∑ i : I,(q i j-(if i=j then 1 else 0)) • flatHalfRaisingL i)‖ ≤ 54*K^2*N*ε/β := by
    have h := norm_weighted_sum_three_le (fun i => q i j-(if i=j then 1 else 0)) flatHalfRaisingL
      (9*K^2*ε/β) N (by positivity) hDiff norm_flatHalfRaisingL_le
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
  exact (norm_add_le _ _).trans ((add_le_add hD hA).trans_eq (by dsimp only [B,N];ring))

lemma Admissible.contDiffOn_principalModelFirstDerivativeHalfL {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (j : I) :
    ContDiffOn ℝ ∞ (fun y => principalModelFirstDerivativeHalfL d y j) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hQ := fun i k => hd.contDiffOn_framePrincipalCoefficient hSub hK i k
  have hT := fun i => contDiffOn_scaledFrameLogRadius hY hd.2.2.2.2.1.1
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
    (fun k => (hd.1.2.2.2.2.2.2.1 k).mono hSub) i
  have hDegree : ContDiffOn ℝ ∞ (fun y => ∑ i : I,
      ((frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
        frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i)*scaledFrameLogRadius d.radius d.frame i y) •
        sphereSobolevShiftedDegreeL (1/2:ℝ)) Y := by
    apply ContDiffOn.sum
    intro i _
    exact (((hQ i j).add (hQ j i)).mul (hT i)).smul contDiffOn_const
  have hRaising : ContDiffOn ℝ ∞ (fun y => ∑ i : I,
      (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-(if i=j then 1 else 0)) • flatHalfRaisingL i) Y := by
    apply ContDiffOn.sum
    intro i _
    exact ((hQ i j).sub contDiffOn_const).smul contDiffOn_const
  exact hDegree.add (hRaising.const_smul (2:ℝ))

def principalModelPotentialL (d : Data) (y : X) : SphereSobolev 2 →L[ℝ] SphereSobolev 0 :=
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let f := fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k)
  d.radius y • (∑ i : I,∑ j : I,q i j •
    ((hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y j)) •
      sphereSobolevDegreeL.comp (sphereSobolevInclusionL 2 1 (by norm_num))+
      (f i*f j) • sphereSobolevDegreeL.comp (sphereSobolevShiftedDegreeL 2)))+
    (2:ℝ) • (∑ i : I,∑ j : I,((q i j-(if i=j then 1 else 0))*f j) •
      (flatOneRaisingL i).comp (sphereSobolevShiftedDegreeL 2))

/-- Exact covariant base-order normal form of the model and mixed-h terms.
The only second-base coefficient is the real scalar rQ. -/
lemma principal_model_base_collection (d : Data) (U : X → SphereSobolev 2) (y : X) :
    let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
    d.radius y • (∑ i : I,∑ j : I,q i j • modelPlusTensorSection d U y i j)+
      (2:ℝ) • (∑ i : I,∑ j : I,(q i j-(if i=j then 1 else 0)) • flatOneRaisingL i (highSectionModelPlus d U y j))=
      d.radius y • (∑ i : I,∑ j : I,q i j • highSectionCovariantHessian d U y i j)+
      (∑ j : I,principalModelFirstDerivativeL d y j (highSectionCovariantDerivative d U y (d.frame y j)))+
      principalModelPotentialL d y (U y) := by
  dsimp only
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let f := fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k)
  let D := fun k => highSectionCovariantDerivative d U y (d.frame y k)
  have hSwap : (∑ i : I,∑ j : I,q i j • (f i • sphereSobolevDegreeL (D j)))=
      ∑ j : I,∑ i : I,q i j • (f i • sphereSobolevDegreeL (D j)) := Finset.sum_comm
  simp only [principalModelFirstDerivativeL,principalModelPotentialL,modelPlusTensorSection,highSectionModelPlus,
    _root_.add_apply,_root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    map_add,map_smul,smul_add,Finset.sum_add_distrib]
  dsimp only [q,f,D] at hSwap
  simp only [smul_smul,scaledFrameLogRadius]
  simp only [smul_smul] at hSwap
  rw [hSwap]
  simp only [Fin.sum_univ_three]
  module
end ShrinkingSpheres
