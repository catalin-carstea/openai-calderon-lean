module

public import Proof.CalderonN.AngularRadialWeight
public import Proof.CalderonN.ActualAngularCoefficientJets
public import Proof.CalderonN.SmoothBallReciprocal

import Proof.CalderonN.ZonalProjection
import Mathlib.Tactic

/-! Gauss' radial weight and its angular derivative have matching
affine terms and local C1 Taylor remainders. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option maxHeartbeats 5800000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_angular_radial_weights (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let ell := firstDensityCenterLinear d y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      ∀ A : X dim → Mat dim, ContDiff ℝ ∞ A → EqOn A a (ball (0 : X dim) (5/4)) →
        (∀ z ∈ closedBall (0 : X dim) 1, (A z).PosDef) ∧
        ∃ W D WI : SmoothData dim,
          (∀ u : SmoothData dim, EqOn (smoothBallConormal A u.1)
            (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim)) ∧
          (∀ z, W.1 z = 1+D.1 z) ∧
          (∀ z ∈ closedBall (0 : X dim) 1,
            WI.1 z*W.1 z = 1 ∧ |WI.1 z| ≤ C ∧ ‖fderiv ℝ WI.1 z‖ ≤ C ∧
            |D.1 z| ≤ C*r ∧ ‖fderiv ℝ D.1 z‖ ≤ C*r) ∧
          ∀ i j : Fin dim,
            let ellθ := ell.comp (ballRotationGeneratorL i j)
            ‖ellθ‖ ≤ C ∧ ∃ V E : SmoothData dim,
              EqOn V.1 (sphereRotationDerivative i j W.1) (standardSphere dim) ∧
              (∀ z, V.1 z = r*ellθ z+E.1 z) ∧
              ∀ z ∈ closedBall (0 : X dim) 1,
                |V.1 z| ≤ C*r ∧ ‖fderiv ℝ V.1 z‖ ≤ C*r ∧
                |E.1 z| ≤ C*r^2 ∧ ‖fderiv ℝ E.1 z‖ ≤ C*r^2 := by
  obtain ⟨η,C,hη,hC,hW⟩ := uniform_actual_radial_weight_remainder (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηθ,Pθ,Qθ,hηθ,hPθ,hQθ,hθ⟩ := uniform_actual_angular_coefficient_jets (Y := Y)
    hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηN,hηN,hN⟩ := uniform_normal_control_on_disk (Y := Y) hΩ (by omega : 2 ≤ m)
    K ρ c₀ M Cj hK hρ 1 zero_le_one
  let Q := 3*(dim : ℝ)^2*Qθ
  let B := 2+8*C+2*Pθ+Q
  let τ := min (min η ηθ) (min ηN (1/(4*(C+1))))
  have hB : 0 ≤ B := by dsimp only [B,Q]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  refine ⟨τ,B,lt_min (lt_min hη hηθ) (lt_min hηN (by positivity)),hB,?_⟩
  intro floor hf ε hε hs d hd y hy
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let ell := firstDensityCenterLinear d y
  intro A hA hAa
  have hJ := (hθ floor hf ε hε
    (hs.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy).2 A hA hAa
  refine ⟨hJ.1,?_⟩
  obtain ⟨hEll,R,hWr,hR⟩ := hW floor hf ε hε
    (hs.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 y hy).2
  have hrB : r*(4*(C+1)) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 4*(C+1))).mp
    (hrε.trans (hs.trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hr1 : r ≤ 1 := by nlinarith only [hrB,mul_nonneg hr.le hC]
  have hrC : 2*C*r ≤ 1/2 := by nlinarith only [hrB,hr]
  let D : SmoothData dim := ⟨fun z => r*ell z+R.1 z,(contDiff_const.mul ell.contDiff).add R.2⟩
  let W : SmoothData dim := ⟨fun z => 1+D.1 z,contDiff_const.add D.2⟩
  have hSum (ℓ : X dim →L[ℝ] ℝ) (E : SmoothData dim) (P J : ℝ)
      (hPJ : 0 ≤ P ∧ 0 ≤ J) (hℓ : ‖ℓ‖ ≤ P)
      (hE : ∀ z ∈ closedBall (0 : X dim) 1, |E.1 z| ≤ J*r^2 ∧ ‖fderiv ℝ E.1 z‖ ≤ J*r^2) :
      ∀ z ∈ closedBall (0 : X dim) 1,
        |r*ℓ z+E.1 z| ≤ (P+J)*r ∧ ‖fderiv ℝ (fun x => r*ℓ x+E.1 x) z‖ ≤ (P+J)*r := by
    intro z hz
    have hNum : r*P+J*r^2 ≤ (P+J)*r := by
      have hh := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hPJ.2 hr.le)
      nlinarith only [hh]
    have hBnd : |ℓ z| ≤ P := (ℓ.le_opNorm z).trans
      ((mul_le_mul hℓ (mem_closedBall_zero_iff.mp hz) (norm_nonneg _) hPJ.1).trans_eq (mul_one _))
    refine ⟨((abs_add_le _ _).trans (add_le_add ?_ (hE z hz).1)).trans hNum,?_⟩
    · rw [abs_mul,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hBnd hr.le
    · have hD : fderiv ℝ (fun x => r*ℓ x) z = r • ℓ := by
        change fderiv ℝ (r • ⇑ℓ) z = _
        have h := fderiv_const_smul (ℓ.differentiable z) r
        change fderiv ℝ (r • ⇑ℓ) z = _ at h
        rw [h,ContinuousLinearMap.fderiv]
      have hadd := fderiv_fun_add ((differentiableAt_const r).mul (ℓ.differentiable z))
        (E.2.differentiable (by simp) z)
      change fderiv ℝ (fun x => r*ℓ x+E.1 x) z = fderiv ℝ (fun x => r*ℓ x) z+_ at hadd
      rw [hadd,hD]
      exact ((norm_add_le _ _).trans (add_le_add (by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
        exact mul_le_mul_of_nonneg_left hℓ hr.le) (hE z hz).2)).trans hNum
  have hD (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) :
      |D.1 z| ≤ 2*C*r ∧ ‖fderiv ℝ D.1 z‖ ≤ 2*C*r := by
    have h := hSum ell R C C ⟨hC,hC⟩ hEll hR z hz
    change |D.1 z| ≤ (C+C)*r ∧ ‖fderiv ℝ D.1 z‖ ≤ (C+C)*r at h
    simpa only [← two_mul] using h
  have hWpos (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) : (1/2 : ℝ) ≤ W.1 z := by
    change (1/2 : ℝ) ≤ 1+D.1 z
    linarith only [(abs_le.mp (hD z hz).1).1,hrC]
  have hWder (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) : ‖fderiv ℝ W.1 z‖ ≤ 2*C*r := by
    change ‖fderiv ℝ (fun x => 1+D.1 x) z‖ ≤ _
    rw [fderiv_fun_add (differentiableAt_const (1 : ℝ)) (D.2.differentiable (by simp) z),
      fderiv_fun_const,Pi.zero_apply,zero_add]
    exact (hD z hz).2
  obtain ⟨WI,hWI,hWIn⟩ := exists_smoothBall_reciprocal W (by positivity) hWpos hWder
  have hSphW (z : X dim) (hz : z ∈ standardSphere dim) : W.1 z = firstNormalRadialWeight d y r z := by
    change 1+(r*ell z+R.1 z) = _
    rw [← add_assoc]
    exact hWr hz
  have hNear (z : X dim) (hz : z ∈ standardSphere dim) :
      r • frameVector d.frame y z ∈ interior (disk d.γ y (max ρ (d.radius y))) := by
    have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
    have hw := frameVector_mem_disk d.γ d.frame y z 1 hFrame (sphere_subset_closedBall hz)
    exact (hN floor hf ε hε (hs.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy _ hw).1.1
  have hAF (z : X dim) (hz : z ∈ standardSphere dim) : A z = a z :=
    hAa (closedBall_subset_ball (by norm_num : (1 : ℝ) < 5/4) (sphere_subset_closedBall hz))
  have hCFlux (u : SmoothData dim) : EqOn (smoothBallConormal A u.1)
      (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim) := by
    intro z hz
    have hF : smoothBallFlux A u.1 z = smoothBallFlux a u.1 z := by
      ext k
      simp only [smoothBallFlux_apply,hAF z hz]
    change smoothBallConormal A u.1 z = W.1 z*fderiv ℝ u.1 z z
    rw [smoothBallConormal,hF,hSphW z hz]
    exact hd.inner_actualNormalFlux_radial_row hn hΩ (zero_lt_one.trans_le hK) hy hr.ne' z (hNear z hz) u.1
  have hSQ : EqOn (scalarQuadraticCoefficient A) W.1 (standardSphere dim) := by
    intro z hz
    have hNrm : ∑ k : Fin dim, z k*z k = 1 := by
      simpa only [pow_two] using unitSphere_sum_sq ⟨z,hz⟩
    rw [scalarQuadraticCoefficient,Finset.sum_comm,hSphW z hz]
    have hRow (l : Fin dim) : (∑ k, z k*A z k l*z l) =
        firstNormalRadialWeight d y r z*(z l*z l) := by
      rw [← Finset.sum_mul,hAF z hz,
        hd.actualNormalCoeff_radial_row hn hΩ (zero_lt_one.trans_le hK) hy hr.ne' z (hNear z hz) l]
      ring
    simp_rw [hRow,← Finset.mul_sum,hNrm,mul_one]
  refine ⟨W,D,WI,hCFlux,fun _ => rfl,?_,?_⟩
  · intro z hz
    have hb := hWIn z hz
    have hDz := hD z hz
    have he : WI.1 z*W.1 z = 1 := by
      rw [hWI hz,inv_mul_cancel₀ (by linarith only [hWpos z hz])]
    refine ⟨he,hb.1.trans ?_,hb.2.trans ?_,hDz.1.trans ?_,hDz.2.trans ?_⟩
    · dsimp only [B]; linarith only [hC,hPθ,hQ]
    · dsimp only [B]; nlinarith only [hQ,hPθ,mul_le_mul_of_nonneg_left hr1 hC]
    · exact mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith only [hC,hPθ,hQ]) hr.le
    · exact mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith only [hC,hPθ,hQ]) hr.le
  intro i j
  let ellθ := ell.comp (ballRotationGeneratorL i j)
  let Aθ := ballRotationCoefficient i j A
  let L (z : X dim) := r • (ellθ z • (1 : Mat dim))
  let F := Aθ-L
  let hF : ContDiff ℝ ∞ F := (contDiff_ballRotationCoefficient i j hA).sub
    ((ellθ.contDiff.smul contDiff_const).const_smul r)
  let E : SmoothData dim := ⟨scalarQuadraticCoefficient F,contDiff_scalarQuadraticCoefficient hF⟩
  let V : SmoothData dim := ⟨fun z => r*ellθ z+E.1 z,(contDiff_const.mul ellθ.contDiff).add E.2⟩
  have hE (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) : |E.1 z| ≤ Q*r^2 ∧ ‖fderiv ℝ E.1 z‖ ≤ Q*r^2 := by
    have hNrm := mem_closedBall_zero_iff.mp hz
    have hBnd : ‖F z‖ ≤ Qθ*r^2 ∧ ‖fderiv ℝ F z‖ ≤ Qθ*r^2 := (hJ.2 i j).2 z hz
    have hq : 0 ≤ Qθ*r^2 := by positivity
    refine ⟨(abs_scalarQuadraticCoefficient_le (A := F) hNrm (Qθ*r^2) hq hBnd.1).trans ?_,
      (norm_fderiv_scalarQuadraticCoefficient_le hF hNrm (Qθ*r^2) hq hBnd.1 hBnd.2).trans_eq ?_⟩
    · dsimp only [Q]; nlinarith only [show 0 ≤ (dim : ℝ)^2*(Qθ*r^2) by positivity]
    · dsimp only [Q]; ring
  have hℓθ : ‖ellθ‖ ≤ 2*Pθ := (hJ.2 i j).1
  have hBound : 2*Pθ+Q ≤ B := by dsimp only [B]; linarith only [hC]
  refine ⟨hℓθ.trans (by linarith only [hBound,hQ]),V,E,?_,fun _ => rfl,?_⟩
  · have hRot := EqOn.sphereRotationDerivative hSQ (contDiff_scalarQuadraticCoefficient hA) W.2 i j
    rw [sphereRotationDerivative_scalarQuadraticCoefficient i j hA] at hRot
    intro z hz
    change r*ellθ z+scalarQuadraticCoefficient F z = _
    rw [scalarQuadraticCoefficient_sub,Pi.sub_apply,scalarQuadraticCoefficient_smul_linear_at_sphere ellθ r hz]
    rw [← hRot hz]
    ring
  · intro z hz
    have hV := hSum ellθ E (2*Pθ) Q ⟨by positivity,hQ⟩ hℓθ hE z hz
    exact ⟨hV.1.trans (mul_le_mul_of_nonneg_right hBound hr.le),
      hV.2.trans (mul_le_mul_of_nonneg_right hBound hr.le),
      (hE z hz).1.trans (mul_le_mul_of_nonneg_right (by linarith only [hBound,hPθ]) (sq_nonneg _)),
      (hE z hz).2.trans (mul_le_mul_of_nonneg_right (by linarith only [hBound,hPθ]) (sq_nonneg _))⟩

end CalderonN
