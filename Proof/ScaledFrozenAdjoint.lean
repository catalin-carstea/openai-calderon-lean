import Proof.BoundaryCoefficientNorms
import Proof.ScaledLogRadiusBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

theorem Admissible.norm_fixedCenterBoundaryAdjointL_le {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε CD : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) {y : X} (hy : y ∈ Y)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (hDa : ‖Da‖ ≤ CD) (a : X) :
    ‖boundaryGradientAdjointL (fixedCenterCoefficient Q d.γ d.frame y a) Da‖ ≤
      (73*boundaryTangentialAdjointBudget+438*CD)*(9*|M 0| *K)*‖a‖ := by
  let C0 := 9*|M 0| *K
  have hC0 : 0 ≤ C0 := by dsimp only [C0];positivity
  have hCenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
  have hL (j : I) : ‖frameCoordinateLinear d.γ d.frame y j‖ ≤ C0 :=
    hd.1.1.norm_frameCoordinateLinear_le hK hCenter d.frame hFrame |M 0| (abs_nonneg _)
      (fun i l => (hd.1.reference_entry_bound hCenter i l).trans (le_abs_self _)) j
  have hP (j : I) : LocalC1Bound (coefficientValue 2 (fixedCenterCoefficient Q d.γ d.frame y a j)) (C0*‖a‖) := by
    have hLocal := constantBoundaryCoefficient_local_C1 Q hQ (frameCoordinateLinear d.γ d.frame y j a)
    have hValue : |frameCoordinateLinear d.γ d.frame y j a| ≤ C0*‖a‖ :=
      ((frameCoordinateLinear d.γ d.frame y j).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hL j) (norm_nonneg a))
    intro z hz
    exact ⟨(hLocal z hz).1.trans hValue,(hLocal z hz).2.trans hValue⟩
  have hFactor : 73*boundaryTangentialAdjointBudget+438*‖Da‖ ≤
      73*boundaryTangentialAdjointBudget+438*CD :=
    add_le_add (le_refl (73*boundaryTangentialAdjointBudget))
      (mul_le_mul_of_nonneg_left hDa (by norm_num : (0:ℝ) ≤ 438))
  have hFinal := mul_le_mul_of_nonneg_right hFactor (mul_nonneg hC0 (norm_nonneg a))
  exact (norm_boundaryGradientAdjointL_local_C1 _ Da (C0*‖a‖) (by positivity) hP).trans
    (hFinal.trans_eq (by dsimp only [C0];ring))

theorem norm_scaled_movingBoundaryAdjointL_le (P C : I → SmoothCoefficientJets 2)
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (r b CG CD CE K : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hCE : 0 ≤ CE) (hK : 0 ≤ K)
    (hP : ‖boundaryGradientAdjointL P Da‖ ≤ CG) (hDa : ‖Da‖ ≤ CD)
    (hC : ‖r⁻¹ • boundaryGradientAdjointL C Da‖ ≤ CE*r) (hBeta : r*|b| ≤ K) :
    ‖r • movingBoundaryHorizontalAdjointL P C Da r b‖ ≤ CG+K*CD+CE := by
  let E := r⁻¹ • boundaryGradientAdjointL C Da
  have hEq : r • movingBoundaryHorizontalAdjointL P C Da r b =
      boundaryGradientAdjointL P Da+(r*b) • Da+r • E := by
    change r • ((r⁻¹ • boundaryGradientAdjointL P Da+b • Da)+E) = _
    simp only [smul_add,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hMid : ‖(r*b) • Da‖ ≤ K*CD := by
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos hr]
    exact mul_le_mul hBeta hDa (norm_nonneg _) hK
  have hEnd : ‖r • E‖ ≤ CE := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    have hrSq : r^2 ≤ 1 := by nlinarith only [hr,hr1]
    calc
      r*‖E‖ ≤ r*(CE*r) := mul_le_mul_of_nonneg_left hC hr.le
      _ = CE*r^2 := by ring
      _ ≤ CE*1 := mul_le_mul_of_nonneg_left hrSq hCE
      _ = CE := mul_one CE
  rw [hEq]
  exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add hP hMid)) hEnd))

/-- The actual frozen adjoint, multiplied by its radius, has a common H1-to-L2
    bound on every admitted profile. This also supplies the true component realization. -/
theorem uniform_scaled_frozen_adjoint {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CA : ℝ,0 < η ∧ 0 ≤ CA ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i : I,
      ∃ S : SphereSobolev 1 →L[ℝ] SphereSobolev 0,‖S‖ ≤ CA ∧
        ∀ φ : Field,smoothNear φ (bundle Y d.γ) → ∀ L : ℂ →L[ℝ] ℝ,∀ v : SphereSobolev 1,
        ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
            fun w : UnitSphere => L (φ (y,frameVector d.frame y w.val))) →
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (S v) =ᵐ[sphereProbability]
          fun w : UnitSphere => d.radius y*L (adjointField d.adjoint i φ (y,frameVector d.frame y w.val)) := by
  have hTheorem := uniform_frozen_trace_adjoint_realization hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηA,CD,CB,CJ,CE,Q,hηA,hCD,hCB,hCJ,hCE,hQ,hProduce⟩ := hTheorem
  let CG := (73*boundaryTangentialAdjointBudget+438*CD)*(9*|M 0| *K)
  let CA := CG+K*CD+CE
  have hCG : 0 ≤ CG := by have := boundaryTangentialAdjointBudget_nonneg;dsimp only [CG];positivity
  have hCA : 0 ≤ CA := by dsimp only [CA];positivity
  refine ⟨min ηA 1,CA,lt_min hηA zero_lt_one,hCA,?_⟩
  intro floor hf ε hε hSmall d hd y hy i
  have hHere := hProduce floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨Da,B,hDa,hB,hTaylor,hDirections⟩ := hHere
  have hIHere := hDirections i
  obtain ⟨C,hCRep,hC,hReal⟩ := hIHere
  let r := d.radius y
  let b := fderiv ℝ (fun x => Real.log (d.radius x)) y (axis i)
  let P := fixedCenterCoefficient Q d.γ d.frame y (axis i)
  let T := movingBoundaryHorizontalAdjointL P C Da r b
  let S := r • T
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans (min_le_right _ _))
  have hP := hd.norm_fixedCenterBoundaryAdjointL_le hK hy Q hQ Da hDa (axis i)
  simp only [norm_axis,mul_one] at hP
  have hBeta := hd.scaled_coord_logRadius_bound hK hf hε (hSmall.trans (min_le_right _ _)) hy i
  have hS : ‖S‖ ≤ CA := norm_scaled_movingBoundaryAdjointL_le P C Da r b CG CD CE K hr hr1 hCE
    (zero_le_one.trans hK) hP hDa hC hBeta
  refine ⟨S,hS,?_⟩
  intro φ hφ L v hInput
  have hValue := hReal φ hφ L v hInput
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hScale : Z.symm (S v) = r • Z.symm (T v) := Z.symm.map_smul r (T v)
  rw [hScale]
  filter_upwards [Lp.coeFn_smul r (Z.symm (T v)),hValue] with w hw hv
  exact hw.trans (congrArg (fun t : ℝ => r*t) hv)

end ShrinkingSpheres
