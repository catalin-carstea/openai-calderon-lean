import Proof.PhysicalHalfCovariantGreenBound
import Proof.UniformActualHalfCovariantErrorData
import Proof.DensityCoefficientJets
import Proof.BackgroundBudgets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma Admissible.relative_density_axis_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {y : X} (hy : y ∈ Y) (i : I) :
    |directionalFDeriv (axis i) (metricDensity d.γ) y| ≤
      (27*K*|M ⟨1,by omega⟩|)*metricDensity d.γ y := by
  exact (hd.1.1.relative_density_coordinate_jets hΩ hK (hd.2.1.center_mem hy)
    |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (abs_nonneg _) (abs_nonneg _)
    (fun j k => (hd.1.reference_fderiv_bound (by omega) (hd.2.1.center_mem hy) j k).trans (le_abs_self _))
    (fun j k => (hd.1.reference_second_fderiv_bound hm (hd.2.1.center_mem hy) j k).trans (le_abs_self _)) i i).1

/-- Closed uniform physical first-error form estimate. Endpoints retain the
    SAME actual coarse realization, and the form is on any canonical test.
    This is the first-error contribution, not the full principal coefficient. -/
theorem uniform_actual_first_error_half_first_form {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ a : X,
      ∀ R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y → ContDiffOn ℝ ∞ G Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∃ Lo : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∃ Hi : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        ContDiffOn ℝ ∞ Lo Y ∧ ContDiffOn ℝ ∞ Hi Y ∧
        (∀ x ∈ Y,
          (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A G x)=
            (Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (Hi x)=
            (actualFirstAdjointErrorFamily d a A G x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) ∧
        ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
          Test Y d.γ d.frame φ → ∀ i : I,
          |∫ y in Y,D.halfCovariantFirstDensity Lo i y| ≤ CE*‖a‖*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨η,C0,C1,hη,hη1,hC0,hC1,hData⟩ := uniform_actual_first_error_half_covariant_data
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let MD := 27*K*|M ⟨1,by omega⟩|
  let CE := halfDualPairingNorm*(C0+C1)*(MD+3)*(3*K^2+1)
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hMD : 0 ≤ MD := mul_nonneg (mul_nonneg (by norm_num) hK0.le) (abs_nonneg _)
  have hCE : 0 ≤ CE := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (add_nonneg hC0 hC1))
      (by linarith)) (by positivity)
  refine ⟨η,CE,hη,hη1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd a R A G hAS hGS hR hA hG
  obtain ⟨Lo,Hi,hLS,hHS,hAll⟩ := hData floor hf ε hε hSmall d hd a R A G hAS hGS hR hA hG
  refine ⟨Lo,Hi,hLS,hHS,fun x hx => ⟨(hAll x hx).1,(hAll x hx).2.1⟩,?_⟩
  intro φ E D hφ i
  let Q := (C0+C1)*‖a‖
  have hQ : 0 ≤ Q := mul_nonneg (add_nonneg hC0 hC1) (norm_nonneg _)
  have hgY : Elliptic Y K d.γ := ⟨fun j k => (hd.1.1.1 j k).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y :=
    fun j => (hd.1.2.2.2.2.2.2.1 j).mono (fun x hx => hd.2.1.center_mem hx)
  have hFrame : ∀ x ∈ Y,∀ j k,metricPair d.γ x (d.frame x j) (d.frame x k)=if j=k then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)
  have hPair := fun x hx => (hAll x hx).2.2.1
  have hC (x : X) (hx : x ∈ Y) : ‖Lo x‖ ≤ Q*ε/beta d.γ d.radius x := by
    obtain ⟨_,_,_,hLo,_,_⟩ := hAll x hx
    have hp := hd.2.2.2.2.1.2 x hx
    have hβ : 0 < beta d.γ d.radius x := zero_lt_one.trans_le (hf.trans hp.2.1)
    have hRad := radius_bounds (d.radius x) (beta d.γ d.radius x) floor ε hp.1.le hf hp.2.1
      (hd.2.2.2.2.2 x hx).2
    have hr : d.radius x ≤ ε/beta d.γ d.radius x := (le_div_iff₀ hβ).mpr
      (hRad.2.1.trans (div_le_self hε hf))
    have hQ0 : C0*‖a‖ ≤ Q := by dsimp only [Q];nlinarith only [hC1,norm_nonneg a]
    calc
      _ ≤ (C0*‖a‖)*d.radius x := hLo
      _ ≤ Q*d.radius x := mul_le_mul_of_nonneg_right hQ0 hp.1.le
      _ ≤ Q*(ε/beta d.γ d.radius x) := mul_le_mul_of_nonneg_left hr hQ
      _ = _ := by ring
  have hDC (x : X) (hx : x ∈ Y) : ‖halfOperatorCovariantDerivativeL d Lo Hi x (axis i)‖ ≤ Q*ε := by
    have hh := ((hAll x hx).2.2.2.2.2 (axis i) (by simpa only [norm_axis] using (le_refl (1:ℝ)))).2
    have hQ1 : C1*‖a‖ ≤ Q := by dsimp only [Q];nlinarith only [hC0,norm_nonneg a]
    exact hh.trans (mul_le_mul_of_nonneg_right hQ1 hε)
  have hBound := D.integral_half_covariant_first_form_bound hY hgY hK he hFrame hd.2.2.2.2.1 hf hφ
    Lo Hi hLS hHS hPair i hQ hMD hε hC hDC
      (fun x hx => hd.relative_density_axis_bound hΩ (by omega) hK0 hx i)
  exact hBound.trans_eq (by dsimp only [CE,Q];ring)
end ShrinkingSpheres
