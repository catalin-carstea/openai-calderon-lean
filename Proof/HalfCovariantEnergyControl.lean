import Proof.HalfCanonicalCovariantSection
import Proof.PhysicalErrorForms
import Proof.FrameCoordinateCovectors
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_real_weighted_sum_three_sq_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : I → ℝ) (v : I → F) (K : ℝ) (hK : 0 ≤ K) (hc : ∀ i,|c i| ≤ K) :
    ‖∑ i : I,c i • v i‖^2 ≤ 3*K^2*(∑ i : I,‖v i‖^2) := by
  have hN : ‖∑ i : I,c i • v i‖ ≤ K*(∑ i : I,‖v i‖) := by
    calc
      _ ≤ ∑ i : I,‖c i • v i‖ := norm_sum_le _ _
      _ ≤ ∑ i : I,K*‖v i‖ := Finset.sum_le_sum (fun i _ => by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hS : (∑ i : I,‖v i‖)^2 ≤ 3*(∑ i : I,‖v i‖^2) := by
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_one]
      using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : I => (1:ℝ)) (fun i => ‖v i‖)
  calc
    _ ≤ (K*(∑ i : I,‖v i‖))^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hN
    _ = K^2*(∑ i : I,‖v i‖)^2 := mul_pow _ _ _
    _ ≤ K^2*(3*(∑ i : I,‖v i‖^2)) := mul_le_mul_of_nonneg_left hS (sq_nonneg K)
    _ = _ := by ring

lemma norm_linear_axis_sq_le_frame_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Y : Set X} {g : MetricField} {K : ℝ} (hg : Elliptic Y K g) (hK : 1 ≤ K)
    (e : Frame) {y : X} (hy : y ∈ Y)
    (hFrame : ∀ j k,metricPair g y (e y j) (e y k)=if j=k then 1 else 0)
    (V : X →L[ℝ] F) (i : I) :
    ‖V (axis i)‖^2 ≤ 3*K^2*(∑ j : I,‖V (e y j)‖^2) := by
  have hV : V (axis i)=∑ j : I,frameCoordinateLinear g e y j (axis i) • V (e y j) := by
    have hh := congrArg V (frameCoordinateLinear_reconstruct g e y (axis i) hFrame)
    simpa only [map_sum,map_smul] using hh.symm
  rw [hV]
  apply norm_real_weighted_sum_three_sq_le _ _ K (zero_le_one.trans hK)
  intro j
  rw [frameCoordinateLinear_apply]
  exact hg.frame_coordinate_abs_bound hK e hy hFrame i j

def halfCovariantDirectionEnergy (d : Data) (U : X → SphereSobolev (3/2:ℝ)) (y : X) (β : ℝ) (a : X) : ℝ :=
  β⁻¹*‖halfSectionCovariantDerivativeL d U y a‖^2+β*‖U y‖^2

lemma weighted_direction_energy_comparison (β k x y g h m n : ℝ)
    (hβ : 0 ≤ β) (hk : 0 ≤ k) (hg : 0 ≤ g) (hh : 0 ≤ h) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hx : x ≤ k*g) (hy : y ≤ k*h) :
    β⁻¹*x+β*m+(β⁻¹*y+β*n) ≤ (k+1)*(β⁻¹*g+β*m+(β⁻¹*h+β*n)) := by
  have hX := mul_le_mul_of_nonneg_left (add_le_add hx hy) (inv_nonneg.mpr hβ)
  have hG := mul_nonneg (inv_nonneg.mpr hβ) hg
  have hH := mul_nonneg (inv_nonneg.mpr hβ) hh
  have hM := mul_nonneg hβ hm
  have hN := mul_nonneg hβ hn
  have hKM := mul_nonneg hk (add_nonneg hM hN)
  nlinarith only [hX,hG,hH,hM,hN,hKM]

/-- The genuine covariant section energy used by the Green formula is
    controlled by the frozen physical energy, using only frame values. -/
theorem AngularModelData.half_covariant_direction_energy_le
    {Y : Set X} {d : Data} {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ}
    (D : AngularModelData E d.radius) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y)
    (hFrame : ∀ x ∈ Y,∀ j k,metricPair d.γ x (d.frame x j) (d.frame x k)=if j=k then 1 else 0)
    (hφ : smoothNear φ (bundle Y d.γ)) {y : X} (hy : y ∈ Y) (i : I) :
    metricDensity d.γ y*(
      halfCovariantDirectionEnergy d (E.realSobolevSection (3/2:ℝ) (by norm_num)) y (beta d.γ d.radius y) (axis i)+
      halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y (beta d.γ d.radius y) (axis i)) ≤
      (3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let β := beta d.γ d.radius y
  let Ur := E.realSobolevSection (3/2:ℝ) (by norm_num)
  let Ui := E.imagSobolevSection (3/2:ℝ) (by norm_num)
  let Vr := halfSectionCovariantDerivativeL d Ur y
  let Vi := halfSectionCovariantDerivativeL d Ui y
  have hR (j : I) : ‖Vr (d.frame y j)‖=‖D.realErrorHorizontal y j‖ := by
    simpa only [Vr,Ur,HarmonicTestExpansion.realSobolevSection,Complex.reCLM_apply,AngularModelData.realErrorHorizontal]
      using D.realComponent.norm_half_covariant_section hY hg (zero_lt_one.trans_le hK) he hFrame hφ hy j
  have hI (j : I) : ‖Vi (d.frame y j)‖=‖D.imagErrorHorizontal y j‖ := by
    simpa only [Vi,Ui,HarmonicTestExpansion.imagSobolevSection,Complex.imCLM_apply,AngularModelData.imagErrorHorizontal]
      using D.imagComponent.norm_half_covariant_section hY hg (zero_lt_one.trans_le hK) he hFrame hφ hy j
  have hXR := norm_linear_axis_sq_le_frame_sum hg hK d.frame hy (hFrame y hy) Vr i
  have hXI := norm_linear_axis_sq_le_frame_sum hg hK d.frame hy (hFrame y hy) Vi i
  simp_rw [hR] at hXR
  simp_rw [hI] at hXI
  have hMR : ‖Ur y‖=‖D.realErrorMass y‖ := E.norm_realSobolevSection _ _ y
  have hMI : ‖Ui y‖=‖D.imagErrorMass y‖ := E.norm_imagSobolevSection _ _ y
  have hβ : 0 ≤ β := Real.sqrt_nonneg _
  have hInside : halfCovariantDirectionEnergy d Ur y β (axis i)+halfCovariantDirectionEnergy d Ui y β (axis i) ≤
      (3*K^2+1)*(errorEnergy β (D.realErrorHorizontal y) (D.realErrorMass y)+
        errorEnergy β (D.imagErrorHorizontal y) (D.imagErrorMass y)) := by
    simp only [halfCovariantDirectionEnergy,hMR,hMI,errorEnergy]
    exact weighted_direction_energy_comparison β (3*K^2) _ _ _ _ _ _ hβ
      (mul_nonneg (by norm_num) (sq_nonneg K))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (sq_nonneg _) (sq_nonneg _) hXR hXI
  have hmu : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  calc
    _ ≤ metricDensity d.γ y*((3*K^2+1)*(errorEnergy β (D.realErrorHorizontal y) (D.realErrorMass y)+
        errorEnergy β (D.imagErrorHorizontal y) (D.imagErrorMass y))) := mul_le_mul_of_nonneg_left hInside hmu
    _ = (3*K^2+1)*(metricDensity d.γ y*(errorEnergy β (D.realErrorHorizontal y) (D.realErrorMass y)+
        errorEnergy β (D.imagErrorHorizontal y) (D.imagErrorMass y))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (D.errorEnergy_components_le hFrame hy) (by positivity)
end ShrinkingSpheres
