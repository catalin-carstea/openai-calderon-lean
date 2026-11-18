import Proof.NormalEndpointSecondRay
import Proof.CoordinateTensors
import Proof.IndexedPolynomialHessian

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma exists_pos_smul_mem_disk (g : MetricField) (y v : X) {R : ℝ} (hR : 0 < R) :
    ∃ s : ℝ,0 < s ∧ s • v ∈ disk g y R := by
  let q := metricPair g y v v
  let s := R/(|q|+1)
  have hd : 0 < |q|+1 := by positivity
  have hs : 0 < s := div_pos hR hd
  have hq : q ≤ (|q|+1)^2 := by nlinarith [le_abs_self q,abs_nonneg q]
  have hmul : s*(|q|+1) = R := by dsimp [s]; field_simp
  have hsq : s^2*(|q|+1)^2 = R^2 := by rw [← mul_pow,hmul]
  refine ⟨s,hs,?_⟩
  change metricPair g y (s • v) (s • v) ≤ R^2
  rw [metricPair_smul_left,metricPair_smul_right]
  have hh := mul_le_mul_of_nonneg_left hq (sq_nonneg s)
  nlinarith only [hh,hsq]

/-- Scaling the initial velocity extends the diagonal geodesic identity to every
    tangent vector, with no restriction on the admissible normal radius. -/
theorem NormalCoordinates.second_vertical_diagonal {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (v : X) :
    fderiv ℝ (fderiv ℝ expMap) (y,0) (0,v) (0,v) = -connection g y v v := by
  obtain ⟨s,hs,hsv⟩ := exists_pos_smul_mem_disk g y v (hN.2 y hy).1
  have heq := hN.second_vertical_diagonal_on_disk hy (s • v) hsv
  have hp : ((0:X),s • v) = s • ((0:X),v) := by simp
  simp only [hp,← connectionBilinear_apply,map_smul,_root_.smul_apply,smul_smul] at heq
  have hh := congrArg (fun z : X => (s*s)⁻¹ • z) heq
  simpa only [smul_smul,smul_neg,inv_mul_cancel₀ (mul_ne_zero hs.ne' hs.ne'),one_smul,
    connectionBilinear_apply] using hh

/-- The vertical Hessian of the actual exponential map is minus the Levi-Civita
    connection at the center. This is the zero-radius jet needed for the rescaled
    principal metric and horizontal Jacobi residual. -/
theorem NormalCoordinates.second_vertical {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (hyΩ : y ∈ Ω) (v w : X) :
    fderiv ℝ (fderiv ℝ expMap) (y,0) (0,v) (0,w) = -connection g y v w := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hZero : (y,(0:X)) ∈ U := hTube ⟨hy,zero_mem_disk g y (R y)⟩
  have hReg0 : ContDiffAt ℝ ∞ expMap (y,0) := hReg.contDiffAt (hU.mem_nhds hZero)
  have hSym : fderiv ℝ (fderiv ℝ expMap) (y,0) (0,v) (0,w) =
      fderiv ℝ (fderiv ℝ expMap) (y,0) (0,w) (0,v) :=
    (hReg0.isSymmSndFDerivAt (by simp)).eq ((0:X),v) ((0:X),w)
  have hsum := hN.second_vertical_diagonal hy (v+w)
  have hv := hN.second_vertical_diagonal hy v
  have hw := hN.second_vertical_diagonal hy w
  have hp : ((0:X),v+w) = ((0:X),v)+(0,w) := by simp
  simp only [hp,map_add,_root_.add_apply,hv,hw] at hsum
  rw [← hSym] at hsum
  have hconn := connection_symmetric hΩ hg hyΩ w v
  simp only [← connectionBilinear_apply,map_add,_root_.add_apply] at hsum
  rw [connectionBilinear_apply g y w v,hconn] at hsum
  ext i
  have hh := congrArg (fun z : X => z i) hsum
  simp only [PiLp.add_apply,PiLp.neg_apply,connectionBilinear_apply] at hh ⊢
  nlinarith only [hh]

end ShrinkingSpheres
