import Proof.SpraySecondPrincipalError
import Proof.NormalSecondVariationBounds
import Proof.NormalVelocitySecondError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

def secondVelocityPrincipalErrorBudget (K C D E : ℝ) : ℝ :=
  (2*C*K+D*K^2)*secondNormalVariationBudget K C D E+
    6*D*K*Real.exp (1+2*C*K+D*K^2)^2+
    2*C*normalVariationErrorBudget K C D*(Real.exp (1+2*C*K+D*K^2)+1)+
    E*K^2*Real.exp (1+2*C*K+D*K^2)^2

/-- The second velocity variation has constant leading acceleration -2 Gamma;
    the remaining acceleration gains one initial-speed factor. -/
theorem NormalCoordinates.second_velocity_acceleration_error {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C D E : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v u k : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun s => (secondParameterVariation (normalGeodesicPhase expMap y) u k (v,s)).2) t+
      (2:ℝ) • connectionBilinear g y k u‖ ≤
      secondVelocityPrincipalErrorBudget K C D E*‖v‖*‖u‖*‖k‖ := by
  let P := normalGeodesicPhase expMap y (v,t)
  let Ju := firstParameterVariation (normalGeodesicPhase expMap y) u (v,t)
  let Jk := firstParameterVariation (normalGeodesicPhase expMap y) k (v,t)
  let Z := secondParameterVariation (normalGeodesicPhase expMap y) u k (v,t)
  let S := Real.exp (1+2*C*K+D*K^2)
  let B := normalVariationErrorBudget K C D
  let S2 := secondNormalVariationBudget K C D E
  let Q := 6*D*K*S^2+2*C*B*(S+1)+E*K^2*S^2
  have hPos : P.1 ∈ Ω := hN.path_image hy v (interior_subset hv) ht
  have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
  have hSpeed : ‖P.2‖ ≤ K*‖v‖ := by
    rw [show P = (expMap (y,t • v),deriv (fun s : ℝ => expMap (y,s • v)) t) from
      hN.phase_eq hy v (interior_subset hv) ht]
    exact hN.geodesic_speed_le hΩ hg hK hy v (interior_subset hv) ht
  have hS : 0 ≤ S := (Real.exp_pos _).le
  have hB : 0 ≤ B := by dsimp [B,normalVariationErrorBudget];positivity
  have hS2 : 0 ≤ S2 := by dsimp [S2,secondNormalVariationBudget];positivity
  have hA : 0 ≤ 1+2*C*K+D*K^2 := by positivity
  have hExp : Real.exp ((1+2*C*K+D*K^2)*t) ≤ S :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left ht.2 hA).trans_eq (mul_one _))
  have hFirst (w : X) : ‖firstParameterVariation (normalGeodesicPhase expMap y) w (v,t)‖ ≤ S*‖w‖ :=
    (hN.velocity_variation_bound hΩ hg hK hC hD hΓ0 hΓ1 hy v w hv hv1 ht).trans
      ((mul_le_mul_of_nonneg_left hExp (norm_nonneg w)).trans_eq (mul_comm _ _))
  have hFirstError (w : X) :
      ‖(firstParameterVariation (normalGeodesicPhase expMap y) w (v,t)).2-w‖ ≤ B*‖v‖*‖w‖ :=
    (hN.velocity_variation_error_le hΩ hg hK hC hD hΓ0 hΓ1 hy v w hv hv1 ht).trans
      ((mul_le_mul_of_nonneg_left ht.2 (by positivity)).trans_eq (mul_one _))
  have hTransport : ‖connectionBilinear g P.1-connectionBilinear g y‖ ≤ D*K*‖v‖ :=
    (hN.map_transport_bound hΩ hg hK hD (connectionBilinear g)
      (hg.contDiffOn_connectionBilinear hΩ hK) hΓ1 hy v (interior_subset hv) ht).trans
        ((mul_le_mul_of_nonneg_left ht.2 (by positivity)).trans_eq (mul_one _))
  have hForceFull := hg.second_spray_principal_error hΩ hK P Ju Jk y u k hPos ‖v‖ C D E S B
    (norm_nonneg v) hv1 hC hD hE hS hB (hΓ0 y (hN.center_mem hy)) (hΓ1 _ hPos) (hΓ2 _ hPos)
    hTransport hSpeed (hFirst u) (hFirst k) (hFirstError u) (hFirstError k)
  have hForce : ‖(fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) P Jk Ju).2+
      (2:ℝ) • connectionBilinear g y k u‖ ≤ Q*‖v‖*‖u‖*‖k‖ := by
    have hh := (norm_snd_le (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) P Jk Ju-
      ((0:X),-(2:ℝ) • connectionBilinear g y k u))).trans hForceFull
    change ‖(fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) P Jk Ju).2-
      (-(2:ℝ) • connectionBilinear g y k u)‖ ≤ _ at hh
    simpa only [neg_smul,sub_neg_eq_add] using hh
  have hZ : ‖Z‖ ≤ S2*‖u‖*‖k‖ :=
    hN.second_velocity_variation_bound hΩ hg hK hC hD hE hΓ0 hΓ1 hΓ2 hy v u k hv hv1 ht
  have hLinear : ‖(fderiv ℝ (coordinateGeodesicSpray g) P Z).2‖ ≤
      (2*C*K+D*K^2)*S2*‖v‖*‖u‖*‖k‖ := by
    have hb := norm_fderiv_coordinateGeodesicSpray_snd_le g P Z hdΓ C D (K*‖v‖)
      hC hD (by positivity) (hΓ0 _ hPos) (hΓ1 _ hPos) hSpeed
    have hFirstBound := hb.trans (mul_le_mul_of_nonneg_left hZ (by positivity))
    have hvSq : ‖v‖^2 ≤ ‖v‖ := by nlinarith [norm_nonneg v]
    have hSmall := mul_le_mul_of_nonneg_left hvSq (show 0 ≤ D*K^2*(S2*‖u‖*‖k‖) by positivity)
    nlinarith only [hFirstBound,hSmall]
  have hVar := hasDerivAt_prod_snd (hN.hasDerivAt_second_phase_variation hΩ hg hK hy v u k hv ht)
  rw [hVar.deriv]
  change ‖(fderiv ℝ (coordinateGeodesicSpray g) P Z).2+
    (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) P Jk Ju).2+
      (2:ℝ) • connectionBilinear g y k u‖ ≤ _
  rw [add_assoc]
  exact (norm_add_le _ _).trans ((add_le_add hLinear hForce).trans_eq (by
    dsimp [secondVelocityPrincipalErrorBudget,S2,Q,S,B];ring))

end ShrinkingSpheres
