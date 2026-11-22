module

public import Proof.CalderonN.NormalJacobiError
public import Proof.CalderonN.NormalMapTransport
public import Proof.CalderonN.NormalGeodesicTaylor
public import Proof.CalderonN.BilinearDifferenceBound

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/NormalVelocitySecondError.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def normalVelocitySecondErrorBudget (K C D : ℝ) : ℝ :=
  3*D*K^2*Real.exp (1+2*C*K+D*K^2)+2*C^2*K^2*Real.exp (1+2*C*K+D*K^2)+
    2*C*normalVariationErrorBudget K C D

/-- After subtracting its first nonzero acceleration term, the vertical Jacobi
    variation has an error quadratic in the initial speed. -/
theorem NormalCoordinates.velocity_variation_acceleration_second_error {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u : (X dim)) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun s => (normalVelocityVariation expMap y v u s).2) t+(2:ℝ) • connection g y v u‖ ≤
      normalVelocitySecondErrorBudget K C D*‖v‖^2*‖u‖ := by
  let P := normalGeodesicPhase expMap y (v,t)
  let J := normalVelocityVariation expMap y v u t
  let S := Real.exp (1+2*C*K+D*K^2)
  let B := normalVariationErrorBudget K C D
  have hPos : P.1 ∈ Ω := hN.path_image hy v (interior_subset hv) ht
  have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
  have hSpeed : ‖P.2‖ ≤ K*‖v‖ := by
    rw [show P = (expMap (y,t • v),deriv (fun s : ℝ => expMap (y,s • v)) t) from
      hN.phase_eq hy v (interior_subset hv) ht]
    exact hN.geodesic_speed_le hΩ hg hK hy v (interior_subset hv) ht
  have hA : 0 ≤ 1+2*C*K+D*K^2 := by positivity
  have hExp : Real.exp ((1+2*C*K+D*K^2)*t) ≤ S :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left ht.2 hA).trans_eq (mul_one _))
  have hJ : ‖J‖ ≤ S*‖u‖ :=
    (hN.velocity_variation_bound hΩ hg hK hC hD hΓ0 hΓ1 hy v u hv hv1 ht).trans
      ((mul_le_mul_of_nonneg_left hExp (norm_nonneg u)).trans_eq (mul_comm _ _))
  have hJPos : ‖J.1‖ ≤ S*‖u‖ := (norm_fst_le J).trans hJ
  have hJVel : ‖J.2‖ ≤ S*‖u‖ := (norm_snd_le J).trans hJ
  have hB : 0 ≤ B := by dsimp [B,normalVariationErrorBudget];positivity
  have hJError : ‖J.2-u‖ ≤ B*‖v‖*‖u‖ :=
    (hN.velocity_variation_error_le hΩ hg hK hC hD hΓ0 hΓ1 hy v u hv hv1 ht).trans
      ((mul_le_mul_of_nonneg_left ht.2 (by positivity)).trans_eq (mul_one _))
  have hVError : ‖P.2-v‖ ≤ C*K^2*‖v‖^2 := by
    rw [show P = (expMap (y,t • v),deriv (fun s : ℝ => expMap (y,s • v)) t) from
      hN.phase_eq hy v (interior_subset hv) ht]
    exact (hN.geodesic_velocity_error_le hΩ hg hK hC hΓ0 hy v (interior_subset hv) ht).trans
      ((mul_le_mul_of_nonneg_left ht.2 (by positivity)).trans_eq (mul_one _))
  have hTransport : ‖connectionBilinear g P.1-connectionBilinear g y‖ ≤ D*K*‖v‖ :=
    (hN.map_transport_bound hΩ hg hK hD (connectionBilinear g)
      (hg.contDiffOn_connectionBilinear hΩ hK) hΓ1 hy v (interior_subset hv) ht).trans
        ((mul_le_mul_of_nonneg_left ht.2 (by positivity)).trans_eq (mul_one _))
  have hC0 := hΓ0 y (hN.center_mem hy)
  have hDiff : ‖connectionBilinear g P.1 P.2 J.2-connectionBilinear g y v u‖ ≤
      (D*K^2*S+C^2*K^2*S+C*B)*‖v‖^2*‖u‖ := by
    calc
      _ ≤ ‖connectionBilinear g P.1-connectionBilinear g y‖*‖P.2‖*‖J.2‖+
          ‖connectionBilinear g y‖*‖P.2-v‖*‖J.2‖+
          ‖connectionBilinear g y‖*‖v‖*‖J.2-u‖ := norm_bilinear_difference_le _ _ _ _ _ _
      _ ≤ (D*K*‖v‖)*(K*‖v‖)*(S*‖u‖)+C*(C*K^2*‖v‖^2)*(S*‖u‖)+C*‖v‖*(B*‖v‖*‖u‖) := by
        gcongr
      _ = _ := by ring
  have hDF : ‖fderiv ℝ (connectionBilinear g) P.1 J.1 P.2 P.2‖ ≤ D*K^2*S*‖v‖^2*‖u‖ := by
    calc
      _ ≤ ‖fderiv ℝ (connectionBilinear g) P.1‖*‖J.1‖*‖P.2‖*‖P.2‖ := norm_trilinear_apply_le _ _ _ _
      _ ≤ D*(S*‖u‖)*(K*‖v‖)*(K*‖v‖) := by gcongr;exact hΓ1 _ hPos
      _ = _ := by ring
  have hVar := hasDerivAt_prod_snd (hN.hasDerivAt_phase_variation hΩ hg hK hy v u hv ht)
  change HasDerivAt (fun s => (normalVelocityVariation expMap y v u s).2)
    (fderiv ℝ (coordinateGeodesicSpray g) P J).2 t at hVar
  rw [hVar.deriv,fderiv_coordinateGeodesicSpray g P hdΓ J.1 J.2]
  have hSym : connectionBilinear g P.1 J.2 P.2 = connectionBilinear g P.1 P.2 J.2 := by
    simpa only [connectionBilinear_apply] using connection_symmetric hΩ hg hPos J.2 P.2
  change ‖-(connectionBilinear g P.1 P.2 J.2+
    (connectionBilinear g P.1 J.2 P.2+fderiv ℝ (connectionBilinear g) P.1 J.1 P.2 P.2))+
      (2:ℝ) • connection g y v u‖ ≤ _
  rw [hSym,← connectionBilinear_apply]
  have hEq : -(connectionBilinear g P.1 P.2 J.2+
      (connectionBilinear g P.1 P.2 J.2+fderiv ℝ (connectionBilinear g) P.1 J.1 P.2 P.2))+
      (2:ℝ) • connectionBilinear g y v u =
      -((2:ℝ) • (connectionBilinear g P.1 P.2 J.2-connectionBilinear g y v u))-
        fderiv ℝ (connectionBilinear g) P.1 J.1 P.2 P.2 := by module
  rw [hEq]
  have hTwice : ‖-((2:ℝ) • (connectionBilinear g P.1 P.2 J.2-connectionBilinear g y v u))‖ ≤
      2*((D*K^2*S+C^2*K^2*S+C*B)*‖v‖^2*‖u‖) := by
    simpa only [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] using
      mul_le_mul_of_nonneg_left hDiff (by norm_num : (0:ℝ)≤2)
  exact (norm_sub_le _ _).trans ((add_le_add hTwice hDF).trans_eq (by
    dsimp [normalVelocitySecondErrorBudget,S,B];ring))

end CalderonN
