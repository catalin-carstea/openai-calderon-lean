import Proof.CoordinateSpraySecondBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

/-- The mixed spray forcing remembers the separate position and velocity
    components of the two variations. -/
theorem Elliptic.norm_second_spray_separated {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K) (p J L : X × X) (hp : p.1 ∈ Ω)
    (C D E : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hΓ0 : ‖connectionBilinear g p.1‖ ≤ C)
    (hΓ1 : ‖fderiv ℝ (connectionBilinear g) p.1‖ ≤ D)
    (hΓ2 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1‖ ≤ E) :
    ‖fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) p L J‖ ≤
      2*C*‖L.2‖*‖J.2‖+2*D*‖L.1‖*‖p.2‖*‖J.2‖+
        2*D*‖J.1‖*‖L.2‖*‖p.2‖+E*‖L.1‖*‖J.1‖*‖p.2‖^2 := by
  have h1 : ‖connectionBilinear g p.1 L.2 J.2‖ ≤ C*‖L.2‖*‖J.2‖ :=
    (norm_bilinear_apply_le _ _ _).trans (by gcongr)
  have h2 : ‖fderiv ℝ (connectionBilinear g) p.1 L.1 p.2 J.2‖ ≤ D*‖L.1‖*‖p.2‖*‖J.2‖ :=
    (norm_trilinear_apply_le _ _ _ _).trans (by gcongr)
  have h3 : ‖connectionBilinear g p.1 J.2 L.2‖ ≤ C*‖L.2‖*‖J.2‖ := by
    exact ((norm_bilinear_apply_le _ _ _).trans (by gcongr :
      ‖connectionBilinear g p.1‖*‖J.2‖*‖L.2‖ ≤ C*‖J.2‖*‖L.2‖)).trans_eq (by ring)
  have h4 : ‖fderiv ℝ (connectionBilinear g) p.1 L.1 J.2 p.2‖ ≤ D*‖L.1‖*‖p.2‖*‖J.2‖ := by
    exact ((norm_trilinear_apply_le _ _ _ _).trans (by gcongr :
      ‖fderiv ℝ (connectionBilinear g) p.1‖*‖L.1‖*‖J.2‖*‖p.2‖ ≤
        D*‖L.1‖*‖J.2‖*‖p.2‖)).trans_eq (by ring)
  have h5 : ‖fderiv ℝ (connectionBilinear g) p.1 J.1 p.2 L.2‖ ≤ D*‖J.1‖*‖L.2‖*‖p.2‖ := by
    exact ((norm_trilinear_apply_le _ _ _ _).trans (by gcongr :
      ‖fderiv ℝ (connectionBilinear g) p.1‖*‖J.1‖*‖p.2‖*‖L.2‖ ≤
        D*‖J.1‖*‖p.2‖*‖L.2‖)).trans_eq (by ring)
  have h6 : ‖fderiv ℝ (connectionBilinear g) p.1 J.1 L.2 p.2‖ ≤ D*‖J.1‖*‖L.2‖*‖p.2‖ :=
    (norm_trilinear_apply_le _ _ _ _).trans (by gcongr)
  have h7 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 L.1 J.1 p.2 p.2‖ ≤
      E*‖L.1‖*‖J.1‖*‖p.2‖^2 := by
    exact ((norm_quadrilinear_apply_le _ _ _ _ _).trans (by gcongr :
      ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1‖*‖L.1‖*‖J.1‖*‖p.2‖*‖p.2‖ ≤
        E*‖L.1‖*‖J.1‖*‖p.2‖*‖p.2‖)).trans_eq (by ring)
  rw [hg.second_fderiv_coordinateGeodesicSpray hΩ hK p hp J.1 J.2 L.1 L.2,
    Prod.norm_mk,norm_zero,norm_neg]
  apply max_le (by positivity)
  refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _)
    ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _)
      ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))))))).trans ?_
  linarith only [h1,h2,h3,h4,h5,h6,h7]

/-- If one variation is parallel in the center, its velocity is small. Hence
    its mixed forcing with an ordinary initial-velocity variation is small too. -/
theorem Elliptic.norm_second_spray_parallel_le {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K) (p J L : X × X) (hp : p.1 ∈ Ω)
    (a b : X) (s C D E P V Q : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hP : 0 ≤ P) (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (hΓ0 : ‖connectionBilinear g p.1‖ ≤ C)
    (hΓ1 : ‖fderiv ℝ (connectionBilinear g) p.1‖ ≤ D)
    (hΓ2 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1‖ ≤ E)
    (hSpeed : ‖p.2‖ ≤ K*s) (hJ : ‖J‖ ≤ P*‖a‖)
    (hJv : ‖J.2‖ ≤ V*s*‖a‖) (hL : ‖L‖ ≤ Q*‖b‖) :
    ‖fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) p L J‖ ≤
      (2*C*Q*V+2*D*Q*K*V+2*D*P*Q*K+E*Q*P*K^2)*s*‖a‖*‖b‖ := by
  have hJp := (norm_fst_le J).trans hJ
  have hLp := (norm_fst_le L).trans hL
  have hLv := (norm_snd_le L).trans hL
  have hsSq : s^2 ≤ s := by nlinarith
  have hb := hg.norm_second_spray_separated hΩ hK p J L hp C D E hC hD hE hΓ0 hΓ1 hΓ2
  calc
    _ ≤ 2*C*(Q*‖b‖)*(V*s*‖a‖)+2*D*(Q*‖b‖)*(K*s)*(V*s*‖a‖)+
        2*D*(P*‖a‖)*(Q*‖b‖)*(K*s)+E*(Q*‖b‖)*(P*‖a‖)*(K*s)^2 := by
      exact hb.trans (by gcongr)
    _ = (2*C*Q*V+2*D*P*Q*K)*s*‖a‖*‖b‖+
        (2*D*Q*K*V+E*Q*P*K^2)*‖a‖*‖b‖*s^2 := by ring
    _ ≤ (2*C*Q*V+2*D*P*Q*K)*s*‖a‖*‖b‖+
        (2*D*Q*K*V+E*Q*P*K^2)*‖a‖*‖b‖*s := by gcongr
    _ = _ := by ring

end ShrinkingSpheres
