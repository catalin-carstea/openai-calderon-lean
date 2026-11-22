module

public import Proof.CalderonN.CoordinateSpraySecondBounds
public import Proof.CalderonN.BilinearDifferenceBound

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/SpraySecondPrincipalError.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The second spray derivative has a constant principal forcing in velocity
    variations. Every remaining term gains one power of the small speed. -/
theorem Elliptic.second_spray_principal_error {Ω : Set (X dim)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K) (p J L : (X dim) × (X dim)) (y u k : (X dim))
    (hp : p.1 ∈ Ω) (s C D E S B : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hΓ0 : ‖connectionBilinear g y‖ ≤ C)
    (hΓ1 : ‖fderiv ℝ (connectionBilinear g) p.1‖ ≤ D)
    (hΓ2 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1‖ ≤ E)
    (hTransport : ‖connectionBilinear g p.1-connectionBilinear g y‖ ≤ D*K*s)
    (hSpeed : ‖p.2‖ ≤ K*s) (hJ : ‖J‖ ≤ S*‖u‖) (hL : ‖L‖ ≤ S*‖k‖)
    (hJError : ‖J.2-u‖ ≤ B*s*‖u‖) (hLError : ‖L.2-k‖ ≤ B*s*‖k‖) :
    ‖fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) p L J-
      ((0:(X dim)),-(2:ℝ) • connectionBilinear g y k u)‖ ≤
      (6*D*K*S^2+2*C*B*(S+1)+E*K^2*S^2)*s*‖u‖*‖k‖ := by
  have hJp : ‖J.1‖ ≤ S*‖u‖ := (norm_fst_le J).trans hJ
  have hJv : ‖J.2‖ ≤ S*‖u‖ := (norm_snd_le J).trans hJ
  have hLp : ‖L.1‖ ≤ S*‖k‖ := (norm_fst_le L).trans hL
  have hLv : ‖L.2‖ ≤ S*‖k‖ := (norm_snd_le L).trans hL
  let a0 := connectionBilinear g p.1 L.2 J.2
  let aRef := connectionBilinear g y k u
  let t2 := fderiv ℝ (connectionBilinear g) p.1 L.1 p.2 J.2
  let t4 := fderiv ℝ (connectionBilinear g) p.1 L.1 J.2 p.2
  let t5 := fderiv ℝ (connectionBilinear g) p.1 J.1 p.2 L.2
  let t6 := fderiv ℝ (connectionBilinear g) p.1 J.1 L.2 p.2
  let t7 := fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 L.1 J.1 p.2 p.2
  have hMain : ‖a0-aRef‖ ≤ (D*K*S^2+C*B*S+C*B)*s*‖u‖*‖k‖ := by
    calc
      _ ≤ ‖connectionBilinear g p.1-connectionBilinear g y‖*‖L.2‖*‖J.2‖+
          ‖connectionBilinear g y‖*‖L.2-k‖*‖J.2‖+
          ‖connectionBilinear g y‖*‖k‖*‖J.2-u‖ := norm_bilinear_difference_le _ _ _ _ _ _
      _ ≤ (D*K*s)*(S*‖k‖)*(S*‖u‖)+C*(B*s*‖k‖)*(S*‖u‖)+C*‖k‖*(B*s*‖u‖) := by gcongr
      _ = _ := by ring
  have h2 : ‖t2‖ ≤ D*K*S^2*s*‖u‖*‖k‖ := by
    calc
      _ ≤ ‖fderiv ℝ (connectionBilinear g) p.1‖*‖L.1‖*‖p.2‖*‖J.2‖ := norm_trilinear_apply_le _ _ _ _
      _ ≤ D*(S*‖k‖)*(K*s)*(S*‖u‖) := by gcongr
      _ = _ := by ring
  have h4 : ‖t4‖ ≤ D*K*S^2*s*‖u‖*‖k‖ := by
    calc
      _ ≤ ‖fderiv ℝ (connectionBilinear g) p.1‖*‖L.1‖*‖J.2‖*‖p.2‖ := norm_trilinear_apply_le _ _ _ _
      _ ≤ D*(S*‖k‖)*(S*‖u‖)*(K*s) := by gcongr
      _ = _ := by ring
  have h5 : ‖t5‖ ≤ D*K*S^2*s*‖u‖*‖k‖ := by
    calc
      _ ≤ ‖fderiv ℝ (connectionBilinear g) p.1‖*‖J.1‖*‖p.2‖*‖L.2‖ := norm_trilinear_apply_le _ _ _ _
      _ ≤ D*(S*‖u‖)*(K*s)*(S*‖k‖) := by gcongr
      _ = _ := by ring
  have h6 : ‖t6‖ ≤ D*K*S^2*s*‖u‖*‖k‖ := by
    calc
      _ ≤ ‖fderiv ℝ (connectionBilinear g) p.1‖*‖J.1‖*‖L.2‖*‖p.2‖ := norm_trilinear_apply_le _ _ _ _
      _ ≤ D*(S*‖u‖)*(S*‖k‖)*(K*s) := by gcongr
      _ = _ := by ring
  have h7 : ‖t7‖ ≤ E*K^2*S^2*s*‖u‖*‖k‖ := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1‖*‖L.1‖*‖J.1‖*‖p.2‖*‖p.2‖ := norm_quadrilinear_apply_le _ _ _ _ _
      _ ≤ E*(S*‖k‖)*(S*‖u‖)*(K*s)*(K*s) := by gcongr
      _ = (E*K^2*S^2*s*‖u‖*‖k‖)*s := by ring
      _ ≤ E*K^2*S^2*s*‖u‖*‖k‖ :=
        (mul_le_mul_of_nonneg_left hs1 (by positivity)).trans_eq (mul_one _)
  have hSym : connectionBilinear g p.1 J.2 L.2 = a0 := by
    simpa only [a0,connectionBilinear_apply] using connection_symmetric hΩ hg hp J.2 L.2
  have hRewrite : fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) p L J =
      ((0:(X dim)),-((a0+t2)+((a0+t4)+(t5+(t6+t7))))) := by
    simpa only [a0,t2,t4,t5,t6,t7,hSym] using
      hg.second_fderiv_coordinateGeodesicSpray hΩ hK p hp J.1 J.2 L.1 L.2
  have hEq : fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) p L J-
      ((0:(X dim)),-(2:ℝ) • connectionBilinear g y k u) =
      ((0:(X dim)),-(2:ℝ) • (a0-aRef)-(t2+(t4+(t5+(t6+t7))))) := by
    rw [hRewrite]
    apply Prod.ext
    · simp
    · change -((a0+t2)+((a0+t4)+(t5+(t6+t7))))-(-(2:ℝ) • aRef) =
        -(2:ℝ) • (a0-aRef)-(t2+(t4+(t5+(t6+t7))))
      module
  have hRest : ‖t2+(t4+(t5+(t6+t7)))‖ ≤ (4*D*K*S^2+E*K^2*S^2)*s*‖u‖*‖k‖ := by
    have hb := (norm_add_le _ _).trans (add_le_add h2
      ((norm_add_le _ _).trans (add_le_add h4
        ((norm_add_le _ _).trans (add_le_add h5
          ((norm_add_le _ _).trans (add_le_add h6 h7)))))))
    exact hb.trans_eq (by ring)
  have hTwice : ‖-(2:ℝ) • (a0-aRef)‖ ≤ 2*((D*K*S^2+C*B*S+C*B)*s*‖u‖*‖k‖) := by
    simpa only [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] using
      mul_le_mul_of_nonneg_left hMain (by norm_num : (0:ℝ)≤2)
  rw [hEq,Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg _)]
  exact (norm_sub_le _ _).trans ((add_le_add hTwice hRest).trans_eq (by ring))

end CalderonN
