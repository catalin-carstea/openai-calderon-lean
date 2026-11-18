import Proof.MatrixFamilyCoefficientMixedBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Matrix.Norms.Operator
namespace ShrinkingSpheres

/-- The matrix coefficient calculus preserves quadratic center/angular
    metric jets on the same genuine local family. -/
theorem matrixFamily_coefficient_quadratic_mixed_bound {S : Set (ℝ × X)} (hS : IsOpen S) (G : ℝ × X → Mat)
    (hG : ∀ i j,ContDiffOn ℝ ∞ (fun q => G q i j) S) (hDet : ∀ q ∈ S,0 < (G q).det)
    (z : X) (hz : ((0:ℝ),z) ∈ S) (b : X) (r KP D A B C : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hKP : 0 ≤ KP) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hInv : ∀ i j,|(G (0,z))⁻¹ i j| ≤ KP) (hMu : matrixFamilyDensity G (0,z) ≤ D)
    (hCenter : ∀ i j,|fderiv ℝ (fun q => G q i j) (0,z) (1,0)| ≤ A*r^2)
    (hAngular : ∀ i j,|fderiv ℝ (fun q => G q i j) (0,z) (0,b)| ≤ B*r^2*‖b‖)
    (hMixed : ∀ i j,|fderiv ℝ (fderiv ℝ (fun q => G q i j)) (0,z) (0,b) (1,0)| ≤ C*r^2*‖b‖) :
    ∀ i j,
      |fderiv ℝ (fun q => matrixFamilyCoefficient G q i j) (0,z) (1,0)| ≤ (D*18*KP^2*A)*r^2 ∧
      |fderiv ℝ (fderiv ℝ (fun q => matrixFamilyCoefficient G q i j)) (0,z) (0,b) (1,0)| ≤
        (D*(486*KP^3*A*B+18*KP^2*C))*r^2*‖b‖ := by
  intro i j
  have hFirst := matrixFamily_coefficient_directional_bound hS G hG hDet hz (1,0) KP (A*r^2)
    hKP (by positivity) hInv hCenter i j
  have hSecond := matrixFamily_coefficient_mixed_bound hS G hG hDet hz (1,0) (0,b)
    KP (A*r^2) (B*r^2*‖b‖) (C*r^2*‖b‖) hKP (by positivity) (by positivity) (by positivity)
    hInv hCenter hAngular hMixed i j
  have hSq : r^2 ≤ 1 := by nlinarith only [hr,hr1]
  have hFourth : r^4 ≤ r^2 := by nlinarith only [mul_le_mul_of_nonneg_left hSq (sq_nonneg r)]
  constructor
  · exact hFirst.trans ((mul_le_mul_of_nonneg_right hMu (by positivity)).trans_eq (by ring))
  · have hb := hSecond.trans (mul_le_mul_of_nonneg_right hMu (by positivity))
    have hAlg : D*(486*KP^3*(A*r^2)*(B*r^2*‖b‖)+18*KP^2*(C*r^2*‖b‖)) =
        (D*486*KP^3*A*B*‖b‖)*r^4+(D*18*KP^2*C*‖b‖)*r^2 := by ring
    rw [hAlg] at hb
    have hLe : (D*486*KP^3*A*B*‖b‖)*r^4+(D*18*KP^2*C*‖b‖)*r^2 ≤
        (D*486*KP^3*A*B*‖b‖)*r^2+(D*18*KP^2*C*‖b‖)*r^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hFourth
        (show 0 ≤ D*486*KP^3*A*B*‖b‖ by positivity)) le_rfl
    exact hb.trans (hLe.trans_eq (by ring))

end ShrinkingSpheres
