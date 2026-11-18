import Proof.MatrixFamilyCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- The density times inverse matrix transforms by the same conjugation
    under an orthogonal change of frame. No inverse hypothesis on the metric
    matrix is needed for this exact identity. -/
theorem density_inverse_orthogonal_conjugation (Q G : Mat)
    (hLeft : Q.transpose*Q = 1) (hRight : Q*Q.transpose = 1) :
    Real.sqrt (Q.transpose*G*Q).det • (Q.transpose*G*Q)⁻¹ =
      Q.transpose*(Real.sqrt G.det • G⁻¹)*Q := by
  have hDetQ : Q.det*Q.det = 1 := by
    have h := congrArg Matrix.det hLeft
    simpa only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] using h
  have hDet : (Q.transpose*G*Q).det = G.det := by
    simp only [Matrix.det_mul,Matrix.det_transpose]
    calc
      Q.det*G.det*Q.det = G.det*(Q.det*Q.det) := by ring
      _ = G.det := by rw [hDetQ,mul_one]
  have hInvQ : Q⁻¹ = Q.transpose := Matrix.inv_eq_left_inv hLeft
  have hInvQT : Q.transpose⁻¹ = Q := Matrix.inv_eq_left_inv hRight
  rw [hDet,Matrix.mul_inv_rev,Matrix.mul_inv_rev,hInvQ,hInvQT]
  simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]

end ShrinkingSpheres
