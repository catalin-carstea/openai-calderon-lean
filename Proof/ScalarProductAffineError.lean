import Proof.ExpJetBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres

/-- An affine scalar model times a quadratically Euclidean coefficient retains
    quadratic value and first derivative errors. -/
theorem scalar_product_affine_error {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (q s : V → ℝ) (x : V) (c r δ K A B0 B1 G : ℝ) (L : V →L[ℝ] ℝ)
    (hq : DifferentiableAt ℝ q x) (hs : DifferentiableAt ℝ s x)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hG : 0 ≤ G)
    (hδ : |δ| ≤ 1) (hq0 : |q x| ≤ K) (hq1 : ‖fderiv ℝ q x‖ ≤ G)
    (hqVal : |q x-c-r*L x| ≤ A*r^2)
    (hqDeriv : ‖fderiv ℝ q x-r • L‖ ≤ A*r^2)
    (hsVal : |s x-δ| ≤ B0*r^2) (hsDeriv : ‖fderiv ℝ s x‖ ≤ B1*r^2) :
    |q x*s x-(c+r*L x)*δ| ≤ (A+K*B0)*r^2 ∧
    ‖fderiv ℝ (fun y => q y*s y) x-(r*δ) • L‖ ≤ (A+K*B1+B0*G)*r^2 := by
  constructor
  · have hEq : q x*s x-(c+r*L x)*δ = (q x-c-r*L x)*δ+q x*(s x-δ) := by ring
    rw [hEq]
    calc
      _ ≤ |(q x-c-r*L x)*δ|+|q x*(s x-δ)| := abs_add_le _ _
      _ = |q x-c-r*L x| *|δ|+|q x| *|s x-δ| := by rw [abs_mul,abs_mul]
      _ ≤ (A*r^2)*1+K*(B0*r^2) := by gcongr
      _ = _ := by ring
  · have hProd : HasFDerivAt (fun y => q y*s y)
        (q x • fderiv ℝ s x+s x • fderiv ℝ q x) x := hq.hasFDerivAt.mul hs.hasFDerivAt
    rw [hProd.fderiv]
    have hEq : q x • fderiv ℝ s x+s x • fderiv ℝ q x-(r*δ) • L =
        q x • fderiv ℝ s x+(s x-δ) • fderiv ℝ q x+δ • (fderiv ℝ q x-r • L) := by module
    rw [hEq]
    calc
      _ ≤ ‖q x • fderiv ℝ s x+(s x-δ) • fderiv ℝ q x‖+‖δ • (fderiv ℝ q x-r • L)‖ := norm_add_le _ _
      _ ≤ (‖q x • fderiv ℝ s x‖+‖(s x-δ) • fderiv ℝ q x‖)+‖δ • (fderiv ℝ q x-r • L)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = (|q x| *‖fderiv ℝ s x‖+|s x-δ| *‖fderiv ℝ q x‖)+|δ| *‖fderiv ℝ q x-r • L‖ := by
        simp only [norm_smul,Real.norm_eq_abs]
      _ ≤ (K*(B1*r^2)+(B0*r^2)*G)+1*(A*r^2) := by gcongr
      _ = _ := by ring

end ShrinkingSpheres
