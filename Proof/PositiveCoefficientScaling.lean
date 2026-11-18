import Proof.PullbackDirichletCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- Positive constant scaling preserves actual coefficient ellipticity,
    with both ellipticity constants scaled by exactly the same scalar. -/
theorem uniformlyEllipticOn_positive_const_smul {Ω : Set X} {a : X → Mat} {lam Lam : ℝ}
    (h : TauCeti.PDE.UniformlyEllipticOn Ω a lam Lam) (c : ℝ) (hc : 0 < c) :
    TauCeti.PDE.UniformlyEllipticOn Ω (fun z => c • a z) (c*lam) (c*Lam) := by
  refine ⟨mul_pos hc h.1,mul_le_mul_of_nonneg_left h.2.1 hc.le,?_⟩
  intro z hz
  constructor
  · intro ξ
    rw [Matrix.toQuadraticForm'_smul,_root_.smul_apply,smul_eq_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ((h.2.2 hz).1 ξ) hc.le
  · intro η ξ
    rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,abs_mul,abs_of_pos hc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ((h.2.2 hz).2 η ξ) hc.le

end ShrinkingSpheres
