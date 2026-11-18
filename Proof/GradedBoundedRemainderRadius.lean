import Proof.GradedBoundedRemainderCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres
variable {Mid Lo : Type*} [NormedAddCommGroup Mid] [NormedSpace ℝ Mid]
  [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

lemma norm_boundedRemainderCommutatorL_of_radius
    (I0 : Mid →L[ℝ] Lo) (Ga Gb : Mid →L[ℝ] Lo)
    (Za Zb : Mid →L[ℝ] Mid) (Zan Zbn : Lo →L[ℝ] Lo)
    (C a b r : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hI : ‖I0‖ ≤ 1) (hGa : ‖Ga‖ ≤ C*a*r) (hGb : ‖Gb‖ ≤ C*b*r)
    (hZa : ‖Za‖ ≤ C*a*r^2) (hZb : ‖Zb‖ ≤ C*b*r^2)
    (hZan : ‖Zan‖ ≤ C*a*r^2) (hZbn : ‖Zbn‖ ≤ C*b*r^2) :
    ‖boundedRemainderCommutatorL I0 Ga Gb Za Zb Zan Zbn‖ ≤ 6*C^2*a*b*r^2 := by
  have hr2 : r^2 ≤ 1 := by nlinarith
  have hr3 : r^3 ≤ r^2 := by nlinarith [mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)]
  have hr4 : r^4 ≤ r^2 := by nlinarith [mul_le_mul_of_nonneg_left hr2 (sq_nonneg r)]
  have product3 (A B x y : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hy0 : 0 ≤ y)
      (hx : x ≤ C*A*r) (hy : y ≤ C*B*r^2) : x*y ≤ C^2*A*B*r^2 := by
    calc
      _ ≤ (C*A*r)*(C*B*r^2) := mul_le_mul hx hy hy0 (by positivity)
      _ = (C^2*A*B)*r^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr3 (by positivity)
  have product4 (A B x y : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
      (hx : x ≤ C*A*r^2) (hy : y ≤ C*B*r^2) : x*(‖I0‖*y) ≤ C^2*A*B*r^2 := by
    have hIY := mul_le_mul hI hy hy0 (by norm_num : (0:ℝ) ≤ 1)
    calc
      _ ≤ (C*A*r^2)*(1*(C*B*r^2)) := mul_le_mul hx hIY (mul_nonneg (norm_nonneg _) hy0) (by positivity)
      _ = (C^2*A*B)*r^4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr4 (by positivity)
  have h1 := product3 a b ‖Ga‖ ‖Zb‖ ha hb (norm_nonneg _) hGa hZb
  have h2 : ‖Gb‖*‖Za‖ ≤ C^2*a*b*r^2 := (product3 b a ‖Gb‖ ‖Za‖ hb ha (norm_nonneg _) hGb hZa).trans_eq (by ring)
  have h3 : ‖Zan‖*‖Gb‖ ≤ C^2*a*b*r^2 := by
    calc
      _ = ‖Gb‖*‖Zan‖ := mul_comm _ _
      _ ≤ C^2*b*a*r^2 := product3 b a ‖Gb‖ ‖Zan‖ hb ha (norm_nonneg _) hGb hZan
      _ = _ := by ring
  have h4 : ‖Zbn‖*‖Ga‖ ≤ C^2*a*b*r^2 := by
    simpa only [mul_comm ‖Zbn‖] using product3 a b ‖Ga‖ ‖Zbn‖ ha hb (norm_nonneg _) hGa hZbn
  have h5 := product4 a b ‖Zan‖ ‖Zb‖ ha hb (norm_nonneg _) (norm_nonneg _) hZan hZb
  have h6 : ‖Zbn‖*(‖I0‖*‖Za‖) ≤ C^2*a*b*r^2 :=
    (product4 b a ‖Zbn‖ ‖Za‖ hb ha (norm_nonneg _) (norm_nonneg _) hZbn hZa).trans_eq (by ring)
  have hAll := norm_boundedRemainderCommutatorL_le I0 Ga Gb Za Zb Zan Zbn
  linarith only [h1,h2,h3,h4,h5,h6,hAll]
end ShrinkingSpheres
