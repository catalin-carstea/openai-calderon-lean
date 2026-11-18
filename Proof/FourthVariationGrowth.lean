import Proof.LocalFourthFlowVariation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff
namespace ShrinkingSpheres
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def fourthVariationForcingBudget (B C D J S T : ℝ) : ℝ :=
  D*J^4+6*C*J^2*S+3*B*S^2+4*B*J*T

/-- The genuine fourth variational RHS has the required Gronwall growth
    bound, with all15 terms counted and the linear unknown kept separate. -/
theorem norm_fourthParameterVariationRhs_le (F : E × ℝ → G) (V : G → G)
    (q : E × ℝ) (h k l m : E) (A B C D J0 S0 T0 : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hJ0 : 0 ≤ J0) (hS0 : 0 ≤ S0) (hT0 : 0 ≤ T0)
    (hV1 : ‖fderiv ℝ V (F q)‖ ≤ A)
    (hV2 : ∀ u v,‖fderiv ℝ (fderiv ℝ V) (F q) u v‖ ≤ B*‖u‖*‖v‖)
    (hV3 : ∀ u v w,‖fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F q) u v w‖ ≤ C*‖u‖*‖v‖*‖w‖)
    (hV4 : ∀ u v w z,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ V))) (F q) u v w z‖ ≤ D*‖u‖*‖v‖*‖w‖*‖z‖)
    (hJ : ∀ a,‖firstParameterVariation F a q‖ ≤ J0*‖a‖)
    (hS : ∀ a b,‖secondParameterVariation F a b q‖ ≤ S0*‖a‖*‖b‖)
    (hT : ∀ a b c,‖thirdParameterVariation F a b c q‖ ≤ T0*‖a‖*‖b‖*‖c‖) :
    ‖fourthParameterVariationRhs F V h k l m q‖ ≤ A*‖fourthParameterVariation F h k l m q‖+
      fourthVariationForcingBudget B C D J0 S0 T0*‖h‖*‖k‖*‖l‖*‖m‖ := by
  let t0 := fderiv ℝ V (F q) (fourthParameterVariation F h k l m q)
  let t1 := fderiv ℝ (fderiv ℝ V) (F q) (firstParameterVariation F m q) (thirdParameterVariation F h k l q)
  let t2 := fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F q) (firstParameterVariation F m q) (firstParameterVariation F l q) (secondParameterVariation F h k q)
  let t3 := fderiv ℝ (fderiv ℝ V) (F q) (secondParameterVariation F l m q) (secondParameterVariation F h k q)
  let t4 := fderiv ℝ (fderiv ℝ V) (F q) (firstParameterVariation F l q) (thirdParameterVariation F h k m q)
  let t5 := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ V))) (F q) (firstParameterVariation F m q) (firstParameterVariation F l q) (firstParameterVariation F k q) (firstParameterVariation F h q)
  let t6 := fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F q) (secondParameterVariation F l m q) (firstParameterVariation F k q) (firstParameterVariation F h q)
  let t7 := fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F q) (firstParameterVariation F l q) (secondParameterVariation F k m q) (firstParameterVariation F h q)
  let t8 := fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F q) (firstParameterVariation F l q) (firstParameterVariation F k q) (secondParameterVariation F h m q)
  let t9 := fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F q) (firstParameterVariation F m q) (secondParameterVariation F k l q) (firstParameterVariation F h q)
  let t10 := fderiv ℝ (fderiv ℝ V) (F q) (thirdParameterVariation F k l m q) (firstParameterVariation F h q)
  let t11 := fderiv ℝ (fderiv ℝ V) (F q) (secondParameterVariation F k l q) (secondParameterVariation F h m q)
  let t12 := fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F q) (firstParameterVariation F m q) (firstParameterVariation F k q) (secondParameterVariation F h l q)
  let t13 := fderiv ℝ (fderiv ℝ V) (F q) (secondParameterVariation F k m q) (secondParameterVariation F h l q)
  let t14 := fderiv ℝ (fderiv ℝ V) (F q) (firstParameterVariation F k q) (thirdParameterVariation F h l m q)
  have h0 : ‖t0‖ ≤ A*‖fourthParameterVariation F h k l m q‖ :=
    ((fderiv ℝ V (F q)).le_opNorm _).trans (mul_le_mul_of_nonneg_right hV1 (norm_nonneg _))
  have h1 : ‖t1‖ ≤ (B*J0*T0)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t1‖ ≤ B*(J0*‖m‖)*(T0*‖h‖*‖k‖*‖l‖) :=
      (hV2 (firstParameterVariation F m q) (thirdParameterVariation F h k l q)).trans (by
        gcongr
        · exact hJ m
        · exact hT h k l
      )
    exact hb.trans_eq (by ring)
  have h2 : ‖t2‖ ≤ (C*J0^2*S0)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t2‖ ≤ C*(J0*‖m‖)*(J0*‖l‖)*(S0*‖h‖*‖k‖) :=
      (hV3 (firstParameterVariation F m q) (firstParameterVariation F l q) (secondParameterVariation F h k q)).trans (by
        gcongr
        · exact hJ m
        · exact hJ l
        · exact hS h k
      )
    exact hb.trans_eq (by ring)
  have h3 : ‖t3‖ ≤ (B*S0^2)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t3‖ ≤ B*(S0*‖l‖*‖m‖)*(S0*‖h‖*‖k‖) :=
      (hV2 (secondParameterVariation F l m q) (secondParameterVariation F h k q)).trans (by
        gcongr
        · exact hS l m
        · exact hS h k
      )
    exact hb.trans_eq (by ring)
  have h4 : ‖t4‖ ≤ (B*J0*T0)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t4‖ ≤ B*(J0*‖l‖)*(T0*‖h‖*‖k‖*‖m‖) :=
      (hV2 (firstParameterVariation F l q) (thirdParameterVariation F h k m q)).trans (by
        gcongr
        · exact hJ l
        · exact hT h k m
      )
    exact hb.trans_eq (by ring)
  have h5 : ‖t5‖ ≤ (D*J0^4)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t5‖ ≤ D*(J0*‖m‖)*(J0*‖l‖)*(J0*‖k‖)*(J0*‖h‖) :=
      (hV4 (firstParameterVariation F m q) (firstParameterVariation F l q) (firstParameterVariation F k q) (firstParameterVariation F h q)).trans (by
        gcongr
        · exact hJ m
        · exact hJ l
        · exact hJ k
        · exact hJ h
      )
    exact hb.trans_eq (by ring)
  have h6 : ‖t6‖ ≤ (C*J0^2*S0)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t6‖ ≤ C*(S0*‖l‖*‖m‖)*(J0*‖k‖)*(J0*‖h‖) :=
      (hV3 (secondParameterVariation F l m q) (firstParameterVariation F k q) (firstParameterVariation F h q)).trans (by
        gcongr
        · exact hS l m
        · exact hJ k
        · exact hJ h
      )
    exact hb.trans_eq (by ring)
  have h7 : ‖t7‖ ≤ (C*J0^2*S0)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t7‖ ≤ C*(J0*‖l‖)*(S0*‖k‖*‖m‖)*(J0*‖h‖) :=
      (hV3 (firstParameterVariation F l q) (secondParameterVariation F k m q) (firstParameterVariation F h q)).trans (by
        gcongr
        · exact hJ l
        · exact hS k m
        · exact hJ h
      )
    exact hb.trans_eq (by ring)
  have h8 : ‖t8‖ ≤ (C*J0^2*S0)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t8‖ ≤ C*(J0*‖l‖)*(J0*‖k‖)*(S0*‖h‖*‖m‖) :=
      (hV3 (firstParameterVariation F l q) (firstParameterVariation F k q) (secondParameterVariation F h m q)).trans (by
        gcongr
        · exact hJ l
        · exact hJ k
        · exact hS h m
      )
    exact hb.trans_eq (by ring)
  have h9 : ‖t9‖ ≤ (C*J0^2*S0)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t9‖ ≤ C*(J0*‖m‖)*(S0*‖k‖*‖l‖)*(J0*‖h‖) :=
      (hV3 (firstParameterVariation F m q) (secondParameterVariation F k l q) (firstParameterVariation F h q)).trans (by
        gcongr
        · exact hJ m
        · exact hS k l
        · exact hJ h
      )
    exact hb.trans_eq (by ring)
  have h10 : ‖t10‖ ≤ (B*J0*T0)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t10‖ ≤ B*(T0*‖k‖*‖l‖*‖m‖)*(J0*‖h‖) :=
      (hV2 (thirdParameterVariation F k l m q) (firstParameterVariation F h q)).trans (by
        gcongr
        · exact hT k l m
        · exact hJ h
      )
    exact hb.trans_eq (by ring)
  have h11 : ‖t11‖ ≤ (B*S0^2)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t11‖ ≤ B*(S0*‖k‖*‖l‖)*(S0*‖h‖*‖m‖) :=
      (hV2 (secondParameterVariation F k l q) (secondParameterVariation F h m q)).trans (by
        gcongr
        · exact hS k l
        · exact hS h m
      )
    exact hb.trans_eq (by ring)
  have h12 : ‖t12‖ ≤ (C*J0^2*S0)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t12‖ ≤ C*(J0*‖m‖)*(J0*‖k‖)*(S0*‖h‖*‖l‖) :=
      (hV3 (firstParameterVariation F m q) (firstParameterVariation F k q) (secondParameterVariation F h l q)).trans (by
        gcongr
        · exact hJ m
        · exact hJ k
        · exact hS h l
      )
    exact hb.trans_eq (by ring)
  have h13 : ‖t13‖ ≤ (B*S0^2)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t13‖ ≤ B*(S0*‖k‖*‖m‖)*(S0*‖h‖*‖l‖) :=
      (hV2 (secondParameterVariation F k m q) (secondParameterVariation F h l q)).trans (by
        gcongr
        · exact hS k m
        · exact hS h l
      )
    exact hb.trans_eq (by ring)
  have h14 : ‖t14‖ ≤ (B*J0*T0)*‖h‖*‖k‖*‖l‖*‖m‖ := by
    have hb : ‖t14‖ ≤ B*(J0*‖k‖)*(T0*‖h‖*‖l‖*‖m‖) :=
      (hV2 (firstParameterVariation F k q) (thirdParameterVariation F h l m q)).trans (by
        gcongr
        · exact hJ k
        · exact hT h l m
      )
    exact hb.trans_eq (by ring)
  change ‖t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14‖ ≤ _
  have hSum : ‖t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14‖ ≤ ‖t0‖ + ‖t1‖ + ‖t2‖ + ‖t3‖ + ‖t4‖ + ‖t5‖ + ‖t6‖ + ‖t7‖ + ‖t8‖ + ‖t9‖ + ‖t10‖ + ‖t11‖ + ‖t12‖ + ‖t13‖ + ‖t14‖ :=
    ((norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13) t14).trans (add_le_add ((norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12) t13).trans (add_le_add ((norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11) t12).trans (add_le_add ((norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10) t11).trans (add_le_add ((norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9) t10).trans (add_le_add ((norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8) t9).trans (add_le_add ((norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7) t8).trans (add_le_add ((norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6) t7).trans (add_le_add ((norm_add_le (t0 + t1 + t2 + t3 + t4 + t5) t6).trans (add_le_add ((norm_add_le (t0 + t1 + t2 + t3 + t4) t5).trans (add_le_add ((norm_add_le (t0 + t1 + t2 + t3) t4).trans (add_le_add ((norm_add_le (t0 + t1 + t2) t3).trans (add_le_add ((norm_add_le (t0 + t1) t2).trans (add_le_add ((norm_add_le (t0) t1).trans (add_le_add le_rfl le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl))
  refine hSum.trans ?_
  dsimp only [fourthVariationForcingBudget]
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14]

end ShrinkingSpheres
