import Proof.GradedMixedConnectionPairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped InnerProductSpace
namespace ShrinkingSpheres
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Covariant differentiation respects the true adjunction in the weak
pairing, with genuine forward/adjoint endpoint graphs. -/
lemma graded_adjoint_covariant_pairing (T R C D : E →L[ℝ] E)
    (J Ch Ah Rh : H →L[ℝ] E) (hT : T.adjoint=T) (hR : R.adjoint= -R)
    (hCh : T.comp Ch=C.comp J) (hAh : T.comp Ah=C.adjoint.comp J)
    (hRh : T.comp Rh=R.comp J) (u v : H) :
    ⟪J u,(D.adjoint.comp J-R.comp Ah+C.adjoint.comp Rh) v⟫_ℝ=
      ⟪J v,(D.comp J-R.comp Ch+C.comp Rh) u⟫_ℝ := by
  have hCancelA := graded_connection_pair_cancel_mixed T R C.adjoint J Ah Rh hT hR hAh hRh u v
  have hCancelC := graded_connection_pair_cancel_mixed T R C J Ch Rh hT hR hCh hRh v u
  have hD : ⟪J u,D.adjoint (J v)⟫_ℝ=⟪J v,D (J u)⟫_ℝ :=
    (D.adjoint_inner_right _ _).trans (real_inner_comm _ _)
  have hC : ⟪J u,C.adjoint (Rh v)⟫_ℝ=⟪Rh v,C (J u)⟫_ℝ :=
    (C.adjoint_inner_right _ _).trans (real_inner_comm _ _)
  have hA : ⟪Rh u,C.adjoint (J v)⟫_ℝ=⟪J v,C (Rh u)⟫_ℝ :=
    (C.adjoint_inner_right _ _).trans (real_inner_comm _ _)
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,inner_add_right,inner_sub_right]
  linarith only [hCancelA,hCancelC,hD,hC,hA]
end ShrinkingSpheres
