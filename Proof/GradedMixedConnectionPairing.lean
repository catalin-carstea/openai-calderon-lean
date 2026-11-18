import Proof.GradedConnectionPairing
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace ShrinkingSpheres
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma graded_connection_pair_cancel_mixed (T R C : E →L[ℝ] E)
    (J Ch Rh : H →L[ℝ] E) (hT : T.adjoint=T) (hR : R.adjoint= -R)
    (hCh : T.comp Ch=C.comp J) (hRh : T.comp Rh=R.comp J) (u v : H) :
    ⟪Rh u,C (J v)⟫_ℝ+⟪J u,R (Ch v)⟫_ℝ=0 := by
  have hFirst : ⟪Rh u,C (J v)⟫_ℝ=⟪R (J u),Ch v⟫_ℝ := by
    calc
      _ = ⟪Rh u,T (Ch v)⟫_ℝ := congrArg (fun z => ⟪Rh u,z⟫_ℝ) (DFunLike.congr_fun hCh.symm v)
      _ = ⟪T (Rh u),Ch v⟫_ℝ := by simpa only [hT] using (T.adjoint_inner_left (Ch v) (Rh u)).symm
      _ = _ := congrArg (fun z => ⟪z,Ch v⟫_ℝ) (DFunLike.congr_fun hRh u)
  rw [hFirst,←R.adjoint_inner_right,hR]
  simp only [ContinuousLinearMap.neg_apply,inner_neg_right,neg_add_cancel]

lemma graded_connection_first_integrand_mixed (T R C : E →L[ℝ] E)
    (J Ch Rh C0 D : H →L[ℝ] E) (hT : T.adjoint=T) (hR : R.adjoint= -R)
    (hCh : T.comp Ch=C.comp J) (hRh : T.comp Rh=R.comp J)
    (hD : D=C0-R.comp Ch+C.comp Rh) (u v du : H) :
    ⟪J du,C (J v)⟫_ℝ+⟪J u,C0 v⟫_ℝ+⟪J u,C (Rh v)⟫_ℝ=
      ⟪J du-Rh u,C (J v)⟫_ℝ+⟪J u,D v⟫_ℝ := by
  have hCancel := graded_connection_pair_cancel_mixed T R C J Ch Rh hT hR hCh hRh u v
  rw [hD]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
    inner_sub_left,inner_add_right,inner_sub_right]
  linarith only [hCancel]
end ShrinkingSpheres
