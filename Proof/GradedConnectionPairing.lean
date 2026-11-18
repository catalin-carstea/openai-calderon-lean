import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace ShrinkingSpheres
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Genuine endpoint squares and skew adjunction cancel connection terms
    without estimating the connection coefficients. -/
lemma graded_connection_pair_cancel (T R C : E →L[ℝ] E)
    (J Ch Rh : H →L[ℝ] E) (hT : T.adjoint=T) (hR : R.adjoint= -R)
    (hCh : T.comp Ch=C.comp J) (hRh : T.comp Rh=R.comp J) (u : H) :
    ⟪Rh u,C (J u)⟫_ℝ+⟪J u,R (Ch u)⟫_ℝ=0 := by
  have hFirst : ⟪Rh u,C (J u)⟫_ℝ=⟪R (J u),Ch u⟫_ℝ := by
    calc
      _ = ⟪Rh u,T (Ch u)⟫_ℝ := congrArg (fun z => ⟪Rh u,z⟫_ℝ) (DFunLike.congr_fun hCh.symm u)
      _ = ⟪T (Rh u),Ch u⟫_ℝ := by simpa only [hT] using (T.adjoint_inner_left (Ch u) (Rh u)).symm
      _ = _ := congrArg (fun z => ⟪z,Ch u⟫_ℝ) (DFunLike.congr_fun hRh u)
  rw [hFirst,← R.adjoint_inner_right,hR]
  simp only [ContinuousLinearMap.neg_apply,inner_neg_right,neg_add_cancel]

/-- The coefficient covariant derivative absorbs exactly the connection
    terms when moving one derivative in a quadratic form. -/
lemma graded_connection_first_integrand (T R C : E →L[ℝ] E)
    (J Ch Rh C0 D : H →L[ℝ] E) (hT : T.adjoint=T) (hR : R.adjoint= -R)
    (hCh : T.comp Ch=C.comp J) (hRh : T.comp Rh=R.comp J)
    (hD : D=C0-R.comp Ch+C.comp Rh) (u v : H) :
    ⟪J v,C (J u)⟫_ℝ+⟪J u,C0 u⟫_ℝ+⟪J u,C (Rh u)⟫_ℝ=
      ⟪J v-Rh u,C (J u)⟫_ℝ+⟪J u,D u⟫_ℝ := by
  have hCancel := graded_connection_pair_cancel T R C J Ch Rh hT hR hCh hRh u
  rw [hD]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
    inner_sub_left,inner_add_right,inner_sub_right]
  linarith only [hCancel]
end ShrinkingSpheres
