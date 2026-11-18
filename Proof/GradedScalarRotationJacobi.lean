import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres

/-- A genuine graded Jacobi identity. All products use the recorded
inclusions and adjacent Sobolev grades; no common endomorphism space is assumed. -/
lemma graded_scalar_rotation_jacobi
    {H M L : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup L] [NormedSpace ℝ L]
    (I1 : H →L[ℝ] M) (I0 : M →L[ℝ] L)
    (Ph Rh Rth : H →L[ℝ] M) (Pl Rtm : M →L[ℝ] L)
    (Qh : H →L[ℝ] H) (Qm Qrm C Cd Cr : M →L[ℝ] M) (Ql Qrl : L →L[ℝ] L)
    (hPair : I0.comp Ph=Pl.comp I1)
    (hIq : Ql.comp I0=I0.comp Qm) (hIqr : Qrl.comp I0=I0.comp Qrm)
    (hC : Ph.comp Qh-Qm.comp Ph=C.comp I1)
    (hClow : Pl.comp Qm-Ql.comp Pl=I0.comp C)
    (hR : Rtm.comp Ph-Pl.comp Rth=I0.comp Rh)
    (hQhigh : Rth.comp Qh-Qm.comp Rth=Qrm.comp I1)
    (hQlow : Rtm.comp Qm-Ql.comp Rtm=I0.comp Qrm)
    (hCd : Rh.comp Qh-Qm.comp Rh=Cd.comp I1)
    (hCr : Pl.comp Qrm-Qrl.comp Pl=I0.comp Cr) (u : H) :
    I0 (C (Rth u)+(Cd+Cr) (I1 u))=Rtm (C (I1 u)) := by
  have hPair' (v : H) : I0 (Ph v)=Pl (I1 v) := DFunLike.congr_fun hPair v
  have hIq' (v : M) : Ql (I0 v)=I0 (Qm v) := DFunLike.congr_fun hIq v
  have hIqr' (v : M) : Qrl (I0 v)=I0 (Qrm v) := DFunLike.congr_fun hIqr v
  have hC' (v : H) : C (I1 v)=Ph (Qh v)-Qm (Ph v) := (DFunLike.congr_fun hC v).symm
  have hClow' (v : M) : Pl (Qm v)=Ql (Pl v)+I0 (C v) :=
    (eq_add_of_sub_eq (DFunLike.congr_fun hClow v)).trans (add_comm _ _)
  have hR' (v : H) : Rtm (Ph v)=Pl (Rth v)+I0 (Rh v) :=
    (eq_add_of_sub_eq (DFunLike.congr_fun hR v)).trans (add_comm _ _)
  have hQhigh' (v : H) : Rth (Qh v)=Qm (Rth v)+Qrm (I1 v) :=
    (eq_add_of_sub_eq (DFunLike.congr_fun hQhigh v)).trans (add_comm _ _)
  have hQlow' (v : M) : Rtm (Qm v)=Ql (Rtm v)+I0 (Qrm v) :=
    (eq_add_of_sub_eq (DFunLike.congr_fun hQlow v)).trans (add_comm _ _)
  have hCd' (v : H) : Rh (Qh v)=Qm (Rh v)+Cd (I1 v) :=
    (eq_add_of_sub_eq (DFunLike.congr_fun hCd v)).trans (add_comm _ _)
  have hCr' (v : M) : Pl (Qrm v)=Qrl (Pl v)+I0 (Cr v) :=
    (eq_add_of_sub_eq (DFunLike.congr_fun hCr v)).trans (add_comm _ _)
  rw [hC' u,map_sub,hR' (Qh u),hQlow' (Ph u),hQhigh' u,hCd' u]
  simp only [map_add]
  rw [hClow' (Rth u),hCr' (I1 u),hR' u]
  simp only [map_add]
  rw [hIq' (Rh u),← hPair' u,hIqr' (Ph u)]
  simp only [_root_.add_apply,map_add]
  abel
end ShrinkingSpheres
