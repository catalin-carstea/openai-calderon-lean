import Proof.Archive.ParametricCoerciveInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The Lax–Milgram functional inverses satisfy the exact resolvent identity. -/
theorem functionalInverse_sub_apply (B B0 : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (hB0 : IsCoercive B0) (ell : StrongDual ℝ V) :
    functionalInverse B ell-functionalInverse B0 ell =
      functionalInverse B ((B0-B) (functionalInverse B0 ell)) := by
  apply eq_functionalInverse B hB
  intro v
  simp only [map_sub,_root_.sub_apply]
  rw [apply_functionalInverse B hB,apply_functionalInverse B0 hB0]

/-- A quantitative continuity bound for the canonical weak solution inverse. -/
theorem norm_functionalInverse_sub_le (B B0 : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (hB0 : IsCoercive B0) :
    ‖functionalInverse B-functionalInverse B0‖ ≤
      ‖functionalInverse B‖*‖B-B0‖*‖functionalInverse B0‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ell
  change ‖functionalInverse B ell-functionalInverse B0 ell‖ ≤ _
  rw [functionalInverse_sub_apply B B0 hB hB0]
  calc
    _ ≤ ‖functionalInverse B‖*‖(B0-B) (functionalInverse B0 ell)‖ :=
      (functionalInverse B).le_opNorm _
    _ ≤ ‖functionalInverse B‖*(‖B0-B‖*‖functionalInverse B0 ell‖) := by
      gcongr; exact (B0-B).le_opNorm _
    _ ≤ ‖functionalInverse B‖*(‖B0-B‖*(‖functionalInverse B0‖*‖ell‖)) := by
      gcongr; exact (functionalInverse B0).le_opNorm ell
    _ = _ := by rw [norm_sub_rev B0 B]; ring

end ShrinkingSpheres
