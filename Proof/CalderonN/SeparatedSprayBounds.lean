module

public import Proof.CalderonN.CoordinateSprayBounds

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/SeparatedSprayBounds.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 15
open Set
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Keeping position and velocity variations separate retains the second speed
    factor when the initial variation is parallel in the center. -/
theorem norm_fderiv_spray_snd_separated (g : (MetricField dim)) (p J : (X dim) × (X dim))
    (hΓ : DifferentiableAt ℝ (connectionBilinear g) p.1) (C D V : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (hΓ0 : ‖connectionBilinear g p.1‖ ≤ C) (hΓ1 : ‖fderiv ℝ (connectionBilinear g) p.1‖ ≤ D)
    (hSpeed : ‖p.2‖ ≤ V) :
    ‖(fderiv ℝ (coordinateGeodesicSpray g) p J).2‖ ≤
      D*V^2*‖J.1‖+2*C*V*‖J.2‖ := by
  rw [show J = (J.1,J.2) from Prod.eta _,fderiv_coordinateGeodesicSpray g p hΓ J.1 J.2]
  change ‖-(connectionBilinear g p.1 p.2 J.2+
    (connectionBilinear g p.1 J.2 p.2+fderiv ℝ (connectionBilinear g) p.1 J.1 p.2 p.2))‖ ≤ _
  rw [norm_neg]
  have h1 : ‖connectionBilinear g p.1 p.2 J.2‖ ≤ C*V*‖J.2‖ :=
    (norm_bilinear_apply_le _ _ _).trans (by gcongr)
  have h2 : ‖connectionBilinear g p.1 J.2 p.2‖ ≤ C*‖J.2‖*V :=
    (norm_bilinear_apply_le _ _ _).trans (by gcongr)
  have h3 : ‖fderiv ℝ (connectionBilinear g) p.1 J.1 p.2 p.2‖ ≤ D*‖J.1‖*V*V :=
    (norm_trilinear_apply_le _ _ _ _).trans (by gcongr)
  exact (norm_add_le _ _).trans ((add_le_add h1 ((norm_add_le _ _).trans
    (add_le_add h2 h3))).trans_eq (by ring))

end CalderonN
