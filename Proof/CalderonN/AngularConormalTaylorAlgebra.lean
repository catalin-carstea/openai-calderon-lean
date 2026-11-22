module

public import Proof.CalderonN.AngularRadialWeight
public import Proof.CalderonN.SmoothBoundaryHilbert

import Mathlib.Tactic

/-! The radial remainder produces the conormal rotation remainder by
four products on the same sphere. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim]

theorem norm_angular_conormal_remainder_le (i j : Fin dim)
    (C Cθ N Nθ B Qθ W D V E R Δ : SmoothData dim)
    (r c b bθ a u q : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1)
    (hc : 0 ≤ c) (hb : 0 ≤ b) (hbθ : 0 ≤ bθ) (ha : 0 ≤ a) (hu : 0 ≤ u) (hq : 0 ≤ q)
    (ℓθ : X dim →L[ℝ] ℝ)
    (hC : EqOn C.1 (fun z => W.1 z*N.1 z) (standardSphere dim))
    (hCθ : EqOn Cθ.1 (fun z => W.1 z*Nθ.1 z) (standardSphere dim))
    (hD : ∀ z, W.1 z = 1+D.1 z)
    (hV : EqOn V.1 (sphereRotationDerivative i j W.1) (standardSphere dim))
    (hE : ∀ z, V.1 z = r*ℓθ z+E.1 z)
    (hR : EqOn R.1 (fun z => sphereRotationDerivative i j N.1 z-Nθ.1 z-r*Qθ.1 z)
      (standardSphere dim))
    (hΔ : EqOn Δ.1 (fun z => N.1 z-B.1 z) (standardSphere dim))
    (hJet : ∀ z ∈ standardSphere dim, |D.1 z| ≤ c*r ∧ |V.1 z| ≤ c*r ∧ |E.1 z| ≤ c*r^2)
    (hR₀ : ‖smoothSphereLift R.1 R.2‖ ≤ bθ*r^2*a)
    (hΔ₀ : ‖smoothSphereLift Δ.1 Δ.2‖ ≤ b*r*a)
    (hB₀ : ‖smoothSphereLift B.1 B.2‖ ≤ u*a)
    (hQ₀ : ‖smoothSphereLift Qθ.1 Qθ.2‖ ≤ q*a) :
    ∃ F : SmoothData dim,
      EqOn F.1 (fun z => sphereRotationDerivative i j C.1 z-Cθ.1 z-r*(ℓθ z*B.1 z+Qθ.1 z))
        (standardSphere dim) ∧
      ‖smoothSphereLift F.1 F.2‖ ≤ ((1+c)*bθ+c*q+c*u+c*b)*r^2*a := by
  let A1 : SmoothData dim := ⟨fun z => W.1 z*R.1 z,W.2.mul R.2⟩
  let A2 : SmoothData dim := ⟨fun z => r*(D.1 z*Qθ.1 z),contDiff_const.mul (D.2.mul Qθ.2)⟩
  let A3 : SmoothData dim := ⟨fun z => E.1 z*B.1 z,E.2.mul B.2⟩
  let A4 : SmoothData dim := ⟨fun z => V.1 z*Δ.1 z,V.2.mul Δ.2⟩
  let F : SmoothData dim := ⟨fun z => A1.1 z+A2.1 z+A3.1 z+A4.1 z,
    ((A1.2.add A2.2).add A3.2).add A4.2⟩
  have hRot := EqOn.sphereRotationDerivative hC C.2 (W.2.mul N.2) i j
  refine ⟨F,fun z hz => ?_,?_⟩
  · change W.1 z*R.1 z+r*(D.1 z*Qθ.1 z)+E.1 z*B.1 z+V.1 z*Δ.1 z = _
    change _ = sphereRotationDerivative i j C.1 z-Cθ.1 z-r*(ℓθ z*B.1 z+Qθ.1 z)
    rw [hRot hz,sphereRotationDerivative_mul i j W.2 N.2,hCθ hz,hR hz,hΔ hz,← hV hz]
    have hw := hD z
    have hv := hE z
    linear_combination (-r*Qθ.1 z)*hw-(B.1 z)*hv
  have hW (z : X dim) (hz : z ∈ standardSphere dim) : |W.1 z| ≤ 1+c := by
    rw [hD z]
    exact (abs_add_le _ _).trans (by
      rw [abs_one]
      exact add_le_add_right ((hJet z hz).1.trans (by simpa using mul_le_mul_of_nonneg_left hr₁ hc)) _)
  have h1 : ‖smoothSphereLift A1.1 A1.2‖ ≤ (1+c)*(bθ*r^2*a) :=
    (norm_smoothBoundaryLift_mul_le W R (by positivity) hW).trans
      (mul_le_mul_of_nonneg_left hR₀ (by positivity))
  have h2 : ‖smoothSphereLift A2.1 A2.2‖ ≤ r*(c*r*(q*a)) := by
    let G : SmoothData dim := ⟨fun z => D.1 z*Qθ.1 z,D.2.mul Qθ.2⟩
    have hId : smoothSphereLift A2.1 A2.2 = r • smoothSphereLift G.1 G.2 := by
      unfold smoothSphereLift
      rw [← map_smul]
      congr 1
    rw [hId,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    apply mul_le_mul_of_nonneg_left _ hr
    exact (norm_smoothBoundaryLift_mul_le D Qθ (by positivity) (fun z hz => (hJet z hz).1)).trans
      (mul_le_mul_of_nonneg_left hQ₀ (by positivity))
  have h3 : ‖smoothSphereLift A3.1 A3.2‖ ≤ c*r^2*(u*a) :=
    (norm_smoothBoundaryLift_mul_le E B (by positivity) (fun z hz => (hJet z hz).2.2)).trans
      (mul_le_mul_of_nonneg_left hB₀ (by positivity))
  have h4 : ‖smoothSphereLift A4.1 A4.2‖ ≤ c*r*(b*r*a) :=
    (norm_smoothBoundaryLift_mul_le V Δ (by positivity) (fun z hz => (hJet z hz).2.1)).trans
      (mul_le_mul_of_nonneg_left hΔ₀ (by positivity))
  dsimp only [F]
  rw [smoothSphereLift_add _ _ ((A1.2.add A2.2).add A3.2) A4.2,
    smoothSphereLift_add _ _ (A1.2.add A2.2) A3.2,smoothSphereLift_add _ _ A1.2 A2.2]
  calc
    _ ≤ ‖smoothSphereLift A1.1 A1.2‖ + ‖smoothSphereLift A2.1 A2.2‖ +
        ‖smoothSphereLift A3.1 A3.2‖ + ‖smoothSphereLift A4.1 A4.2‖ :=
      (norm_add_le _ _).trans (add_le_add_left
        ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)) _)
    _ ≤ _ := (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq (by ring)

end CalderonN
