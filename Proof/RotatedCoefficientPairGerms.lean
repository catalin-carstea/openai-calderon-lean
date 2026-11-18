import Proof.RotatedCompactCoefficientGerms
import Proof.OrthogonalAffineCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- A rotated true coefficient, canonical first model, and their SAME affine
residual have compact smooth representatives and joint geometric germs. -/
theorem exists_rotated_coefficient_pair_germs (R B : X → Mat)
    (hB : ContDiff ℝ ∞ B) (hCompact : HasCompactSupport B)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,B =ᶠ[𝓝 z] R)
    (ell : X →L[ℝ] ℝ) (r : ℝ) (i j : I) :
    ∃ A A1 D : ℝ × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ hA1 : ContDiff ℝ ∞ A1,∃ hD : ContDiff ℝ ∞ D,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ t z,z ∉ S → A (t,z) = 0,
      ∃ hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0,∃ hzD : ∀ t z,z ∉ S → D (t,z) = 0,
      (∀ t z,z ∈ Metric.closedBall (0:X) 2 → A =ᶠ[𝓝 (t,z)]
        (fun p : ℝ × X => coordinateRotationPrincipalFamily i j (fun v : ℝ × X => R v.2) ((p.1,0),p.2))) ∧
      (∀ t z,z ∈ Metric.closedBall (0:X) 2 → A1 =ᶠ[𝓝 (t,z)]
        (fun p : ℝ × X => ell (coordinateRotation i j p.1 p.2) • (1:Mat))) ∧
      (∀ p,D p = A p-r • A1 p) ∧
      ∀ t z,z ∈ Metric.closedBall (0:X) 2 → D =ᶠ[𝓝 (t,z)]
        (fun p : ℝ × X => (1:Mat)+coordinateRotationPrincipalFamily i j
          (fun v : ℝ × X => affineMatrixRemainder R 1 r ell v.2) ((p.1,0),p.2)) := by
  let R1 : X → Mat := fun z => ell z • (1:Mat)
  have hR1 : ContDiff ℝ ∞ R1 := ell.contDiff.smul contDiff_const
  obtain ⟨B1,hB1,hSupport1,hRep1⟩ := exists_contDiff_eq_near_compact_of_contDiffOn
    (Metric.closedBall (0:X) 2) Set.univ (isCompact_closedBall _ _) isOpen_univ (subset_univ _)
      R1 hR1.contDiffOn
  obtain ⟨A,hA,L,hzA,hGermA⟩ := exists_rotated_compact_coefficient_germs R B hB hCompact hRep i j
  obtain ⟨A1,hA1,L1,hzA1,hGermA1⟩ := exists_rotated_compact_coefficient_germs R1 B1 hB1 hSupport1 hRep1 i j
  let S := Metric.closedBall (0:X) (max L L1)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hz (t : ℝ) (z : X) (hzS : z ∉ S) : A (t,z) = 0 :=
    hzA t z (fun h => hzS (Metric.closedBall_subset_closedBall (le_max_left _ _) h))
  have hz1 (t : ℝ) (z : X) (hzS : z ∉ S) : A1 (t,z) = 0 :=
    hzA1 t z (fun h => hzS (Metric.closedBall_subset_closedBall (le_max_right _ _) h))
  let D : ℝ × X → Mat := fun p => A p-r • A1 p
  have hD : ContDiff ℝ ∞ D := hA.sub (hA1.const_smul r)
  have hzD (t : ℝ) (z : X) (hzS : z ∉ S) : D (t,z) = 0 := by
    simp only [D,hz t z hzS,hz1 t z hzS,smul_zero,sub_zero]
  have hFirst (t : ℝ) (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) : A1 =ᶠ[𝓝 (t,z)]
      (fun p : ℝ × X => ell (coordinateRotation i j p.1 p.2) • (1:Mat)) := by
    filter_upwards [hGermA1 t z hzB] with p hp
    exact hp.trans (coordinateRotationPrincipalFamily_scalar i j ell p.1 p.2)
  refine ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,hGermA,hFirst,(fun _ => rfl),?_⟩
  intro t z hzB
  filter_upwards [hGermA t z hzB,hFirst t z hzB] with p hp hp1
  change A p-r • A1 p = _
  rw [hp,hp1]
  have hId := rotated_affineMatrixRemainder_identity i j R 1 r ell p.1 p.2
  rw [one_smul] at hId
  rw [hId]
  module

end ShrinkingSpheres
