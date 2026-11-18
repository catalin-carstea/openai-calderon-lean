import Proof.FrameTensorMatrix
import Proof.ActualSecondTraceAssembly
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

def expandedPrincipalSection (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (U : X → SphereSobolev 2) (V : I → X → SphereSobolev 1) (y : X) : SphereSobolev 0 :=
  d.radius y • ∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
    expandedSecondTraceSection d A G S U V y i j

/-- Contracting the SAME actual second-trace sections gives exactly the
    physical principal trace, before any perturbation coefficient collection. -/
theorem SecondTraceSectionOutput.principal_ae {Y Ω : Set X} (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    {S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    {φ : Field} (hφ : smoothNear φ (bundle Y d.γ)) {L : ℂ →L[ℝ] ℝ}
    {F : X × X → ℝ} {hF : ContDiff ℝ ∞ F}
    (P : SecondTraceSectionOutput Y d A G S φ L F hF) {y : X} (hy : y ∈ Y) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (expandedPrincipalSection d A G S (ambientSobolevSection 2 (by norm_num) F hF)
        (fun k => ambientSobolevSection 1 (by norm_num) (P.representative k) (P.smooth k)) y) =ᵐ[sphereProbability]
      fun w : UnitSphere => L (principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ (y,frameVector d.frame y w.val)) := by
  let q : I → I → ℝ := fun i j => frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j
  have hInner (i : I) := coarseValue_weighted_sum_three (q i) _ _ (fun j => P.second y hy i j)
  have hSum := coarseValue_sum_three _ _ hInner
  have hScaled := coarseValue_smul (d.radius y) _ _ hSum
  apply hScaled.trans
  apply Eventually.of_forall
  intro w
  dsimp only
  rw [hd.principalMovingTrace_frame_matrix hY hSub hK hφ hy
    (frameVector_mem_sphere d.γ d.frame y (hd.1.2.2.2.2.2.2.2 y (hSub hy)) w)]
  simp only [q,map_smul,map_sum,smul_eq_mul]
end ShrinkingSpheres
