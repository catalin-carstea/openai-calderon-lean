import Proof.FirstAdjointCorrectionHorizontal
import Proof.CanonicalFirstRadialFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME canonical bounded first-adjoint correction at every genuine grade. -/
def firstFrameAdjointCorrectionAtL (s : ℝ) (d : Data) (y : X) (i : I) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  firstAdjointCorrectionSobolevL s (firstDensityLogCovector d y)
    (scaledFrameLogRadius d.radius d.frame i y) i

lemma firstFrameAdjointCorrectionAtL_zero (d : Data) (y : X) (i : I) :
    firstFrameAdjointCorrectionAtL 0 d y i=firstFrameAdjointCorrectionL d y i :=
  firstFrameAdjointCorrectionL_zero d y i

lemma firstFrameAdjointCorrectionAtL_one (d : Data) (y : X) (i : I) :
    firstFrameAdjointCorrectionAtL 1 d y i=firstFrameAdjointCorrectionSobolevL d y i := rfl

lemma firstFrameAdjointCorrectionAtL_inclusion (s t : ℝ) (hst : t ≤ s)
    (d : Data) (y : X) (i : I) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hst (firstFrameAdjointCorrectionAtL s d y i u)=
      firstFrameAdjointCorrectionAtL t d y i (sphereSobolevInclusionL s t hst u) :=
  firstAdjointCorrectionSobolevL_inclusion s t hst _ _ i u

lemma Admissible.norm_firstFrameAdjointCorrectionAtL_le {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (s : ℝ) {y : X} (hy : y ∈ Y) (i : I) :
    ‖firstFrameAdjointCorrectionAtL s d y i‖ ≤
      6*(K^2*|M ⟨1,by omega⟩|)*radialDriftSobolevBound (-s)*
        (2*(radialDriftSobolevBound s+radialDriftSobolevBound (-s))+1) := by
  have hQ := hd.1.norm_firstDensityLogCovector_le hΩ hK hm (hd.2.1.center_mem hy)
  have hT := hd.scaled_frame_logRadius_bound hf hε hε1 hy i
  change |scaledFrameLogRadius d.radius d.frame i y| ≤ 1 at hT
  have hBs : 0 ≤ radialDriftSobolevBound s := zero_le_one.trans (le_max_left _ _)
  have hBn : 0 ≤ radialDriftSobolevBound (-s) := zero_le_one.trans (le_max_left _ _)
  exact (norm_firstAdjointCorrectionSobolevL_le s _ _ i).trans (by gcongr)

lemma contDiff_radialCorrectionVector : ContDiff ℝ ∞ radialCorrectionVector := by
  apply contDiff_piLp'
  intro i
  exact (ContinuousLinearMap.apply ℝ ℝ (axis i)).contDiff

lemma Admissible.contDiffOn_firstFrameAdjointCorrectionAtL {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (s : ℝ) (i : I) :
    ContDiffOn ℝ ∞ (fun x => firstFrameAdjointCorrectionAtL s d x i) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hq := (hd.1.firstDensityLogCovector_smooth hΩ hK).mono hSub
  have hDrift : ContDiff ℝ ∞ (fun v : X =>
      sphereSobolevRadialDriftAdjointL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics s v) :=
    (contDiff_sphereSobolevRadialDriftAdjointL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics s).of_le (by simp)
  have hB : ContDiffOn ℝ ∞ (fun x => radialCorrectionAdjointSobolevL s (firstDensityLogCovector d x)) Y :=
    hDrift.comp_contDiffOn (contDiff_radialCorrectionVector.comp_contDiffOn hq)
  have ht := contDiffOn_scaledFrameLogRadius hY hd.2.2.2.2.1.1
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
    (fun j => (hd.1.2.2.2.2.2.2.1 j).mono hSub) i
  exact (hB.clm_comp contDiffOn_const).add (ht.smul hB)
end ShrinkingSpheres
