import Proof.FrameCorrectionProducts
import Proof.FramePrincipalSmooth
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def firstCorrectionGradeBound (s K M1 : ℝ) : ℝ :=
  6*(K^2*|M1|)*radialDriftSobolevBound (-s)*
    (2*(radialDriftSobolevBound s+radialDriftSobolevBound (-s))+1)

lemma firstCorrectionGradeBound_nonneg (s K M1 : ℝ) : 0 ≤ firstCorrectionGradeBound s K M1 := by
  have hBs : 0 ≤ radialDriftSobolevBound s := zero_le_one.trans (le_max_left _ _)
  have hBn : 0 ≤ radialDriftSobolevBound (-s) := zero_le_one.trans (le_max_left _ _)
  dsimp only [firstCorrectionGradeBound]
  positivity

lemma Admissible.norm_firstFrameAdjointCorrectionAtL_le_gradeBound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (s : ℝ) {y : X} (hy : y ∈ Y) (i : I) :
    ‖firstFrameAdjointCorrectionAtL s d y i‖ ≤ firstCorrectionGradeBound s K (M ⟨1,by omega⟩) :=
  hd.norm_firstFrameAdjointCorrectionAtL_le hΩ hm hK hf hε hε1 s hy i

def principalCorrectionProductL (s : ℝ) (d : Data) (x : X) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  radiusFrameCorrectionProductL s d
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) x

lemma Admissible.norm_principalCorrectionProductL_small {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (s : ℝ) {y : X} (hy : y ∈ Y) :
    ‖principalCorrectionProductL s d y‖ ≤
      81*(K+1)*K^2*(firstCorrectionGradeBound s K (M ⟨1,by omega⟩))^2*ε := by
  have hr : 0 < d.radius y := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hB : 0 ≤ 9*(K+1)*K^2 := by positivity
  exact (norm_radiusFrameCorrectionProductL_small s d _ y hB
    (firstCorrectionGradeBound_nonneg s K (M ⟨1,by omega⟩)) hr.le hrε
    (fun i j => (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).2.1)
    (fun i => hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 s hy i)).trans_eq (by ring)

lemma Admissible.contDiffOn_principalCorrectionProductL {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (s : ℝ) :
    ContDiffOn ℝ ∞ (principalCorrectionProductL s d) Y :=
  hd.contDiffOn_radiusFrameCorrectionProductL hY hΩ hK s _
    (fun i j => hd.contDiffOn_framePrincipalCoefficient (fun _x hx => hd.2.1.center_mem hx) hK i j)

/-- The full principal F/F coefficient on the actual H2 input. -/
lemma principalCorrectionProductL_actual (d : Data) (y : X) (u : SphereSobolev 2) :
    d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
      firstFrameAdjointCorrectionL d y i (sphereSobolevInclusionL 1 0 (by norm_num)
        (firstFrameAdjointCorrectionSobolevL d y j (sphereSobolevInclusionL 2 1 (by norm_num) u))))=
      principalCorrectionProductL 0 d y (sphereSobolevInclusionL 2 0 (by norm_num) u) := by
  have h := frameCorrectionProductL_actual d
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) y
    (sphereSobolevInclusionL 2 1 (by norm_num) u)
  rw [sphereSobolevInclusionL_trans_apply] at h
  exact congrArg (fun v : SphereSobolev 0 => d.radius y • v) h
end ShrinkingSpheres
