import Proof.ScaledFrozenAdjoint
import Proof.SphereSobolevPhysicalPair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Uniform physical complex fiber estimate for the actual radius-scaled
    frozen adjoint. Its right hand side is exactly the selected H1 norm. -/
theorem uniform_scaled_frozen_adjoint_fiber {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CA : ℝ,0 < η ∧ 0 ≤ CA ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i : I,
      ∀ φ : Field,smoothNear φ (bundle Y d.γ) →
      (d.radius y)^2*fiberSq d.frame y (fun w => adjointField d.adjoint i φ (y,w)) ≤
        CA^2*sobolevSq d.γ d.frame 1 y (fun w => φ (y,w)) := by
  have hTheorem := uniform_scaled_frozen_adjoint hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,CA,hη,hCA,hProduce⟩ := hTheorem
  refine ⟨η,CA,hη,hCA,?_⟩
  intro floor hf ε hε hSmall d hd y hy i φ hφ
  have hHere := hProduce floor hf ε hε hSmall d hd y hy i
  obtain ⟨S,hS,hReal⟩ := hHere
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  obtain ⟨u,hu⟩ := hφ.exists_one_boundary_component hy d.frame hFrame Complex.reCLM
  obtain ⟨v,hv⟩ := hφ.exists_one_boundary_component hy d.frame hFrame Complex.imCLM
  have hOutR := hReal φ hφ Complex.reCLM u hu
  have hOutI := hReal φ hφ Complex.imCLM v hv
  have hR : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (S u) =ᵐ[sphereProbability]
      fun w : UnitSphere => (d.radius y • adjointField d.adjoint i φ (y,frameVector d.frame y w.val)).re := by
    simpa only [Complex.smul_re,smul_eq_mul,Complex.reCLM_apply] using hOutR
  have hI : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (S v) =ᵐ[sphereProbability]
      fun w : UnitSphere => (d.radius y • adjointField d.adjoint i φ (y,frameVector d.frame y w.val)).im := by
    simpa only [Complex.smul_im,smul_eq_mul,Complex.imCLM_apply] using hOutI
  have hBound := fiberSq_operator_bound d.γ d.frame y hFrame (fun w => φ (y,w))
    (fun w => d.radius y • adjointField d.adjoint i φ (y,w)) u v S CA hCA hS hu hv hR hI
  rw [fiberSq_smul_real] at hBound
  exact hBound

end ShrinkingSpheres
