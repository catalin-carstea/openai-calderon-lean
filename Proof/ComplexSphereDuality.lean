import Proof.SmoothSphereSobolevData
import Proof.AdjointLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
open Set Filter MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma continuousSphere_memLp_complex (F : C(UnitSphere,ℂ)) : MemLp (fun w => F w) 2 sphereProbability :=
  (memLp_congr_ae (ContinuousMap.coeFn_toLp (p:=2) (μ:=sphereProbability) (𝕜:=ℂ) F)).mp
    (Lp.memLp ((ContinuousMap.toLp 2 sphereProbability ℂ) F))

/-- Complex Dirichlet duality gives the physical real L2 pairing of each real
    component, including when the real harmonic derivative is only given by an
    L2 representative. -/
theorem realComponent_pairing_of_complex_integral (F G : UnitSphere → ℂ)
    (hF : MemLp F 2 sphereProbability) (hG : MemLp G 2 sphereProbability)
    (L : ℂ →L[ℝ] ℝ) (q h FR GR : SphereL2) (q0 h0 : UnitSphere → ℝ)
    (hQ : q =ᵐ[sphereProbability] q0) (hH : h =ᵐ[sphereProbability] h0)
    (hFR : FR =ᵐ[sphereProbability] fun w => L (F w))
    (hGR : GR =ᵐ[sphereProbability] fun w => L (G w))
    (hDual : (∫ w : UnitSphere,G w*(q0 w : ℂ) ∂sphereProbability) =
      ∫ w : UnitSphere,F w*(h0 w : ℂ) ∂sphereProbability) :
    ⟪q,GR⟫_ℝ = ⟪h,FR⟫_ℝ := by
  have hMQ : MemLp q0 2 sphereProbability := (memLp_congr_ae hQ).mp (Lp.memLp q)
  have hMH : MemLp h0 2 sphereProbability := (memLp_congr_ae hH).mp (Lp.memLp h)
  have hIntG : Integrable (fun w : UnitSphere => G w*(q0 w : ℂ)) sphereProbability :=
    hG.integrable_mul hMQ.ofReal
  have hIntF : Integrable (fun w : UnitSphere => F w*(h0 w : ℂ)) sphereProbability :=
    hF.integrable_mul hMH.ofReal
  have hL := congrArg L hDual
  rw [← L.integral_comp_comm hIntG,← L.integral_comp_comm hIntF] at hL
  have hLin (z : ℂ) (t : ℝ) : L (z*(t:ℂ)) = t*L z := by
    rw [mul_comm,← Complex.real_smul,map_smul,smul_eq_mul]
  have hIntegrals : (∫ w : UnitSphere,q0 w*L (G w) ∂sphereProbability) =
      ∫ w : UnitSphere,h0 w*L (F w) ∂sphereProbability := by
    simpa only [hLin] using hL
  have hLeft : ⟪q,GR⟫_ℝ = ∫ w : UnitSphere,q0 w*L (G w) ∂sphereProbability := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hQ,hGR] with w hq hg
    simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial,hq,hg]
    ring
  have hRight : ⟪h,FR⟫_ℝ = ∫ w : UnitSphere,h0 w*L (F w) ∂sphereProbability := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH,hFR] with w hh hf
    simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial,hh,hf]
    ring
  exact hLeft.trans (hIntegrals.trans hRight.symm)

end ShrinkingSpheres
