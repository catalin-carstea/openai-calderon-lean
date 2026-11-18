import Proof.LocalRadialFirstJetBound
import Proof.BilinearFamilyJetBounds
import Proof.PositiveAffineFamilyJets
import Proof.PositiveJetCompositionBound
import Proof.NormalFrameMatrixInputJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Multiplying the radial first model by the relative-radius factor retains
    a uniform finite jet budget. The extension is used solely for germs. -/
theorem norm_iteratedFDeriv_relative_first_model_le
    (F : P × ℝ → V) (m : P → V) {U : Set (P × ℝ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (p : P) (hp : (p,0) ∈ U)
    (hm : (fun q => radialFirstDerivative F (q,0)) =ᶠ[𝓝 p] m)
    (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hJets : ∀ j : ℕ,j ≤ N+1 → ‖iteratedFDeriv ℝ j F (p,0)‖ ≤ B)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun q : P × ℝ => (1+q.2) • m q.1) (p,0)‖ ≤
      2^N*((N.factorial:ℝ)*B) := by
  obtain ⟨G,hG,he⟩ := exists_global_smooth_germ_of_open F hU hF hp
  have hRad : (fun q => radialFirstDerivative G (q,0)) =ᶠ[𝓝 p]
      (fun q => radialFirstDerivative F (q,0)) :=
    (radialFirstDerivative_congr_nhds he).comp_tendsto
      (continuousAt_id.prodMk continuousAt_const).tendsto
  have hmSmooth : ContDiffAt ℝ ∞ m p :=
    (((contDiff_radialFirstDerivative G hG).comp
      (contDiff_id.prodMk contDiff_const)).contDiffAt).congr_of_eventuallyEq (hRad.trans hm).symm
  have hmJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j m p‖ ≤ B := by
    rw [← (hm.iteratedFDeriv ℝ j).eq_of_nhds]
    exact (norm_iteratedFDeriv_radialFirst_left_slice_of_open_le F hU hF p 0 hp j).trans
      (hJets (j+1) (by omega))
  let fstL := ContinuousLinearMap.fst ℝ P ℝ
  have hFirst (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (m ∘ fstL) (p,0)‖ ≤ (N.factorial:ℝ)*B := by
    have hh := iteratedFDeriv_comp_common_bound fstL m (p,0) fstL.contDiff.contDiffAt hmSmooth
      N B 1 hB le_rfl hmJets
      (fun k hk _ => norm_iteratedFDeriv_clm_le_one fstL
        (ContinuousLinearMap.norm_fst_le ℝ P ℝ) _ k hk) j hj
    simpa only [one_pow,mul_one] using hh
  have hScalar (j : ℕ) (_hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun q : P × ℝ => (1:ℝ)+q.2) (p,0)‖ ≤ 1 := by
    by_cases hj0 : j = 0
    · subst j
      simp only [norm_iteratedFDeriv_zero,add_zero,norm_one,le_refl]
    · rw [iteratedFDeriv_fixed_add_positive Prod.snd (1:ℝ) (p,0) j (by omega)]
      exact norm_iteratedFDeriv_clm_le_one (ContinuousLinearMap.snd ℝ P ℝ)
        (ContinuousLinearMap.norm_snd_le ℝ P ℝ) _ j (by omega)
  have h := norm_iteratedFDeriv_bilinear_common_bound (ContinuousLinearMap.lsmul ℝ ℝ)
    (fun q : P × ℝ => (1:ℝ)+q.2) (m ∘ fstL) (p,0)
    (contDiffAt_const.add contDiffAt_snd) (hmSmooth.comp (p,0) fstL.contDiff.contDiffAt)
    N 1 ((N.factorial:ℝ)*B) zero_le_one (by positivity) hScalar hFirst n hn
  exact h.trans (by
    calc
      _ = ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)‖*
        (2^N*((N.factorial:ℝ)*B)) := by ring
      _ ≤ 1*(2^N*((N.factorial:ℝ)*B)) := mul_le_mul_of_nonneg_right
        ContinuousLinearMap.opNorm_lsmul_le (by positivity)
      _ = _ := one_mul _)

end ShrinkingSpheres
