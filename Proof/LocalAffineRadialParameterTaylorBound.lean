import Proof.AffineRadialParameterTaylorBound
import Proof.LocalMixedParameterJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

def smoothOpenLocus {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F : P → V) : Set P :=
  {x | ∃ U : Set P,IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ F U}

lemma isOpen_smoothOpenLocus {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F : P → V) : IsOpen (smoothOpenLocus F) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨U,hU,hx,hF⟩
  filter_upwards [hU.mem_nhds hx] with y hy
  exact ⟨U,hU,hy,hF⟩

lemma contDiffOn_smoothOpenLocus {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F : P → V) :
    ContDiffOn ℝ ∞ F (smoothOpenLocus F) := by
  rintro x ⟨U,hU,hx,hF⟩
  exact (hF.contDiffAt (hU.mem_nhds hx)).contDiffWithinAt

/-- Local form of affine parameter Taylor on a compact radial segment.
    A smooth ambient extension transfers derivatives by exact germs and
    contributes no quantitative estimate. -/
theorem norm_parameterJetField_sub_affine_of_local_joint_bound
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : P × ℝ → V) (p : P) (n : ℕ) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hLocal : ∀ t : ℝ,|t| ≤ δ → ∃ U : Set (P × ℝ),IsOpen U ∧ (p,t) ∈ U ∧ ContDiffOn ℝ ∞ F U)
    (hBound : ∀ t : ℝ,|t| ≤ δ → ‖iteratedFDeriv ℝ (n+2) F (p,t)‖ ≤ B)
    (r : ℝ) (hr : |r| ≤ δ) :
    ‖parameterJetField n F (p,r)-parameterJetField n F (p,0)-
      r • parameterJetField n (radialFirstDerivative F) (p,0)‖ ≤ B*r^2 := by
  let K : Set (P × ℝ) := ({p}:Set P) ×ˢ Icc (-δ) δ
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have hKU : K ⊆ smoothOpenLocus F := by
    rintro ⟨q,t⟩ ⟨hq,ht⟩
    have hqp : q = p := by simpa only [mem_singleton_iff] using hq
    subst q
    exact hLocal t (abs_le.mpr ht)
  obtain ⟨G,hG,_,hEq⟩ :=
    OAI.AnisotropicCalderon.DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn K
      (smoothOpenLocus F) hK (isOpen_smoothOpenLocus F) hKU F (contDiffOn_smoothOpenLocus F)
  have he (t : ℝ) (ht : |t| ≤ δ) : G =ᶠ[𝓝 (p,t)] F :=
    hEq (p,t) ⟨mem_singleton p,abs_le.mp ht⟩
  have hGJets (t : ℝ) (ht : |t| ≤ δ) : ‖iteratedFDeriv ℝ (n+2) G (p,t)‖ ≤ B := by
    rw [((he t ht).iteratedFDeriv ℝ (n+2)).eq_of_nhds]
    exact hBound t ht
  have hh := norm_parameterJetField_sub_affine_of_joint_bound G hG p n δ B hδ hB hGJets r hr
  have h0 : |(0:ℝ)| ≤ δ := by simpa only [abs_zero] using hδ
  have hJr := (parameterJetField_congr_nhds n (he r hr)).eq_of_nhds
  have hJ0 := (parameterJetField_congr_nhds n (he 0 h0)).eq_of_nhds
  have hRad0 := (parameterJetField_congr_nhds n (radialFirstDerivative_congr_nhds (he 0 h0))).eq_of_nhds
  rwa [hJr,hJ0,hRad0] at hh

end ShrinkingSpheres
