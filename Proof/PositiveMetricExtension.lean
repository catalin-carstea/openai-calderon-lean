import Proof.PullbackDirichletCoefficient
import Proof.Archive.TauCutoff

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 15
open Set Filter Function
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- A local admitted metric has a globally smooth positive definite extension
    agreeing with it near the selected point. No uniform extension budget is used. -/
theorem Elliptic.exists_positive_global_germ {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    {x : X} (hx : x ∈ Ω) :
    ∃ G : MetricField,(∀ i j,ContDiff ℝ ∞ (fun z => G z i j)) ∧
      (∀ z,(G z).PosDef) ∧ G =ᶠ[𝓝 x] g := by
  have hsub : ({x} : Set X) ⊆ Ω := by simpa only [singleton_subset_iff] using hx
  obtain ⟨χ,hχ,hRange,hOne,_hCompact,hSupp⟩ :=
    (isCompact_singleton (x:=x)).exists_contDiff_cutoff hΩ hsub
  let G : MetricField := fun z => χ z • g z+(1-χ z) • (1:Mat)
  have hSmooth : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ Ω
    · have hMat : ContDiffAt ℝ ∞ g z := contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
        (hg.1 i j).contDiffAt (hΩ.mem_nhds hz)
      exact (hχ.contDiffAt.smul hMat).add
        ((contDiffAt_const.sub hχ.contDiffAt).smul contDiffAt_const)
    · have hOut : z ∈ (tsupport χ)ᶜ := fun hs => hz (hSupp hs)
      have hNear : G =ᶠ[𝓝 z] (fun _ : X => (1:Mat)) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hOut] with w hw
        have hZero : χ w = 0 := notMem_support.mp (fun hs => hw (subset_tsupport χ hs))
        simp only [G,hZero,zero_smul,sub_zero,one_smul,zero_add]
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : X => (1:Mat)) z).congr_of_eventuallyEq hNear
  have hPositive (z : X) : (G z).PosDef := by
    have hR := hRange (mem_range_self z)
    by_cases hZero : χ z = 0
    · simpa only [G,hZero,zero_smul,sub_zero,one_smul,zero_add] using
        (Matrix.PosDef.one : (1:Mat).PosDef)
    · have hχpos : 0 < χ z := lt_of_le_of_ne hR.1 (Ne.symm hZero)
      have hz : z ∈ Ω := hSupp (subset_tsupport χ hZero)
      exact ((hg.posDef hK hz).smul hχpos).add_posSemidef
        ((Matrix.PosSemidef.one : (1:Mat).PosSemidef).smul (sub_nonneg.mpr hR.2))
  refine ⟨G,fun i j => contDiff_pi.mp (contDiff_pi.mp hSmooth i) j,hPositive,?_⟩
  have hxOne := hOne (mem_singleton x)
  filter_upwards [isOpen_interior.mem_nhds hxOne] with z hz
  have hχone : χ z = 1 := by
    have hh : z ∈ χ ⁻¹' {1} := interior_subset hz
    exact hh
  simp only [G,hχone,one_smul,sub_self,zero_smul,add_zero]

end ShrinkingSpheres
