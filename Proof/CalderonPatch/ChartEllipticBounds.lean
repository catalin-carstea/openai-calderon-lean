module

public import Proof.CalderonPatch.ChartCoercivity
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.EnergyForm.Sobolev

import Mathlib.Analysis.Calculus.MeanValue
import Proof.CalderonN.CompactEllipticity
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace TauCeti.PDE
open scoped ContDiff ENNReal Matrix.Norms.Elementwise NNReal

namespace CalderonPatch

open CalderonN (X I Mat MetricField divergenceCoeff contDiffOn_divergenceCoeff)

variable {n : ℕ} [NeZero n]

/-- The genuine chart energy coefficient field is uniformly elliptic
on each compact part of a signed chart. -/
theorem exists_uniformlyEllipticOn_divergenceMatrix {O C : Set (X n)}
    {g : MetricField n} (hg : CalderonN.SmoothMetric O g) (hC : IsCompact C) (hCO : C ⊆ O) :
    ∃ lam Lam : ℝ, UniformlyEllipticOn C (fun z => Matrix.of (divergenceCoeff g z)) lam Lam := by
  let A (z : X n) : Mat n := Matrix.of (divergenceCoeff g z)
  let : CompactSpace C := isCompact_iff_compactSpace.1 hC
  let : NormedAddCommGroup (X n →L[ℝ] X n →L[ℝ] ℝ) := inferInstance
  have hA (i j : I n) : Continuous (fun z : C => A z i j) :=
    continuousOn_iff_continuous_domRestrict.1 ((contDiffOn_divergenceCoeff hg i j).continuousOn.mono hCO)
  have hPos (z : C) (_ : z ∈ (univ : Set C)) : (A z).PosDef :=
    CalderonN.divergenceMatrix_posDef g z (hg.2 _ (hCO z.2))
  obtain ⟨L,hL,hLower⟩ := CalderonN.Elliptic.lower_ellipticity_on_compact hA isCompact_univ hPos
  have hCOnt : ContDiffOn ℝ ∞ A O :=
    contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => contDiffOn_divergenceCoeff hg i j
  obtain ⟨B,hB⟩ := hC.exists_bound_of_continuousOn (hCOnt.continuousOn.matrixBilinearForm.mono hCO)
  refine ⟨L,max L B,hL,le_max_left _ _,fun z hz => ⟨?_,?_⟩⟩
  · intro v
    have h := hLower ⟨z,hz⟩ (mem_univ _) (fun i => v i)
    rw [EuclideanSpace.norm_sq_eq, ← matrixBilinearForm_self, matrixBilinearForm_apply]
    simpa only [Real.norm_eq_abs, sq_abs, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
      using h
  · intro η ξ
    rw [← matrixBilinearForm_apply, ← Real.norm_eq_abs]
    exact ((matrixBilinearForm (A z)).le_opNorm₂ η ξ).trans
      (by gcongr; exact (hB z hz).trans (le_max_right _ _))

/-- On a compact convex part of the chart, the divergence matrix in
operator norm is Lipschitz with a bound from the smooth metric. -/
theorem exists_lipschitzOnWith_divergenceMatrix {O C : Set (X n)} (hO : IsOpen O)
    {g : MetricField n} (hg : CalderonN.SmoothMetric O g) (hC : IsCompact C)
    (hCO : C ⊆ O) (hConv : Convex ℝ C) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (fun z => matrixBilinearForm (Matrix.of (divergenceCoeff g z))) C := by
  let A (z : X n) : Mat n := Matrix.of (divergenceCoeff g z)
  let : NormedAddCommGroup (X n →L[ℝ] X n →L[ℝ] ℝ) := inferInstance
  let B (z : X n) := matrixBilinearForm (A z)
  have hA : ContDiffOn ℝ ∞ A O :=
    contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => contDiffOn_divergenceCoeff hg i j
  have hB : ContDiffOn ℝ ∞ B O :=
    ((matrixBilinearFormLinear (n := I n)).contDiff.comp_contDiffOn hA).congr
      fun _ _ => (matrixBilinearFormLinear_apply _).symm
  have hD := hB.fderiv_of_isOpen hO (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))
  obtain ⟨M,hM⟩ := hC.exists_bound_of_continuousOn (hD.continuousOn.mono hCO)
  refine ⟨⟨max M 0,le_max_right _ _⟩,hConv.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) ?_ ?_⟩
  · exact fun x hx => ((hB.differentiableOn (by simp)) x (hCO hx)).differentiableAt (hO.mem_nhds (hCO hx))
  · intro x hx
    exact_mod_cast (hM x hx).trans (le_max_left M 0)

end CalderonPatch
