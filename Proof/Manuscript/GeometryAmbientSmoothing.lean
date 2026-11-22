module

public import Proof.Manuscript.GeometryClassicalRestriction

import Proof.Manuscript.StereoAmbientKernel
import Mathlib.Tactic

public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Metric CalderonN
open scoped ContDiff Topology

namespace CalderonPaper

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {dim : ℕ}

/-- A joint smooth ambient representation supplies the compact uniform
ordered jets required by the geometric angular smoothing interface. -/
theorem uniformGeometryAngularSmoothing_of_ambient
    {U J : Set P} (hU : IsOpen U) (hJ : IsCompact J) (hJU : J ⊆ U)
    {F : P × (X dim × X dim) → ℂ} (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) :
    UniformGeometryAngularSmoothing U J (fun q z => F (q.1,(q.2,z))) := by
  let O : Set ((P × X dim) × X dim) := (U ×ˢ univ) ×ˢ univ
  refine ⟨⟨O,(hU.prod isOpen_univ).prod isOpen_univ,?_,?_⟩,?_⟩
  · exact fun _ hq => ⟨⟨hq.1.1,mem_univ _⟩,mem_univ _⟩
  · exact hF.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)).contDiffOn
      (fun _ hq => ⟨hq.1.1,mem_univ _⟩)
  · intro l j
    -- The product parameter is (geometry, output angle), differentiated jointly.
    let U' : Set (P × X dim) := U ×ˢ univ
    let J' : Set (P × X dim) := J ×ˢ standardSphere dim
    let H (q : (P × X dim) × (X dim × X dim)) := F (q.1.1,(q.1.2,q.2.2))
    have hU' : IsOpen U' := hU.prod isOpen_univ
    have hJ' : IsCompact J' := hJ.prod (isCompact_sphere _ _)
    have hJ'U' : J' ⊆ U' := fun _ h => ⟨hJU h.1,mem_univ _⟩
    have hH : ContDiffOn ℝ ∞ H (U' ×ˢ univ) :=
      hF.comp (show ContDiff ℝ ∞ (fun q : (P × X dim) × (X dim × X dim) =>
        (q.1.1,(q.1.2,q.2.2))) from by fun_prop).contDiffOn
        (fun _ hw => ⟨hw.1.1,mem_univ _⟩)
    obtain ⟨D,hD,hDB⟩ := exists_compact_mixed_ambient_kernel_jet_bound hU' hJ' hJ'U' hH j 0 l
    refine ⟨D,hD,fun q hq w hw z hz => ?_⟩
    let L := (continuousMultilinearCurryFin0 ℝ (X dim)
      (X dim [×l]→L[ℝ] ℂ)).symm
    let g (p : P × X dim) := iteratedFDeriv ℝ l (fun z' => F (p.1,(p.2,z'))) z
    have h := hDB (q,w) ⟨hq,hw⟩ ⟨w,hw⟩ ⟨z,hz⟩
    have he : ‖iteratedFDeriv ℝ j (L ∘ g) (q,w)‖ ≤ D := by
      simpa only [H, g, L, iteratedFDeriv_zero_eq_comp, Function.comp_def] using h
    rw [L.norm_iteratedFDeriv_comp_left] at he
    exact he

end CalderonPaper
