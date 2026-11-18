import Proof.FischerIntegration
import Proof.Archive.TauCutoff

noncomputable section
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- Multiplication by a cutoff with closed support inside the smooth domain gives a globally
    smooth representative, even when the original function has arbitrary exterior values. -/
lemma contDiff_cutoff_smul {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set D} (hΩ : IsOpen Ω) (η : D → ℝ) (f : D → E)
    (hη : ContDiff ℝ ∞ η) (hf : ContDiffOn ℝ ∞ f Ω) (hsupp : tsupport η ⊆ Ω) :
    ContDiff ℝ ∞ (fun y => η y • f y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ Ω
  · exact hη.contDiffAt.smul (hf.contDiffAt (hΩ.mem_nhds hy))
  · have hout : y ∉ tsupport η := fun ht => hy (hsupp ht)
    apply (contDiffAt_const (c := (0:E))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hout] with x hx
    simp [image_eq_zero_of_notMem_tsupport hx]

/-- A field whose closed support lies inside its smooth domain is globally smooth. -/
lemma contDiff_of_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set X} (hΩ : IsOpen Ω) (f : X → E) (hf : ContDiffOn ℝ ∞ f Ω) (hsupp : tsupport f ⊆ Ω) :
    ContDiff ℝ ∞ f := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ Ω
  · exact hf.contDiffAt (hΩ.mem_nhds hy)
  · have hout : y ∉ tsupport f := fun ht => hy (hsupp ht)
    apply (contDiffAt_const (c := (0:E))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hout] with x hx
    exact image_eq_zero_of_notMem_tsupport hx

/-- A smooth local field admits a smooth global representative agreeing on a neighborhood of
    the compact set needed for integration. The original local field remains the authority. -/
lemma exists_smooth_localization {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω K : Set X} (hΩ : IsOpen Ω) (hK : IsCompact K) (hsub : K ⊆ Ω)
    (f : X → E) (hf : ContDiffOn ℝ ∞ f Ω) :
    ∃ F : X → E, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      ∀ y ∈ K, F =ᶠ[nhds y] f := by
  obtain ⟨η,hη,_,hone,hcompact,hsupp⟩ := hK.exists_contDiff_cutoff hΩ hsub
  refine ⟨fun y => η y • f y, contDiff_cutoff_smul hΩ η f hη hf hsupp, hcompact.smul_right, ?_⟩
  intro y hy
  filter_upwards [isOpen_interior.mem_nhds (hone hy)] with x hx
  have hh : x ∈ η ⁻¹' {1} := interior_subset hx
  change η x = 1 at hh
  simp [hh]

end ShrinkingSpheres
