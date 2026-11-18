import Proof.PhysicalHilbertProjection
import Proof.Archive.SmoothSphereFields

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 10
open Set MeasureTheory
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A local compact test admits a globally smooth standard-sphere representative with the
    same compact center support. Exterior values of the original field and frame are ignored
    by cutoffs supported strictly inside their actual smooth domains. -/
theorem exists_smooth_standard_representative_of_support {Y : Set X} (hY : IsOpen Y) {g : MetricField} (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : smoothNear φ (bundle Y g))
    (hcpt : ∃ K,IsCompact K ∧ K ⊆ Y ∧ ∀ y ∈ Y \ K,∀ w ∈ sphereAt g y,φ (y,w) = 0) :
    ∃ K : Set X,IsCompact K ∧ K ⊆ Y ∧ ∃ G : X × X → ℂ,ContDiff ℝ ∞ G ∧
      (∀ y ∈ Y,∀ v : UnitSphere,G (y,v.val) = φ (y,frameVector e y v.val)) ∧
      (∀ y ∉ K,∀ v : UnitSphere,G (y,v.val) = 0) := by
  obtain ⟨V,hV,hbundle,hφV⟩ := hφ
  obtain ⟨K,hK,hKY,hzero⟩ := hcpt
  obtain ⟨η,hη,_,hηone,hηcompact,hηsupp⟩ := hK.exists_contDiff_cutoff hY hKY
  obtain ⟨ξ,hξ,_,hξone,hξcompact,hξsupp⟩ := hηcompact.exists_contDiff_cutoff hY hηsupp
  let E : Frame := fun y i => ξ y • e y i
  have hE (i : I) : ContDiff ℝ ∞ (fun y => E y i) := contDiff_cutoff_smul hY ξ (fun y => e y i) hξ (he i) hξsupp
  have hEeq {y : X} (hy : y ∈ tsupport η) (i : I) : E y i = e y i := by
    have hx := interior_subset (hξone hy)
    change ξ y = 1 at hx
    simp only [E,hx,one_smul]
  let P : X × X → X × X := fun z => (z.1,frameVector E z.1 z.2)
  have hP : ContDiff ℝ ∞ P := by
    apply contDiff_fst.prodMk
    exact ContDiff.sum (fun i _ =>
      ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp contDiff_snd).smul ((hE i).comp contDiff_fst))
  let S : Set (X × X) := P '' (tsupport η ×ˢ (Metric.sphere (0 : X) 1))
  have hS : IsCompact S := (hηcompact.prod (isCompact_sphere (0 : X) 1)).image hP.continuous
  have hPframe {y : X} (hy : y ∈ tsupport η) (w : X) : frameVector E y w = frameVector e y w := by
    unfold frameVector
    apply Finset.sum_congr rfl
    intro i _
    rw [hEeq hy i]
  have hSV : S ⊆ V := by
    rintro z ⟨⟨y,w⟩,⟨hy,hw⟩,rfl⟩
    apply hbundle
    change y ∈ Y ∧ frameVector E y w ∈ sphereAt g y
    refine ⟨hηsupp hy,?_⟩
    rw [hPframe hy w]
    exact frameVector_mem_sphere g e y (hframe y (hηsupp hy)) ⟨w,hw⟩
  obtain ⟨χ,hχ,_,hχone,hχcompact,hχsupp⟩ := hS.exists_contDiff_cutoff hV hSV
  let F : X × X → ℂ := fun z => χ z • φ z
  have hF : ContDiff ℝ ∞ F := contDiff_cutoff_smul hV χ φ hχ hφV hχsupp
  let G : X × X → ℂ := fun z => η z.1 • F (P z)
  have hG : ContDiff ℝ ∞ G := (hη.comp contDiff_fst).smul (hF.comp hP)
  have hGform {y : X} (hy : y ∈ tsupport η) (v : UnitSphere) :
      G (y,v.val) = η y • φ (y,frameVector e y v.val) := by
    have hPS : P (y,v.val) ∈ S := ⟨(y,v.val),⟨hy,v.property⟩,rfl⟩
    have hχeq := interior_subset (hχone hPS)
    change χ (P (y,v.val)) = 1 at hχeq
    dsimp only [G,F]
    rw [hχeq,one_smul]
    change η y • φ (y,frameVector E y v.val) = _
    rw [hPframe hy v.val]
  have hGzero (y : X) (hy : y ∉ K) (v : UnitSphere) : G (y,v.val) = 0 := by
    by_cases hs : y ∈ tsupport η
    · rw [hGform hs v,hzero y ⟨hηsupp hs,hy⟩ (frameVector e y v.val)
        (frameVector_mem_sphere g e y (hframe y (hηsupp hs)) v),smul_zero]
    · have hη0 := image_eq_zero_of_notMem_tsupport hs
      simp only [G,hη0,zero_smul]
  refine ⟨K,hK,hKY,G,hG,?_,hGzero⟩
  intro y hy v
  by_cases hKmem : y ∈ K
  · have hηeq := interior_subset (hηone hKmem)
    change η y = 1 at hηeq
    have hs : y ∈ tsupport η := subset_closure (show y ∈ Function.support η by simpa only [Function.mem_support,hηeq] using (one_ne_zero : (1 : ℝ) ≠ 0))
    rw [hGform hs v,hηeq,one_smul]
  · rw [hGzero y hKmem v,hzero y ⟨hy,hKmem⟩ (frameVector e y v.val)
      (frameVector_mem_sphere g e y (hframe y hy) v)]

theorem Test.exists_smooth_standard_representative {Y : Set X} (hY : IsOpen Y) {g : MetricField} (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : Test Y g e φ) :
    ∃ K : Set X,IsCompact K ∧ K ⊆ Y ∧ ∃ G : X × X → ℂ,ContDiff ℝ ∞ G ∧
      (∀ y ∈ Y,∀ v : UnitSphere,G (y,v.val) = φ (y,frameVector e y v.val)) ∧
      (∀ y ∉ K,∀ v : UnitSphere,G (y,v.val) = 0) :=
  exists_smooth_standard_representative_of_support hY e he hframe hφ.1 hφ.2.1

end ShrinkingSpheres
