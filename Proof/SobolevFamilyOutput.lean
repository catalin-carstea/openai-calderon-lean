import Proof.CanonicalTestSobolevSections
import Proof.ProductOutputCompletion
import Proof.Localization
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A product-L2 output of an actual H1-to-L2 family on the same canonical
    real/imaginary test sections. The point identities fix its meaning. -/
structure SobolevFamilyOutput {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) where
  realSection : X → SphereL2
  imagSection : X → SphereL2
  realEq : ∀ x ∈ Y,realSection x=(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
    (H x (E.realSobolevSection 1 (by norm_num) x))
  imagEq : ∀ x ∈ Y,imagSection x=(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
    (H x (E.imagSobolevSection 1 (by norm_num) x))
  realization : ProductOutputRealization realSection imagSection Y d.γ E.supportSet

def SobolevFamilyOutput.output {Y : Set X} {d : Data} {φ : Field}
    {E : HarmonicTestExpansion Y d.γ d.frame φ} {H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (P : SobolevFamilyOutput d E H) : Output Y d := P.realization.output

/-- Localization changes no action on the compact input support. Genuine
    finite harmonic representatives then construct the actual product output. -/
theorem exists_sobolevFamilyOutput {Y : Set X} (hY : IsOpen Y) (d : Data)
    (hρ : ContinuousOn (metricDensity d.γ) Y) {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (hH : ContDiffOn ℝ ∞ H Y) :
    Nonempty (SobolevFamilyOutput d E H) := by
  obtain ⟨T,hT,hTC,hEq⟩ := exists_smooth_localization hY E.compactSupportSet E.supportSubset H hH
  let Z := (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
  let U : X → SphereL2 := fun x => Z (T x (E.realSobolevSection 1 (by norm_num) x))
  let V : X → SphereL2 := fun x => Z (T x (E.imagSobolevSection 1 (by norm_num) x))
  have hUS : ContDiff ℝ ∞ U := Z.contDiff.comp (hT.clm_apply (E.contDiff_realSobolevSection 1 (by norm_num)))
  have hVS : ContDiff ℝ ∞ V := Z.contDiff.comp (hT.clm_apply (E.contDiff_imagSobolevSection 1 (by norm_num)))
  have hU0 (x : X) (hx : x ∉ E.supportSet) : U x=0 := by
    change Z (T x (E.realSobolevSection 1 (by norm_num) x))=0
    rw [E.realSobolevSection_zero 1 (by norm_num) hx,map_zero,map_zero]
  have hV0 (x : X) (hx : x ∉ E.supportSet) : V x=0 := by
    change Z (T x (E.imagSobolevSection 1 (by norm_num) x))=0
    rw [E.imagSobolevSection_zero 1 (by norm_num) hx,map_zero,map_zero]
  have hUEq (x : X) (hx : x ∈ Y) : U x=Z (H x (E.realSobolevSection 1 (by norm_num) x)) := by
    by_cases hs : x ∈ E.supportSet
    · change Z (T x _)=Z (H x _)
      rw [(hEq x hs).eq_of_nhds]
    · rw [hU0 x hs,E.realSobolevSection_zero 1 (by norm_num) hs,map_zero,map_zero]
  have hVEq (x : X) (hx : x ∈ Y) : V x=Z (H x (E.imagSobolevSection 1 (by norm_num) x)) := by
    by_cases hs : x ∈ E.supportSet
    · change Z (T x _)=Z (H x _)
      rw [(hEq x hs).eq_of_nhds]
    · rw [hV0 x hs,E.imagSobolevSection_zero 1 (by norm_num) hs,map_zero,map_zero]
  obtain ⟨P⟩ := exists_productOutputRealization hY hρ U V hUS hVS E.supportSet E.compactSupportSet E.supportSubset hU0 hV0
  exact ⟨⟨U,V,hUEq,hVEq,P⟩⟩
end ShrinkingSpheres
