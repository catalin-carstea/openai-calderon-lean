import Proof.SobolevFamilyOutput
import Proof.SupportedOperatorCalculus
import Proof.CompactSupportedLpWeightedSquare
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OperatorForms

lemma memLp_supported_sobolev_operator_section {Y : Set X} (hY : IsOpen Y)
    (U : X → SphereSobolev 1) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0)
    (H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (hH : ContDiffOn ℝ ∞ H Y) (p : ℝ≥0∞) :
    MemLp (fun y => (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (H y (U y))) p (volume.restrict Y) := by
  let Z := (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
  have hOut := Z.contDiff.comp (contDiff_supported_operator_apply U H S hS.isClosed hU h0U
    (fun y hy => hH.contDiffAt (hY.mem_nhds (hSY hy))))
  have h0 (y) (hy : y ∉ S) : Z (H y (U y))=0 := by rw [h0U y hy,map_zero,map_zero]
  exact hOut.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS h0)

lemma SobolevFamilyOutput.sections_memLp {Y : Set X} {d : Data} {φ : Field}
    {E : HarmonicTestExpansion Y d.γ d.frame φ} {H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (P : SobolevFamilyOutput d E H) (hY : IsOpen Y) (hH : ContDiffOn ℝ ∞ H Y) (p : ℝ≥0∞) :
    MemLp P.realSection p (volume.restrict Y) ∧ MemLp P.imagSection p (volume.restrict Y) := by
  have hR := memLp_supported_sobolev_operator_section hY (E.realSobolevSection 1 (by norm_num))
    (E.contDiff_realSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun _ hx => E.realSobolevSection_zero _ _ hx) H hH p
  have hI := memLp_supported_sobolev_operator_section hY (E.imagSobolevSection 1 (by norm_num))
    (E.contDiff_imagSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun _ hx => E.imagSobolevSection_zero _ _ hx) H hH p
  refine ⟨hR.ae_eq ?_,hI.ae_eq ?_⟩
  · filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact (P.realEq y hy).symm
  · filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact (P.imagEq y hy).symm

lemma SobolevFamilyOutput.sections_zero_on_domain {Y : Set X} {d : Data} {φ : Field}
    {E : HarmonicTestExpansion Y d.γ d.frame φ} {H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (P : SobolevFamilyOutput d E H) {y : X} (hy : y ∈ Y) (hs : y ∉ E.supportSet) :
    P.realSection y=0 ∧ P.imagSection y=0 := by
  constructor
  · rw [P.realEq y hy,E.realSobolevSection_zero _ _ hs,map_zero,map_zero]
  · rw [P.imagEq y hy,E.imagSobolevSection_zero _ _ hs,map_zero,map_zero]

end ShrinkingSpheres
