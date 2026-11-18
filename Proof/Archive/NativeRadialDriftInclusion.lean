/- Adopted from the selected ZIP, ActualFirstCorrectionSobolevFamilies.lean.
   The four generic Sobolev inclusion lemmas only; proof bodies preserved.
   Specialized reference families and parameter compactness bounds omitted. -/
import Proof.Archive.SphereSobolevCoordinateInclusion
import Proof.Archive.SphereSobolevRadialDriftAdjoint
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SphereHilbertDecomposition BoundedAngularShift BoundedSpectralMultiplier
  OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local irreducible] sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL

lemma sphereSobolevInclusionL_radialDrift_single
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hts : t ≤ s) (d : R3) (k : ℕ) (a : harmonicSphereSubspace k) :
    sphereSobolevInclusionL s t hts
      (sphereSobolevRadialDriftL hF hO hD s d (sphereSobolevSingleL s k a)) =
      sphereSobolevRadialDriftL hF hO hD t d
        (sphereSobolevInclusionL s t hts (sphereSobolevSingleL s k a)) := by
  cases k with
  | zero => rw [sphereSobolevRadialDriftL_constant,map_zero,
      sphereSobolevInclusionL_single,sphereSobolevRadialDriftL_constant]
  | succ k =>
    let I := sphereSobolevInclusionL s t hts
    calc
      _ = I (sphereSobolevSingleL s k (radialDriftBlockL hF d k a)) :=
        congrArg I (sphereSobolevRadialDriftL_single hF hO hD s d k a)
      _ = sphereSobolevSingleL t k (radialDriftBlockL hF d k a) :=
        sphereSobolevInclusionL_single s t hts k (radialDriftBlockL hF d k a)
      _ = sphereSobolevRadialDriftL hF hO hD t d (sphereSobolevSingleL t (k+1) a) :=
        (sphereSobolevRadialDriftL_single hF hO hD t d k a).symm
      _ = _ := congrArg (sphereSobolevRadialDriftL hF hO hD t d)
        (sphereSobolevInclusionL_single s t hts (k+1) a).symm


lemma sphereSobolevInclusionL_radialDrift
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hts : t ≤ s) (d : R3) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hts (sphereSobolevRadialDriftL hF hO hD s d u) =
      sphereSobolevRadialDriftL hF hO hD t d (sphereSobolevInclusionL s t hts u) := by
  let A : SphereSobolev s →L[ℝ] SphereSobolev t :=
    (sphereSobolevInclusionL s t hts).comp (sphereSobolevRadialDriftL hF hO hD s d)
  let B : SphereSobolev s →L[ℝ] SphereSobolev t :=
    (sphereSobolevRadialDriftL hF hO hD t d).comp (sphereSobolevInclusionL s t hts)
  have hn (n : ℕ) : A (sphereSobolevPartialSum s n u) = B (sphereSobolevPartialSum s n u) := by
    unfold sphereSobolevPartialSum
    rw [map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact sphereSobolevInclusionL_radialDrift_single hF hO hD s t hts d k
      (sphereSobolevCoefficientL s k u)
  have hA : Tendsto (fun n : ℕ => A (sphereSobolevPartialSum s n u)) atTop (𝓝 (A u)) :=
    (A.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum s u)
  have hB : Tendsto (fun n : ℕ => A (sphereSobolevPartialSum s n u)) atTop (𝓝 (B u)) := by
    simp_rw [hn]
    exact (B.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum s u)
  exact tendsto_nhds_unique hA hB

lemma sphereSobolevInclusionL_radialDriftAdjoint_single
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hts : t ≤ s) (d : R3) (k : ℕ) (a : harmonicSphereSubspace k) :
    sphereSobolevInclusionL s t hts
      (sphereSobolevRadialDriftAdjointL hF hO hD s d (sphereSobolevSingleL s k a)) =
      sphereSobolevRadialDriftAdjointL hF hO hD t d
        (sphereSobolevInclusionL s t hts (sphereSobolevSingleL s k a)) := by
  rw [sphereSobolevRadialDriftAdjointL_single,sphereSobolevInclusionL_single,
    sphereSobolevInclusionL_single,sphereSobolevRadialDriftAdjointL_single]

lemma sphereSobolevInclusionL_radialDriftAdjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hts : t ≤ s) (d : R3) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hts (sphereSobolevRadialDriftAdjointL hF hO hD s d u) =
      sphereSobolevRadialDriftAdjointL hF hO hD t d (sphereSobolevInclusionL s t hts u) := by
  let A : SphereSobolev s →L[ℝ] SphereSobolev t :=
    (sphereSobolevInclusionL s t hts).comp (sphereSobolevRadialDriftAdjointL hF hO hD s d)
  let B : SphereSobolev s →L[ℝ] SphereSobolev t :=
    (sphereSobolevRadialDriftAdjointL hF hO hD t d).comp (sphereSobolevInclusionL s t hts)
  have hn (n : ℕ) : A (sphereSobolevPartialSum s n u) = B (sphereSobolevPartialSum s n u) := by
    unfold sphereSobolevPartialSum
    rw [map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact sphereSobolevInclusionL_radialDriftAdjoint_single hF hO hD s t hts d k
      (sphereSobolevCoefficientL s k u)
  have hA : Tendsto (fun n : ℕ => A (sphereSobolevPartialSum s n u)) atTop (𝓝 (A u)) :=
    (A.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum s u)
  have hB : Tendsto (fun n : ℕ => A (sphereSobolevPartialSum s n u)) atTop (𝓝 (B u)) := by
    simp_rw [hn]
    exact (B.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum s u)
  exact tendsto_nhds_unique hA hB

end OAI.AnisotropicCalderon.SphereHarmonic
