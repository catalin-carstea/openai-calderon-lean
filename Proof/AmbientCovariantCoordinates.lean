import Proof.HarmonicCovariantDerivative
import Proof.Archive.SmoothAngularCoordinates

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.SmoothSphereFields
open OAI.AnisotropicCalderon.SmoothSphereRotation
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.SmoothAmbientAngularCasimir
open OAI.AnisotropicCalderon.SmoothMovingFrameFields

def ambientCovariantL2 (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y a : X) (A : I → I → ℝ) : SphereL2 :=
  fderiv ℝ (ambientSphereL2 G hG) y a + ∑ i,∑ j,(-(1/2 : ℝ)*A i j) •
    ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) y

lemma harmonicProjection_ambientCovariantL2 (g : MetricField) (e : Frame) (k : ℕ)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y a : X) :
    harmonicProjection k (ambientCovariantL2 G hG y a (frameConnectionCoefficient g e y a)) =
      harmonicCovariantDerivative g e k (fun y => harmonicProjection k (ambientSphereL2 G hG y)) y a := by
  unfold ambientCovariantL2 harmonicCovariantDerivative
  simp only [map_add,map_sum,map_smul]
  have hd := congrArg (fun L => L a) (fderiv_sphereHarmonicCoordinate orthogonalSphereHarmonics
    denseSphereHarmonics k (ambientSphereL2 G hG) y
    ((contDiff_ambientSphereL2 G hG).differentiable (by simp) y))
  change fderiv ℝ (fun y => harmonicProjection k (ambientSphereL2 G hG y)) y a =
    harmonicProjection k (fderiv ℝ (ambientSphereL2 G hG) y a) at hd
  rw [hd]
  unfold harmonicProjection
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun q => (-(1/2 : ℝ)*frameConnectionCoefficient g e y a i j) • q)
    (sphereHarmonicCoordinate_ambientAngularRotation orthogonalSphereHarmonics denseSphereHarmonics k i j G hG y)

lemma sphereL2_sum_ae {J : Type*} (s : Finset J) (f : J → SphereL2) (u : J → UnitSphere → ℝ)
    (h : ∀ j ∈ s,f j =ᵐ[sphereProbability] u j) :
    (∑ j ∈ s,f j) =ᵐ[sphereProbability] (fun v => ∑ j ∈ s,u j v) := by
  apply (Lp.coeFn_fun_finsetSum s f).trans
  have hh := eventuallyEq_sum h
  filter_upwards [hh] with v hv
  simpa only [Finset.sum_apply] using hv

lemma sphereL2_smul_ae (c : ℝ) (f : SphereL2) (u : UnitSphere → ℝ)
    (h : f =ᵐ[sphereProbability] u) : c • f =ᵐ[sphereProbability] (fun v => c*u v) := by
  filter_upwards [Lp.coeFn_smul c f,h] with v hs hu
  simpa only [Pi.smul_apply,smul_eq_mul,hu] using hs

lemma covariantVector_apply (L : X × X →L[ℝ] ℝ) (a : X) (A : I → I → ℝ)
    (hA : ∀ i j,A i j = -A j i) (z : X) :
    L (a,frameAngularVector A z) = L (a,0)+
      ∑ i,∑ j,(-(1/2 : ℝ)*A i j)*L (0,rotationVector i j z) := by
  have hv : (0,frameAngularVector A z) =
      ∑ i,∑ j,(-(1/2 : ℝ)*A i j) • ((0 : X),rotationVector i j z) := by
    have hh := congrArg (ContinuousLinearMap.inr ℝ X X) (frameAngularVector_eq_rotation A hA z)
    simpa only [map_sum,map_smul,ContinuousLinearMap.inr_apply] using hh
  have hp : (a,frameAngularVector A z) = (a,0)+(0,frameAngularVector A z) := by simp
  rw [hp,map_add,hv,map_sum]
  simp only [map_sum,map_smul,smul_eq_mul]

/-- The Hilbert covariant derivative has the actual tangent derivative as its AE representative. -/
lemma ambientCovariantL2_ae (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y a : X) (A : I → I → ℝ)
    (hA : ∀ i j,A i j = -A j i) :
    ambientCovariantL2 G hG y a A =ᵐ[sphereProbability]
      (fun v : UnitSphere => fderiv ℝ G (y,v.val) (a,frameAngularVector A v.val)) := by
  have hrot : (∑ i : I,∑ j : I,(-(1/2 : ℝ)*A i j) •
      ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) y) =ᵐ[sphereProbability]
      (fun v : UnitSphere => ∑ i : I,∑ j : I,(-(1/2 : ℝ)*A i j)*ambientAngularRotation i j G (y,v.val)) := by
    apply sphereL2_sum_ae Finset.univ
    intro i _
    apply sphereL2_sum_ae Finset.univ
    intro j _
    exact sphereL2_smul_ae _ _ _ (ambientSphereL2_ae _ (contDiff_ambientAngularRotation i j G hG) y)
  have hh := (Lp.coeFn_add (fderiv ℝ (ambientSphereL2 G hG) y a) _).trans
    ((fderiv_ambientSphereL2_ae G hG y a).add hrot)
  apply hh.trans
  exact Filter.Eventually.of_forall (fun v => by
    change fderiv ℝ G (y,v.val) (a,0)+∑ i,∑ j,(-(1/2 : ℝ)*A i j)*ambientAngularRotation i j G (y,v.val) = _
    exact (covariantVector_apply (fderiv ℝ G (y,v.val)) a A hA v.val).symm)

lemma ambientCovariantL2_ae_horizontal {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X × X → ℝ) (hF : smoothNear F (bundle Y g)) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G)
    (hrep : ∀ y ∈ Y,∀ v : UnitSphere,G (y,v.val) = F (y,frameVector e y v.val))
    {y : X} (hy : y ∈ Y) (a : X) :
    ambientCovariantL2 G hG y a (frameConnectionCoefficient g e y a) =ᵐ[sphereProbability]
      (fun v : UnitSphere => horizontal g F y (frameVector e y v.val) a) := by
  apply (ambientCovariantL2_ae G hG y a _ (frameConnection_skew hY h hK e he hframe hy a)).trans
  exact Filter.Eventually.of_forall (fun v =>
    (horizontal_eq_standard_representative hY h hK e he hframe F hF G hG hrep hy v a).symm)

/-- Harmonic projection commutes with the actual horizontal connection on arbitrary local
    smooth real data. The horizontal datum is specified only by its actual AE values. -/
theorem harmonicProjection_horizontal {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X × X → ℝ) (hF : smoothNear F (bundle Y g)) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G)
    (hrep : ∀ y ∈ Y,∀ v : UnitSphere,G (y,v.val) = F (y,frameVector e y v.val))
    {y : X} (hy : y ∈ Y) (a : X) (H : SphereL2)
    (hH : H =ᵐ[sphereProbability] (fun v : UnitSphere => horizontal g F y (frameVector e y v.val) a)) (k : ℕ) :
    harmonicProjection k H = harmonicCovariantDerivative g e k
      (fun y => harmonicProjection k (ambientSphereL2 G hG y)) y a := by
  have hW := ambientCovariantL2_ae_horizontal hY h hK e he hframe F hF G hG hrep hy a
  have heq : H = ambientCovariantL2 G hG y a (frameConnectionCoefficient g e y a) :=
    Lp.ext (hH.trans hW.symm)
  rw [heq,harmonicProjection_ambientCovariantL2]

end ShrinkingSpheres
