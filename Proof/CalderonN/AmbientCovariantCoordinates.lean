module

public import Proof.CalderonN.HarmonicCovariantDerivative
public import Proof.CalderonN.SmoothAmbientAngularCasimir

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ContDiff
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields
open OAI.AnisotropicCalderon.SmoothSphereRotation

def ambientCovariantL2 (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G) (y a : (X N)) (A : (I N) → (I N) → ℝ) : (SphereL2 N) :=
  fderiv ℝ (ambientSphereL2 G hG) y a + ∑ i,∑ j,(-(1/2 : ℝ)*A i j) •
    ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) y

lemma harmonicProjection_ambientCovariantL2 (g : (MetricField N)) (e : (Frame N)) (k : ℕ)
    (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G) (y a : (X N)) :
    harmonicProjection k (ambientCovariantL2 G hG y a (frameConnectionCoefficient g e y a)) =
      harmonicCovariantDerivative g e k (fun y => harmonicProjection k (ambientSphereL2 G hG y)) y a := by
  unfold ambientCovariantL2 harmonicCovariantDerivative
  simp only [map_add,map_sum,map_smul]
  have hd := ((harmonicProjection k).hasFDerivAt.comp y
    ((contDiff_ambientSphereL2 G hG).differentiable (by simp) y).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => harmonicProjection k (ambientSphereL2 G hG y)) y = _ at hd
  rw [hd, ContinuousLinearMap.comp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have he := ambientAngularRotation_slice i j G hG y
  have hrot : ambientSphereL2 (ambientAngularRotation i j G)
      (contDiff_ambientAngularRotation i j G hG) y =
      smoothSphereLift (sphereRotationDerivative i j (fun z => G (y,z)))
        (contDiff_sphereRotationDerivative i j _ (contDiff_angular_slice G hG y)) := by
    rw [ambientSphereL2_eq_smoothSphereLift]
    unfold smoothSphereLift
    congr 1
    ext z
    exact congrFun he z.val
  rw [hrot, ambientSphereL2_eq_smoothSphereLift]
  exact harmonicProjection_sphereRotationDerivative k i j
    (fun z => G (y,z)) (contDiff_angular_slice G hG y)

lemma sphereL2_sum_ae {J : Type*} (s : Finset J) (f : J → (SphereL2 N)) (u : J → (UnitSphere N) → ℝ)
    (h : ∀ j ∈ s,f j =ᵐ[(sphereProbability N)] u j) :
    (∑ j ∈ s,f j) =ᵐ[(sphereProbability N)] (fun v => ∑ j ∈ s,u j v) := by
  apply (Lp.coeFn_fun_finsetSum s f).trans
  have hh := eventuallyEq_sum h
  filter_upwards [hh] with v hv
  change (∑ j ∈ s, ((f j : (SphereL2 N)) : (UnitSphere N) → ℝ)) v = (∑ j ∈ s, u j) v at hv
  simpa only [Finset.sum_apply] using hv

lemma sphereL2_smul_ae (c : ℝ) (f : (SphereL2 N)) (u : (UnitSphere N) → ℝ)
    (h : f =ᵐ[(sphereProbability N)] u) : c • f =ᵐ[(sphereProbability N)] (fun v => c*u v) := by
  filter_upwards [Lp.coeFn_smul c f,h] with v hs hu
  change (c • f) v = (c • (f : (UnitSphere N) → ℝ)) v at hs
  change f v = u v at hu
  rw [hs]
  change c * f v = c * u v
  rw [hu]

lemma covariantVector_apply (L : (X N) × (X N) →L[ℝ] ℝ) (a : (X N)) (A : (I N) → (I N) → ℝ)
    (hA : ∀ i j,A i j = -A j i) (z : (X N)) :
    L (a,frameAngularVector A z) = L (a,0)+
      ∑ i,∑ j,(-(1/2 : ℝ)*A i j)*L (0,rotationVector i j z) := by
  have hv : (0,frameAngularVector A z) =
      ∑ i,∑ j,(-(1/2 : ℝ)*A i j) • ((0 : (X N)),rotationVector i j z) := by
    have hh := congrArg (ContinuousLinearMap.inr ℝ (X N) (X N)) (frameAngularVector_eq_rotation A hA z)
    simpa only [map_sum,map_smul,ContinuousLinearMap.inr_apply] using hh
  have hp : (a,frameAngularVector A z) = (a,0)+(0,frameAngularVector A z) := by simp
  rw [hp,map_add,hv,map_sum]
  simp only [map_sum,map_smul,smul_eq_mul]

/-- The Hilbert covariant derivative has the actual tangent derivative as its AE representative. -/
lemma ambientCovariantL2_ae (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G) (y a : (X N)) (A : (I N) → (I N) → ℝ)
    (hA : ∀ i j,A i j = -A j i) :
    ambientCovariantL2 G hG y a A =ᵐ[(sphereProbability N)]
      (fun v : (UnitSphere N) => fderiv ℝ G (y,v.val) (a,frameAngularVector A v.val)) := by
  have hrot : (∑ i : (I N),∑ j : (I N),(-(1/2 : ℝ)*A i j) •
      ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) y) =ᵐ[(sphereProbability N)]
      (fun v : (UnitSphere N) => ∑ i : (I N),∑ j : (I N),(-(1/2 : ℝ)*A i j)*ambientAngularRotation i j G (y,v.val)) := by
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

lemma ambientCovariantL2_ae_horizontal {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : (X N) × (X N) → ℝ) (hF : smoothNear F (bundle Y g)) (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G)
    (hrep : ∀ y ∈ Y,∀ v : (UnitSphere N),G (y,v.val) = F (y,frameVector e y v.val))
    {y : (X N)} (hy : y ∈ Y) (a : (X N)) :
    ambientCovariantL2 G hG y a (frameConnectionCoefficient g e y a) =ᵐ[(sphereProbability N)]
      (fun v : (UnitSphere N) => horizontal g F y (frameVector e y v.val) a) := by
  apply (ambientCovariantL2_ae G hG y a _ (frameConnection_skew hY h hK e he hframe hy a)).trans
  exact Filter.Eventually.of_forall (fun v =>
    (horizontal_eq_standard_representative hY h hK e he hframe F hF G hG hrep hy v a).symm)

/-- Harmonic projection commutes with the actual horizontal connection on arbitrary local
    smooth real data. The horizontal datum is specified only by its actual AE values. -/
theorem harmonicProjection_horizontal {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : (X N) × (X N) → ℝ) (hF : smoothNear F (bundle Y g)) (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G)
    (hrep : ∀ y ∈ Y,∀ v : (UnitSphere N),G (y,v.val) = F (y,frameVector e y v.val))
    {y : (X N)} (hy : y ∈ Y) (a : (X N)) (H : (SphereL2 N))
    (hH : H =ᵐ[(sphereProbability N)] (fun v : (UnitSphere N) => horizontal g F y (frameVector e y v.val) a)) (k : ℕ) :
    harmonicProjection k H = harmonicCovariantDerivative g e k
      (fun y => harmonicProjection k (ambientSphereL2 G hG y)) y a := by
  have hW := ambientCovariantL2_ae_horizontal hY h hK e he hframe F hF G hG hrep hy a
  have heq : H = ambientCovariantL2 G hG y a (frameConnectionCoefficient g e y a) :=
    Lp.ext (hH.trans hW.symm)
  rw [heq,harmonicProjection_ambientCovariantL2]

end CalderonN
