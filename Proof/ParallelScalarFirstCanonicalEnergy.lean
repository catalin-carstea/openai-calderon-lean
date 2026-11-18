import Proof.HalfCovariantEnergyControl

noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace ShrinkingSpheres.ParallelEnergy

theorem half_covariant_axis_energy_le
    {Y : Set X} {d : Data} {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ}
    (D : AngularModelData E d.radius) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y)
    (hFrame : ∀ x ∈ Y,∀ j k,metricPair d.γ x (d.frame x j) (d.frame x k)=if j=k then 1 else 0)
    (hφ : smoothNear φ (bundle Y d.γ)) {y : X} (hy : y ∈ Y) :
    metricDensity d.γ y*((∑ i : I,halfCovariantDirectionEnergy d
      (E.realSobolevSection (3/2:ℝ) (by norm_num)) y (beta d.γ d.radius y) (axis i))+
      ∑ i : I,halfCovariantDirectionEnergy d
      (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y (beta d.γ d.radius y) (axis i)) ≤
      (3*(3*K^2+1))*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  calc
    _ = ∑ i : I,metricDensity d.γ y*(halfCovariantDirectionEnergy d
        (E.realSobolevSection (3/2:ℝ) (by norm_num)) y (beta d.γ d.radius y) (axis i)+
        halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y
          (beta d.γ d.radius y) (axis i)) := by simp only [Fin.sum_univ_three];ring
    _ ≤ ∑ _i : I,(3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y :=
      Finset.sum_le_sum (fun i _ => D.half_covariant_direction_energy_le hY hg hK he hFrame hφ hy i)
    _ = _ := by simp only [Fin.sum_univ_three];ring

end ShrinkingSpheres.ParallelEnergy
