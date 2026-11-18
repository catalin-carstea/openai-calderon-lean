import Proof.ParallelFirstSelfLeadingComplex
import Proof.ParallelFirstSelfExchangePerturbationPoint
import Proof.ParallelFirstSelfHodgeRemainderPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma first_self_complex_energy_sum_bound {Y : Set X} {d : Data} {K ε : ℝ}
    (hY : IsOpen Y) (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : Test Y d.γ d.frame φ) {y : X} (hy : y ∈ Y) (C fR fI : ℝ) (hC : 0 ≤ C)
    (hR : |fR| ≤ C*ε^2*metricDensity d.γ y*∑ j : I,halfCovariantDirectionEnergy d
      (E.realSobolevSection (3/2:ℝ) (by norm_num)) y (beta d.γ d.radius y) (axis j))
    (hI : |fI| ≤ C*ε^2*metricDensity d.γ y*∑ j : I,halfCovariantDirectionEnergy d
      (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y (beta d.γ d.radius y) (axis j)) :
    |fR+fI| ≤ (3*C*(3*K^2+1))*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  have hEnergy : metricDensity d.γ y*((∑ j : I,halfCovariantDirectionEnergy d
      (E.realSobolevSection (3/2:ℝ) (by norm_num)) y (beta d.γ d.radius y) (axis j))+
      ∑ j : I,halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y
        (beta d.γ d.radius y) (axis j)) ≤ (3*(3*K^2+1))*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    calc
      _ = ∑ j : I,metricDensity d.γ y*(halfCovariantDirectionEnergy d
          (E.realSobolevSection (3/2:ℝ) (by norm_num)) y (beta d.γ d.radius y) (axis j)+
          halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y (beta d.γ d.radius y) (axis j)) := by
        rw [←Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ ∑ _j : I,(3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y :=
        Finset.sum_le_sum (fun j _ => D.half_covariant_direction_energy_le hY hg hK he hFrame hφ.1 hy j)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  calc
    _ ≤ |fR|+|fI| := abs_add_le _ _
    _ ≤ _ := add_le_add hR hI
    _ = (C*ε^2)*(metricDensity d.γ y*((∑ j : I,halfCovariantDirectionEnergy d
        (E.realSobolevSection (3/2:ℝ) (by norm_num)) y (beta d.γ d.radius y) (axis j))+
        ∑ j : I,halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y
          (beta d.γ d.radius y) (axis j))) := by ring
    _ ≤ (C*ε^2)*((3*(3*K^2+1))*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
      mul_le_mul_of_nonneg_left hEnergy (mul_nonneg hC (sq_nonneg ε))
    _ = _ := by ring

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε CA CL CJ MQ CR K : ℝ}

/-- Original physical energy bound for both actual curvature/density
remainders together, retaining the common source expansion. -/
theorem first_self_hodge_complex_remainder_point_bound
    (hY : IsOpen Y) (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : Test Y d.γ d.frame φ) {y : X} (hy : y ∈ Y)
    (hR : FirstSelfAdjointSourcePointBounds P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y CA CL CJ)
    (hI : FirstSelfAdjointSourcePointBounds P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y CA CL CJ)
    (hCA : 0 ≤ CA) (hCL : 0 ≤ CL) (hCJ : 0 ≤ CJ) (hMQ : 0 ≤ MQ) (hCR : 0 ≤ CR)
    (hε : 0 ≤ ε) (hβ : 1 ≤ beta d.γ d.radius y)
    (hDμ : ∀ i,|fderiv ℝ (metricDensity d.γ) y (axis i)| ≤ MQ*metricDensity d.γ y)
    (hCurv : ∀ b c,‖frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis b) (axis c)‖ ≤ CR) :
    |firstSelfAdjointSourceHodgeComplexRemainder WF E y| ≤
      (27*(CA^2*CR+2*MQ*CA*(CL+CJ))*(3*K^2+1))*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  have hr : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (E.realHigherSobolevSection (5/2:ℝ) (by norm_num) x))=E.realSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hi : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num) x))=E.imagSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hRB := first_self_hodge_remainder_point_bound P WF W _ y hR hCA hCL hCJ hMQ hCR hε hβ hDμ hCurv
  have hIB := first_self_hodge_remainder_point_bound P WF W _ y hI hCA hCL hCJ hMQ hCR hε hβ hDμ hCurv
  rw [hr] at hRB
  rw [hi] at hIB
  have hB := first_self_complex_energy_sum_bound hY hg hK he hFrame E D hφ hy
    (9*(CA^2*CR+2*MQ*CA*(CL+CJ))) _ _ (by positivity) hRB hIB
  exact hB.trans_eq (by ring)

/-- Original physical energy bound for the complete real/imaginary
exchange perturbation, with actual forward commutator compatibility. -/
theorem first_self_leading_complex_perturbation_point_bound
    {Ω : Set X} {m : ℕ} {ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : Test Y d.γ d.frame φ) {y : X} (hy : y ∈ Y)
    (hR : FirstSelfAdjointSourcePointBounds P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y CA CL CJ)
    (hI : FirstSelfAdjointSourcePointBounds P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y CA CL CJ)
    (hCL : 0 ≤ CL) (hCJ : 0 ≤ CJ) (hε : 0 ≤ ε) (hβ : 1 ≤ beta d.γ d.radius y)
    (hRaw : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL y b)=
      (P.firstDerivativeCoordinateHalfL y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    |firstSelfLeadingPerturbationComplexDensity P WF W E y| ≤
      (162*CJ*(CL+CJ)*(3*K^2+1))*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  have hr : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (E.realHigherSobolevSection (5/2:ℝ) (by norm_num) x))=E.realSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hi : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num) x))=E.imagSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hRB := first_self_exchange_hodge_perturbation_point_bound P WF W _ hy hR hCL hCJ hε hβ
  have hIB := first_self_exchange_hodge_perturbation_point_bound P WF W _ hy hI hCL hCJ hε hβ
  rw [hr] at hRB
  rw [hi] at hIB
  rw [firstSelfLeadingPerturbationComplexDensity_eq_exchange hY hd P WF W E hy hRaw]
  have hB := first_self_complex_energy_sum_bound hY hg hK he hFrame E D hφ hy
    (54*CJ*(CL+CJ)) _ _ (by positivity) hRB hIB
  exact hB.trans_eq (by ring)

end ShrinkingSpheres.ParallelEnergy
