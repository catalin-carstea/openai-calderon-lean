import Proof.ParallelFirstSelfWeakAdjointBound
import Proof.ParallelScalarFirstCanonicalEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def firstWeakSquareDensity {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  metricDensity d.γ y*(
    ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (P.firstFormalAdjointCore WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y)‖^2+
    ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (P.firstFormalAdjointCore WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y)‖^2)

/-- Compose first-self's independently owned checked weak norm bound with
the common canonical physical energy comparison. -/
theorem uniform_first_weak_square_point_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CB CS CG CK : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ y ∈ Y,
        firstWeakSquareDensity P WF W E y ≤ C*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  obtain ⟨η,CE,hη,hη1,hCE,hWeak⟩ := uniform_first_formal_adjoint_core_weak_norm_sq_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CE*(3*(3*K^2+1)),hη,hη1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CB CS CG CK P WF W φ E D hφ y hy
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Rr := E.realSobolevSection (3/2:ℝ) (by norm_num)
  let Ri := E.imagSobolevSection (3/2:ℝ) (by norm_num)
  have hR := hWeak floor hf ε hε hSmall d hd CF CT CB CS CG CK P WF W Ur
    (E.contDiff_realHigherSobolevSection _ _).contDiffOn y hy
  have hI := hWeak floor hf ε hε hSmall d hd CF CT CB CS CG CK P WF W Ui
    (E.contDiff_imagHigherSobolevSection _ _).contDiffOn y hy
  have hUR : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ur x))=Rr :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hUI : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ui x))=Ri :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  rw [hUR] at hR
  rw [hUI] at hI
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hEnergy := half_covariant_axis_energy_le D hY hg hK he hFrame hφ.1 hy
  change metricDensity d.γ y*(_+_) ≤ _
  calc
    _ ≤ metricDensity d.γ y*((CE*ε^2)*(∑ b : I,halfCovariantDirectionEnergy d Rr y (beta d.γ d.radius y) (axis b))+
        (CE*ε^2)*(∑ b : I,halfCovariantDirectionEnergy d Ri y (beta d.γ d.radius y) (axis b))) :=
      mul_le_mul_of_nonneg_left (add_le_add hR hI) (Real.sqrt_nonneg _)
    _ = (CE*ε^2)*(metricDensity d.γ y*((∑ b : I,halfCovariantDirectionEnergy d Rr y (beta d.γ d.radius y) (axis b))+
        ∑ b : I,halfCovariantDirectionEnergy d Ri y (beta d.γ d.radius y) (axis b))) := by ring
    _ ≤ (CE*ε^2)*((3*(3*K^2+1))*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
      mul_le_mul_of_nonneg_left hEnergy (mul_nonneg hCE (sq_nonneg ε))
    _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
