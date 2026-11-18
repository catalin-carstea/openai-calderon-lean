import Proof.ParallelScalarPotentialDefectIntegrability
import Proof.ParallelScalarFirstDefectSquare
import Proof.ParallelFirstSelfDefectSquareIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME actual potential adjoint weak output has an epsilon-squared
complex mass bound in the original frozen physical energy. -/
theorem scalar_potential_adjoint_weak_square_point_bound
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCG : 0 ≤ CG)
    (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : Test Y d.γ d.frame φ) {y : X} (hy : y ∈ Y) :
    let CQ := (max (physicalPotentialGeneratorBudget CF) CG)^2*(49*potentialWordEntryBudget K)
    metricDensity d.γ y*(
      ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W
        (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y)‖^2+
      ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W
        (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y)‖^2) ≤
      (CQ^2*(3*K^2+1))*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let CQ := (max (physicalPotentialGeneratorBudget CF) CG)^2*(49*potentialWordEntryBudget K)
  have hCQ : 0 ≤ CQ := by dsimp only [CQ,potentialWordEntryBudget];positivity
  have hPer (U : X → SphereSobolev (5/2:ℝ)) :
      ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W U y)‖^2 ≤
        CQ^2*ε^2*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖^2 := by
    have hN : ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W U y)‖ ≤
        CQ*ε*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖ := by
      rw [actual_potential_adjoint_section_weak_graph P W U hy]
      exact actual_potential_adjoint_weak_norm_bound P hd hK hf hε hε1 hy hCG (W y hy) _
    exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hN).trans_eq (by ring)
  have hR := hPer (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
  have hI := hPer (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
  rw [E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num)] at hR
  rw [E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num)] at hI
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hMass := first_self_complex_mass_density_le hY hg hK he hFrame E D hφ hy hβ
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  calc
    _ ≤ metricDensity d.γ y*(CQ^2*ε^2*‖E.realSobolevSection (3/2:ℝ) (by norm_num) y‖^2+
        CQ^2*ε^2*‖E.imagSobolevSection (3/2:ℝ) (by norm_num) y‖^2) :=
      mul_le_mul_of_nonneg_left (add_le_add hR hI) hμ
    _ = (CQ^2*ε^2)*(metricDensity d.γ y*(‖E.realSobolevSection (3/2:ℝ) (by norm_num) y‖^2+
        ‖E.imagSobolevSection (3/2:ℝ) (by norm_num) y‖^2)) := by ring
    _ ≤ (CQ^2*ε^2)*((3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
      mul_le_mul_of_nonneg_left hMass (by positivity)
    _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
