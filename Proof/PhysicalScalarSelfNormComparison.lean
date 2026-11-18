import Proof.PhysicalScalarCoreDomain
import Proof.PhysicalScalarSelfIntegral
import Proof.ScalarCovariantSelfCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def scalarPrincipalSquareDensity {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  metricDensity d.γ y*(
    ‖scalarCovariantSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius)
      (E.realSobolevSection 2 (by norm_num)) y‖^2+
    ‖scalarCovariantSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius)
      (E.imagSobolevSection 2 (by norm_num)) y‖^2)

def scalarPrincipalTransposeSquareDensity {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  metricDensity d.γ y*(
    ‖scalarCovariantSecondTransposeSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
      (E.realSobolevSection 2 (by norm_num)) y‖^2+
    ‖scalarCovariantSecondTransposeSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
      (E.imagSobolevSection 2 (by norm_num)) y‖^2)

/-- Both actual scalar operators are individually square-integrable on
the same supported core, and their squared physical norms differ by a
uniform epsilon-squared multiple of the original energy. -/
theorem uniform_physical_scalar_self_norm_comparison {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      IntegrableOn (scalarPrincipalSquareDensity d E) Y ∧
        IntegrableOn (scalarPrincipalTransposeSquareDensity d E) Y ∧
        |(∫ y in Y,scalarPrincipalSquareDensity d E y)-
          (∫ y in Y,scalarPrincipalTransposeSquareDensity d E y)| ≤
            C*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨C,hC,hBase⟩ := uniform_physical_scalar_self_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK
  refine ⟨C,hC,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ
  let mu := metricDensity d.γ
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hmuS := hg.contDiffOn_density hKpos
  have hmu (x : X) (hx : x ∈ E.supportSet) : ContDiffAt ℝ ∞ mu x :=
    hmuS.contDiffAt (hY.mem_nhds (E.supportSubset hx))
  have hPer (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
      (h0 : ∀ x ∉ E.supportSet,U x=0) :
      Integrable (fun x => mu x*‖scalarCovariantSecondSection d A U x‖^2) ∧
        Integrable (fun x => mu x*‖scalarCovariantSecondTransposeSection d mu A U x‖^2) := by
    have hDomain := physical_scalar_principal_core_supported hY hSub hd hKpos U hU
      E.supportSet E.compactSupportSet.isClosed E.supportSubset h0
    have hS := hDomain.1
    have hSA := hDomain.2

    exact ⟨integrable_supported_weighted_norm_sq mu _ E.supportSet E.compactSupportSet hmu hS.1 hS.2,
      integrable_supported_weighted_norm_sq mu _ E.supportSet E.compactSupportSet hmu hSA.1 hSA.2⟩
  have hR := hPer (E.realSobolevSection 2 (by norm_num))
    (E.contDiff_realSobolevSection 2 (by norm_num)) (fun x hx => E.realSobolevSection_zero 2 (by norm_num) hx)
  have hI := hPer (E.imagSobolevSection 2 (by norm_num))
    (E.contDiff_imagSobolevSection 2 (by norm_num)) (fun x hx => E.imagSobolevSection_zero 2 (by norm_num) hx)
  have hSI : IntegrableOn (scalarPrincipalSquareDensity d E) Y := by
    apply Integrable.integrableOn
    change Integrable (fun x => mu x*(_+_))
    simp only [mul_add]
    exact hR.1.add hI.1
  have hSAI : IntegrableOn (scalarPrincipalTransposeSquareDensity d E) Y := by
    apply Integrable.integrableOn
    change Integrable (fun x => mu x*(_+_))
    simp only [mul_add]
    exact hR.2.add hI.2
  have hDiff (x : X) : scalarSelfNormDifferenceDensity d E x=
      scalarPrincipalSquareDensity d E x-scalarPrincipalTransposeSquareDensity d E x := by
    unfold scalarSelfNormDifferenceDensity scalarPrincipalSquareDensity scalarPrincipalTransposeSquareDensity
    ring
  have hEq : (∫ x in Y,scalarSelfNormDifferenceDensity d E x)=
      (∫ x in Y,scalarPrincipalSquareDensity d E x)-(∫ x in Y,scalarPrincipalTransposeSquareDensity d E x) := by
    calc
      _ = ∫ x in Y,scalarPrincipalSquareDensity d E x-scalarPrincipalTransposeSquareDensity d E x :=
        integral_congr_ae (Eventually.of_forall hDiff)
      _ = _ := integral_sub hSI hSAI
  refine ⟨hSI,hSAI,?_⟩
  rw [←hEq]
  exact (hBase floor hf ε hε hε1 d hd φ E D hφ).2

end ShrinkingSpheres
