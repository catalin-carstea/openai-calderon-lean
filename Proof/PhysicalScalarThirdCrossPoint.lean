import Proof.CanonicalCoarseTripleEnergy
import Proof.PrincipalScalarAdjointProductWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def scalarThirdCrossRemainderDensity {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (q : X → ℝ) (a b c : I) (y : X) : ℝ :=
  scalarCovariantThirdCrossRemainder d q (E.realSobolevSection 2 (by norm_num)) (axis a) (axis b) (axis c) y+
    scalarCovariantThirdCrossRemainder d q (E.imagSobolevSection 2 (by norm_num)) (axis a) (axis b) (axis c) y

/-- Actual scalar-principal/adjoint third-base remainder, uniformly
bounded by the original physical energy. All constants precede every
profile, configuration, coefficient index and test section. -/
theorem uniform_physical_scalar_third_cross_remainder_point_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ i j l a b c : I,∀ y ∈ Y,
      |scalarThirdCrossRemainderDensity d E (scalarAdjointProductWeight d.γ d.g₂ d.radius i j l) a b c y| ≤
        C*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let Q0 := scalarAdjointProductZeroBudget K M1
  let Q := scalarAdjointProductFirstBudget K M1 M2 (Cj 2)
  let CR := fixedDirectionAngularCurvatureBudget hm K M
  let CP := 3*Q+3*Q0*CR
  let CE := 3*(3*K^2+1)
  have hQBud := scalarAdjointProductBudgets_nonneg K M1 M2 (Cj 2) (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _)
  have hQ0 : 0 ≤ Q0 := hQBud.1
  have hQ : 0 ≤ Q := hQBud.2
  have hCR : 0 ≤ CR := fixedDirectionAngularCurvatureBudget_nonneg hm K (zero_le_one.trans hK) M
  have hCP : 0 ≤ CP := by dsimp only [CP];positivity
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  refine ⟨CP*CE,mul_nonneg hCP hCE,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ i j l a b c y hy
  let q := scalarAdjointProductWeight d.γ d.g₂ d.radius i j l
  let β := beta d.γ d.radius y
  let μ := metricDensity d.γ y
  let Ur := E.realSobolevSection 2 (by norm_num)
  let Ui := E.imagSobolevSection 2 (by norm_num)
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y :=
    (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hD (u v : I) : ‖fderiv ℝ (fun x => d.γ x u v) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound (by omega) (hSub hy) u v).trans (le_abs_self _)
  have hD2 (u v : I) : ‖fderiv ℝ (fderiv ℝ (fun x => d.γ x u v)) y‖ ≤ M2 :=
    (hd.1.reference_second_fderiv_bound hm (hSub hy) u v).trans (le_abs_self _)
  have hWeights := scalar_principal_adjoint_product_weights hY hg hg2 hK d.frame hFrame
    hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy M1 M2 (abs_nonneg _) (abs_nonneg _) hD hD2 i j l
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hμ : 0 ≤ μ := Real.sqrt_nonneg _
  have hq : |q y| ≤ μ*Q0*ε^2/β^3 := hWeights.1
  have hDq (k : I) : |fderiv ℝ q y (axis k)| ≤ μ*Q*ε^2/β^2 := hWeights.2 k
  have hR := hd.1.scalar_third_cross_remainder_bound hΩ hK hm q Ur (hSub hy)
    μ Q Q0 ε β hμ hQ hQ0 hβ hq hDq a b c
  have hI := hd.1.scalar_third_cross_remainder_bound hΩ hK hm q Ui (hSub hy)
    μ Q Q0 ε β hμ hQ hQ0 hβ hq hDq a b c
  have hEnergy := D.coarse_covariant_triple_energy_le hY hg hK he hFrame hφ.1 hy a b c
  change |scalarCovariantThirdCrossRemainder d q Ur (axis a) (axis b) (axis c) y+
    scalarCovariantThirdCrossRemainder d q Ui (axis a) (axis b) (axis c) y| ≤ _
  calc
    _ ≤ CP*μ*ε^2*coarseCovariantTripleEnergy d Ur y β (axis a) (axis b) (axis c)+
        CP*μ*ε^2*coarseCovariantTripleEnergy d Ui y β (axis a) (axis b) (axis c) :=
      (abs_add_le _ _).trans (add_le_add hR hI)
    _ = (CP*ε^2)*(μ*(coarseCovariantTripleEnergy d Ur y β (axis a) (axis b) (axis c)+
        coarseCovariantTripleEnergy d Ui y β (axis a) (axis b) (axis c))) := by ring
    _ ≤ (CP*ε^2)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
      mul_le_mul_of_nonneg_left hEnergy (mul_nonneg hCP (sq_nonneg ε))
    _ = _ := by ring

end ShrinkingSpheres
