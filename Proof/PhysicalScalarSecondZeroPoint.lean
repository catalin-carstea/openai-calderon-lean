import Proof.CanonicalCoarseTripleEnergy
import Proof.PrincipalScalarAdjointZeroProductWeights
import Proof.ScalarCovariantSecondZeroPoint

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

lemma Background.reference_third_fderiv_bound {Ω : Set X} {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e) (hm : 3 ≤ m)
    {y : X} (hy : y ∈ Ω) (i j : I) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => g x i j))) y‖ ≤ M ⟨3,by omega⟩ := by
  have hh := h.reference_jet_bound ⟨3,by omega⟩ hy i j
  rw [←norm_iteratedFDeriv_fderiv (n:=2),←norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] at hh
  exact hh

def scalarSecondZeroRemainderDensity {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (q : X → ℝ) (a b : I) (y : X) : ℝ :=
  scalarCovariantSecondZeroRemainder d q (E.realSobolevSection 2 (by norm_num)) (axis a) (axis b) y+
    scalarCovariantSecondZeroRemainder d q (E.imagSobolevSection 2 (by norm_num)) (axis a) (axis b) y

theorem uniform_physical_scalar_second_zero_remainder_point_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ i j a b : I,∀ y ∈ Y,
      |scalarSecondZeroRemainderDensity d E (scalarAdjointZeroProductWeight d.γ d.g₂ d.radius i j) a b y| ≤
        C*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let M3 := |M ⟨3,by omega⟩|
  let Q0 := scalarAdjointZeroProductValueBudget K M1 M2 (Cj 2)
  let Q1 := scalarAdjointZeroProductFirstBudget K M1 M2 M3 (Cj 2) (Cj 3)
  let CP := 3*Q0+3*Q1
  let CE := 3*(3*K^2+1)
  have hBud := scalarAdjointZeroProductBudgets_nonneg K M1 M2 M3 (Cj 2) (Cj 3)
    (zero_le_one.trans hK) (abs_nonneg _)
  have hQ0 : 0 ≤ Q0 := hBud.1
  have hQ1 : 0 ≤ Q1 := hBud.2
  have hCP : 0 ≤ CP := by dsimp only [CP];positivity
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  refine ⟨CP*CE,mul_nonneg hCP hCE,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ i j a b y hy
  let q := scalarAdjointZeroProductWeight d.γ d.g₂ d.radius i j
  let β := beta d.γ d.radius y
  let μ := metricDensity d.γ y
  let Ur := E.realSobolevSection 2 (by norm_num)
  let Ui := E.imagSobolevSection 2 (by norm_num)
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hD (u v : I) : ‖fderiv ℝ (fun x => d.γ x u v) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound (by omega) (hSub hy) u v).trans (le_abs_self _)
  have hD2 (u v : I) : ‖fderiv ℝ (fderiv ℝ (fun x => d.γ x u v)) y‖ ≤ M2 :=
    (hd.1.reference_second_fderiv_bound (by omega) (hSub hy) u v).trans (le_abs_self _)
  have hD3 (u v : I) : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => d.γ x u v))) y‖ ≤ M3 :=
    (hd.1.reference_third_fderiv_bound hm (hSub hy) u v).trans (le_abs_self _)
  have hWeights := scalar_principal_adjoint_zero_product_weights hY hg hg2 hK d.frame hFrame
    hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy M1 M2 M3 (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    hD hD2 hD3 i j
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hμ : 0 ≤ μ := Real.sqrt_nonneg _
  have hq : |q y| ≤ μ*Q0*ε^2/β^2 := hWeights.1
  have hDq : |fderiv ℝ q y (axis a)| ≤ μ*Q1*ε^2/β := hWeights.2 a
  have hR := scalar_covariant_second_zero_remainder_bound d q Ur y (axis a) (axis b)
    μ Q0 Q1 ε β hμ hQ0 hQ1 hβ hq hDq
  have hI := scalar_covariant_second_zero_remainder_bound d q Ui y (axis a) (axis b)
    μ Q0 Q1 ε β hμ hQ0 hQ1 hβ hq hDq
  have hEnergy := D.coarse_covariant_triple_energy_le hY hg hK he hFrame hφ.1 hy a a b
  change |scalarCovariantSecondZeroRemainder d q Ur (axis a) (axis b) y+
    scalarCovariantSecondZeroRemainder d q Ui (axis a) (axis b) y| ≤ _
  calc
    _ ≤ CP*μ*ε^2*coarseCovariantTripleEnergy d Ur y β (axis a) (axis a) (axis b)+
        CP*μ*ε^2*coarseCovariantTripleEnergy d Ui y β (axis a) (axis a) (axis b) :=
      (abs_add_le _ _).trans (add_le_add hR hI)
    _ = (CP*ε^2)*(μ*(coarseCovariantTripleEnergy d Ur y β (axis a) (axis a) (axis b)+
        coarseCovariantTripleEnergy d Ui y β (axis a) (axis a) (axis b))) := by ring
    _ ≤ (CP*ε^2)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
      mul_le_mul_of_nonneg_left hEnergy (mul_nonneg hCP (sq_nonneg ε))
    _ = _ := by ring

end ShrinkingSpheres
