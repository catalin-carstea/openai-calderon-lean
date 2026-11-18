import Proof.PhysicalFirstCoordinateCommutator
import Proof.UniformPhysicalFirstCommutatorIntegral
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def AngularComponentData.coordinateFirstCommutatorForm {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} {L : ℂ →L[ℝ] ℝ}
    (_Q : AngularComponentData E d.radius L)
    (S : I → I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (y : X) : ℝ :=
  firstCommutatorForm S (fun b => halfSectionCovariantDerivativeL d
    (ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => L (E.representative p))
      (L.contDiff.comp E.representativeSmooth)) y (axis b))

def AngularModelData.coordinateFirstCommutatorDensity {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} (D : AngularModelData E d.radius)
    (S : I → I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (y : X) : ℝ :=
  metricDensity d.γ y*(D.realComponent.coordinateFirstCommutatorForm (fun b c => S b c y) y+
    D.imagComponent.coordinateFirstCommutatorForm (fun b c => S b c y) y)

lemma PhysicalFirstCommutatorPacket.coordinate_component_form_eq {Y : Set X} {d : Data}
    {CF CT CB CS ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (W : PhysicalFirstCommutatorPacket P CB CS ε) {φ : Field}
    {E : HarmonicTestExpansion Y d.γ d.frame φ} {L : ℂ →L[ℝ] ℝ}
    (Q : AngularComponentData E d.radius L) (hY : IsOpen Y) {K : ℝ}
    (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hφ : smoothNear φ (bundle Y d.γ)) {y : X} (hy : y ∈ Y) :
    Q.coordinateFirstCommutatorForm (fun b c => W.coordinateCommLow b c y) y=
      firstCommutatorForm (fun i j => W.commLow i j y) (fun i => Q.horizontalHalfSection i y) := by
  let U := ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => L (E.representative p))
    (L.contDiff.comp E.representativeSmooth)
  have hInputs : (fun i => Q.horizontalHalfSection i y)=
      (fun i => halfSectionCovariantDerivativeL d U y (d.frame y i)) :=
    funext (fun i => Q.horizontalHalfSection_covariant hY hg hK he hFrame hφ hy i)
  rw [hInputs]
  exact (firstCommutatorForm_frame_change (fun i j => W.commLow i j y) d.frame y
    (halfSectionCovariantDerivativeL d U y)).symm

lemma PhysicalFirstCommutatorPacket.coordinate_density_eq {Y Ω : Set X} {d : Data}
    {CF CT CB CS ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (W : PhysicalFirstCommutatorPacket P CB CS ε)
    (hY : IsOpen Y) {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} (D : AngularModelData E d.radius)
    (hφ : smoothNear φ (bundle Y d.γ)) {y : X} (hy : y ∈ Y) :
    D.coordinateFirstCommutatorDensity W.coordinateCommLow y=D.firstCommutatorDensity W.commLow y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y :=
    fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  simp only [AngularModelData.coordinateFirstCommutatorDensity,AngularModelData.firstCommutatorDensity,
    W.coordinate_component_form_eq D.realComponent hY hg hK he hFrame hφ hy,
    W.coordinate_component_form_eq D.imagComponent hY hg hK he hFrame hφ hy]

theorem PhysicalFirstCommutatorPacket.integral_coordinate_density_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {CF CT CB CS : ℝ}
    {P : PhysicalPrincipalData Y d CF CT} (W : PhysicalFirstCommutatorPacket P CB CS ε)
    (hCS : 0 ≤ CS) {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (hφ : Test Y d.γ d.frame φ) :
    IntegrableOn (D.coordinateFirstCommutatorDensity W.coordinateCommLow) Y ∧
      |∫ y in Y,D.coordinateFirstCommutatorDensity W.coordinateCommLow y| ≤
        (9*CS)*ε*energySq Y d.γ d.frame d.radius φ := by
  have hEq : D.firstCommutatorDensity W.commLow =ᵐ[volume.restrict Y]
      D.coordinateFirstCommutatorDensity W.coordinateCommLow := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact (W.coordinate_density_eq hY hd (zero_lt_one.trans_le hK) D hφ.1 hy).symm
  obtain ⟨hInt,hBound⟩ := W.integral_density_bound hY hΩ hd hK hf hε hε1 hCS E D hφ
  exact ⟨hInt.congr hEq,(congrArg abs (integral_congr_ae hEq)).symm.trans_le hBound⟩

theorem uniform_physical_first_coordinate_commutator_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CB CS CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CB ∧ 0 ≤ CS ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ W : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      IntegrableOn (D.coordinateFirstCommutatorDensity W.coordinateCommLow) Y ∧
        |∫ y in Y,D.coordinateFirstCommutatorDensity W.coordinateCommLow y| ≤
          CE*ε*energySq Y d.γ d.frame d.radius φ := by
  have hProduce := uniform_physical_first_commutator_packet hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨η,CB,CS,hη,hη1,hCB,hCS,hData⟩ := hProduce
  refine ⟨η,CB,CS,9*CS,hη,hη1,hCB,hCS,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨W⟩ := hData floor hf ε hε hSmall d hd CT P
  refine ⟨W,?_⟩
  intro φ E D hφ
  exact W.integral_coordinate_density_bound hY hΩ hd hK hf hε (hSmall.trans hη1) hCS E D hφ
end ShrinkingSpheres
