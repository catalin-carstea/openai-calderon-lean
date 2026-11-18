import Proof.PhysicalAdjointCommutatorData
import Proof.UniformNativeFirstErrorAdjointCommutator
import Proof.ActualFirstErrorNativeIdentification
import Proof.ActualFirstAdjointErrorGerm
import Proof.CompatibleEndpointUniqueness
import Proof.UniformNativeRelativeHorizontalTaylorData
import Proof.RelativeCenterErrorCoefficientFamily
import Proof.UniformNativeRelativeSymmetricHigherData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Uniform actual physical mixed adjoint first-error commutator for ANY
already selected compatible physical endpoints. A genuine higher adjoint
endpoint is supplied. Both directions use one common native packet. -/
theorem uniform_actual_first_error_adjoint_commutator {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CS : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CS ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ a b : X,
      ∀ R A Ga Gb : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (Ga x)) →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x b (A x) (Gb x)) →
      ∀ x ∈ Y,
      ∀ La Lb : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A Ga x)=
        La.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) →
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d b A Gb x)=
        Lb.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) →
      PhysicalFirstErrorAdjointCommutatorData (actualFirstAdjointErrorFamily d b A Gb x) La Lb
        (CS*‖a‖*‖b‖*(d.radius x)^2) := by
  classical
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hCoeff⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηV,CFV,CAV,hηV,hηV1,hCFV,hCAV,hSym⟩ :=
    uniform_native_relative_symmetric_higher_data hY hΩ 0 (by omega) K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  obtain ⟨Q0,hQ0⟩ := exists_unit_boundary_coefficient
  obtain ⟨ηS,CS,hηS,hηS1,hCS,hSelf⟩ := uniform_native_first_error_adjoint_commutator
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW (zero_le_one.trans hCQ) hCI hCW F0 hF0 Q0 hQ0 CC CH (zero_le_one.trans hCC)
  refine ⟨min ηT (min ηC (min ηV ηS)),CS,lt_min hηT (lt_min hηC (lt_min hηV hηS)),
    (min_le_left _ _).trans hηT1,hCS,?_⟩
  intro floor hf ε hε hSmall d hd a b R A Ga Gb hR hA hGa hGb x hx La Lb hLa hLb
  have hSmallT := hSmall.trans (min_le_left _ _)
  have hSmallC := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallV := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSmallS := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨s⟩ := hNative floor hf ε hε hSmallT d hd x hx
  obtain ⟨V⟩ := hSym floor hf ε hε hSmallV d hd x hx CQ CF CA CM s
  let Ca : (j : I) → RelativeCenterErrorCoefficientFamily d x a j CC CH :=
    fun j => Classical.choice (hCoeff floor hf ε hε hSmallC d hd x hx a j)
  let Cb : (j : I) → RelativeCenterErrorCoefficientFamily d x b j CC CH :=
    fun j => Classical.choice (hCoeff floor hf ε hε hSmallC d hd x hx b j)
  let p : NormalFrameRelativeParameter := ((x,frameVectorLinear d.frame x),0)
  have hr := (hd.2.2.2.2.1.2 x hx).1.ne'
  obtain ⟨hEa,hLaEq⟩ := s.actual_first_error_native_identification V.neighborhood hY hΩ hSub hd.1
    (zero_lt_one.trans_le hK) hx hr hd.2.2.2.2.1.1 Ca R A Ga hR hA hGa hF0 La hLa
  obtain ⟨hEb,hLbEq⟩ := s.actual_first_error_native_identification V.neighborhood hY hΩ hSub hd.1
    (zero_lt_one.trans_le hK) hx hr hd.2.2.2.2.1.1 Cb R A Gb hR hA hGb hF0 Lb hLb
  exact native_first_error_adjoint_data_transport s
    (hSelf floor hf ε hε hSmallS d hd x hx CF CA CM s) a b Ca Cb _ La Lb hEb hLaEq hLbEq
end ShrinkingSpheres
