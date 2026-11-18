import Proof.ActualFirstAdjointErrorGerm
import Proof.NativeFirstErrorAngularGraph
import Proof.SmoothUniqueLocalRealization
import Proof.CoarseRotationGraphUnique
import Proof.UniformNativeFirstErrorDegreeJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A globally smooth genuine angular commutator for the SAME complete remainder. -/
theorem uniform_actual_first_adjoint_error_angular {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CD ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ a : X,
      ∀ R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∀ i j : I,∃ S : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ContDiffOn ℝ ∞ S Y ∧ ∀ x ∈ Y,
          ‖S x‖ ≤ CD*‖a‖*d.radius x ∧
          ∀ u : SphereSobolev 2,
            sphereSobolevRotationL 0 i j (actualFirstAdjointErrorFamily d a A G x
              (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
              sphereSobolevInclusionL 0 (-1) (by norm_num)
                (S x (sphereSobolevInclusionL 2 1 (by norm_num) u)+
                  actualFirstAdjointErrorFamily d a A G x (sphereSobolevRotationL 2 i j u)) := by
  classical
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hC⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,CD,CDH,hηE,hηE1,hCE,hCD,hCDH,hError⟩ :=
    uniform_native_first_error_degree_three_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
      CQ CI CW CC (zero_le_one.trans hCQ) hCI hCW (zero_le_one.trans hCC) F0 hF0
  refine ⟨min ηT (min ηC ηE),CE,lt_min hηT (lt_min hηC hηE),
    (min_le_left _ _).trans hηT1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd a R A G hR hA hG i j
  let E := actualFirstAdjointErrorFamily d a A G
  let Realizes (x : X) (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0) : Prop :=
    ∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (E x (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (S (sphereSobolevInclusionL 2 1 (by norm_num) u)+E x (sphereSobolevRotationL 2 i j u))
  have hUnique (x : X) (S T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
      (hS : Realizes x S) (hT : Realizes x T) : S=T :=
    coarse_rotation_generator_unique (E x) S T i j hS hT
  have hSmallT := hSmall.trans (min_le_left _ _)
  have hSmallC := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallE := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLocal (y : X) (hy : y ∈ Y) :
      ∃ S : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ContDiffAt ℝ ∞ S y ∧ (∀ᶠ x in 𝓝 y,Realizes x (S x)) ∧ ‖S y‖ ≤ CE*‖a‖*d.radius y := by
    obtain ⟨s⟩ := hNative floor hf ε hε hSmallT d hd y hy
    obtain ⟨V,hJets⟩ := hError floor hf ε hε hSmallE d hd y hy CF CA CM s
    let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH :=
      fun j => Classical.choice (hC floor hf ε hε hSmallC d hd y hy a j)
    let Ψ := normalFrameRelativeActualParameter d (d.radius y)
    let p1 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    have hr := (hd.2.2.2.2.1.2 y hy).1.ne'
    have hΨ := (contDiffOn_normalFrameRelativeActualParameter d (d.radius y) hd.2.2.2.2.1.1
      (fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub)).contDiffAt (hY.mem_nhds hy)
    have hΨ0 : Ψ y = p1 := normalFrameRelativeActualParameter_point d y hr
    have hStay : ∀ᶠ x in 𝓝 y,Ψ x ∈ s.centerDegreeDomain V :=
      hΨ.continuousAt.eventually ((s.centerDegreeDomain_open V).mem_nhds
        (by rw [normalFrameRelativeActualParameter_point d y hr];exact s.centerDegreeDomain_pointMem V))
    let S := (fun p => (s.firstErrorAngularFields C p).angular (i,j)) ∘ Ψ
    have hSS : ContDiffAt ℝ ∞ S y := by
      have hh := (s.firstErrorAngularFields_smoothAt C V hY hΩ hd.1.1 (zero_lt_one.trans_le hK)
        hd.2.2.2.2.1 p1 (s.centerDegreeDomain_pointMem V)).angular (i,j)
      rw [← hΨ0] at hh
      exact hh.comp y hΨ
    have hGerm := s.actual_first_adjoint_error_germ V hY hΩ hSub hd.1 (zero_lt_one.trans_le hK)
      hy hr hd.2.2.2.2.1.1 C R A G hR hA hG
    have hPhysical : ∀ᶠ x in 𝓝 y,Realizes x (S x) := by
      filter_upwards [hGerm,hStay] with x hx hxp
      intro u
      change sphereSobolevRotationL 0 i j (E x (sphereSobolevInclusionL 2 1 (by norm_num) u)) = _
      rw [show E x = s.firstAdjointErrorFamily C (Ψ x) from hx]
      exact s.firstErrorAngularFields_rotation_graph C V hd.1.1 (zero_lt_one.trans_le hK) (Ψ x) hxp.1 i j u
    have hN := ((hJets a CH C).1.angular (i,j)).bound 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hN
    simp only [Function.comp_apply,normalFrameRelativeScaledParameter_point] at hN
    refine ⟨S,hSS,hPhysical,?_⟩
    change ‖(s.firstErrorAngularFields C (Ψ y)).angular (i,j)‖ ≤ _
    rw [hΨ0]
    exact hN
  obtain ⟨S,hSS,hS⟩ := exists_contDiffOn_unique_local_realization hY Realizes
    (fun x hx U V hU hV => hUnique x U V hU hV) (by
      intro y hy
      obtain ⟨S,hSS,hSR,hSN⟩ := hLocal y hy
      exact ⟨S,hSS,hSR⟩)
  refine ⟨S,hSS,?_⟩
  intro x hx
  obtain ⟨T,hTS,hTR,hTN⟩ := hLocal x hx
  have hEq := hUnique x (S x) (T x) (hS x hx) hTR.self_of_nhds
  exact ⟨(congrArg norm hEq).trans_le hTN,hS x hx⟩
end ShrinkingSpheres
