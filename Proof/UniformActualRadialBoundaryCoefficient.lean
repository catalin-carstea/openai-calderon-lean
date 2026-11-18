import Proof.ActualRadialNormalCoefficient
import Proof.RadialBoundaryCoefficient
import Proof.EnlargedFramedEllipticity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

theorem uniform_actual_radial_boundary_coefficient {Y Ω : Set X}
    (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ F : SmoothCoefficientMatrix 2,
      (∀ w : UnitSphere,coefficientMatrixField 2 F w.val=normalizedFirstNormalCoefficient d y w.val) →
      (∀ w : UnitSphere,(boundaryNormalCoefficientData F).1 w.val=actualRadialNormalCoefficient d y w.val) ∧
      coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)=0 ∧
      adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j)=0 ∧
      ∀ w : UnitSphere,0 < actualRadialNormalCoefficient d y w.val := by
  obtain ⟨ηN,hηN,hNormal⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 1 (by norm_num)
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 1 (by norm_num)
  refine ⟨min ηN ηE,lt_min hηN hηE,?_⟩
  intro floor hf ε hε hSmall d hd y hy F hF
  have hKpos := zero_lt_one.trans_le hK
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hEll := hElliptic floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy d.γ (by simp)
  have hSphere (w : UnitSphere) : w.val ∈ Metric.closedBall (0:X) 1 := Metric.sphere_subset_closedBall w.property
  have hPack (w : UnitSphere) := hNormal floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
    (frameVector d.frame y w.val) (frameVector_mem_unitDisk d.γ d.frame y w.val hFrame (hSphere w))
  have hDet (w : UnitSphere) : 0 < (framedNormalMetric d.γ d.frame d.expMap y (d.radius y) w.val).det :=
    (hEll.posDef (by positivity) (hSphere w)).det_pos
  have hRow (w : UnitSphere) (j : I) :
      ∑ i : I,w.val i*coefficientValue 2 (F i j) w.val=actualRadialNormalCoefficient d y w.val*w.val j := by
    change ∑ i : I,w.val i*coefficientMatrixField 2 F w.val i j=_
    rw [hF w]
    exact hd.normalizedFirstNormalCoefficient_radial_row hΩ hKpos hy w.val (hPack w).1.1
      (isUnit_iff_ne_zero.mpr (hDet w).ne') j
  obtain ⟨hT,hTa⟩ := radial_row_tangential_operators_zero F (fun w => actualRadialNormalCoefficient d y w.val) hRow
  refine ⟨boundaryNormalCoefficient_of_radial_row F _ hRow,hT,hTa,?_⟩
  intro w
  have h1 := firstMetricDensityFactor_pos d.γ d.g₁ y
  have h2 := firstMetricDensityFactor_pos d.γ d.g₁ (d.expMap (y,d.radius y • frameVector d.frame y w.val))
  have h3 := Real.sqrt_pos.2 (hDet w)
  unfold actualRadialNormalCoefficient framedFirstDensityFactor
  positivity
end ShrinkingSpheres
