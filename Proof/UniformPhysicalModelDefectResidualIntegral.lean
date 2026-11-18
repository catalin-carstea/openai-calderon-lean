import Proof.PhysicalModelDefectResidualIdentity
import Proof.PhysicalFirstModelDefectIntegral
import Proof.PhysicalScalarSelfIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Complete SAME actual truncated residual applied to the model-adjoint
defect. Scalar, effective first and all quadratic potential contributions
are present; the result uses the original global energy and no extra frame
or operator premise. -/
theorem uniform_physical_model_defect_residual_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      IntegrableOn (P.modelDefectResidualDensity E) Y ∧
        |∫ y in Y,P.modelDefectResidualDensity E y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨CS,hCS,hScalar⟩ := uniform_physical_scalar_model_defect_second_integral_bound
    hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  obtain ⟨ηF,CFB,hηF,hηF1,hCFB,hFirst⟩ := uniform_physical_first_model_defect_integral_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηQ,CG,CK,CQ,hηQ,hηQ1,hCG,hCK,hCQ,hPotential⟩ :=
    uniform_physical_potential_model_defect_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  let C := 9*CS+3*CFB+CQ
  refine ⟨min ηF ηQ,C,lt_min hηF hηQ,(min_le_left _ _).trans hηF1,
    by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨W,hQData⟩ := hPotential floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CT P
  intro φ E D hφ
  let S := fun a b => physicalScalarModelDefectSecondDensity d E
    (scalarPrincipalDensityWeight d.γ d.g₂ d.radius a b) a b
  let F := P.firstModelDefectDensity E
  let Q := P.potentialModelDefectDensityFamily E W
  let SS := fun x => ∑ a : I,∑ b : I,S a b x
  let FS := fun x => ∑ b : I,F b x
  let EN := ε*energySq Y d.γ d.frame d.radius φ
  have hε1 := (hSmall.trans (min_le_left _ _)).trans hηF1
  have hSD (a b : I) := hScalar floor hf ε hε hε1 d hd φ E D hφ a b a b
  have hFD (b : I) := hFirst floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CT P φ E D hφ b
  have hQD := hQData φ E D hφ
  have hSI (a b : I) : IntegrableOn (S a b) Y := (hSD a b).1
  have hFI (b : I) : IntegrableOn (F b) Y := (hFD b).1
  have hQI : IntegrableOn Q Y := hQD.1
  have hSSI : IntegrableOn SS Y := integrable_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ (fun b _ => hSI a b))
  have hFSI : IntegrableOn FS Y := integrable_finsetSum Finset.univ (fun b _ => hFI b)
  have hEq : P.modelDefectResidualDensity E =ᵐ[volume.restrict Y] (fun x => SS x+FS x+Q x) := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    have hh := P.modelDefectResidualDensity_decomposition hY hΩ hd (zero_lt_one.trans_le hK) E hx (W x hx)
    simpa only [Q,PhysicalPrincipalData.potentialModelDefectDensityFamily,dite_eq_left hx] using hh
  have hInt : IntegrableOn (P.modelDefectResidualDensity E) Y := ((hSSI.add hFSI).add hQI).congr hEq.symm
  have hSSInt : (∫ x in Y,SS x)=∑ a : I,∑ b : I,∫ x in Y,S a b x := by
    rw [integral_finsetSum (f:=fun a x => ∑ b : I,S a b x) Finset.univ
      (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hSI a b))]
    apply Finset.sum_congr rfl
    intro a _
    exact integral_finsetSum Finset.univ (fun b _ => hSI a b)
  have hFSInt : (∫ x in Y,FS x)=∑ b : I,∫ x in Y,F b x :=
    integral_finsetSum Finset.univ (fun b _ => hFI b)
  have hSB (a b : I) : |∫ x in Y,S a b x| ≤ CS*EN := by
    simpa only [EN,mul_assoc] using (hSD a b).2.2.2
  have hFB (b : I) : |∫ x in Y,F b x| ≤ CFB*EN := by
    simpa only [EN,mul_assoc] using (hFD b).2
  have hQB : |∫ x in Y,Q x| ≤ CQ*EN := by simpa only [EN,mul_assoc] using hQD.2
  have hSSB : |∫ x in Y,SS x| ≤ 9*CS*EN := by
    rw [hSSInt]
    have hh := abs_fin_three_sum_le (fun a => ∑ b : I,∫ x in Y,S a b x)
      (3*(CS*EN)) (fun a => abs_fin_three_sum_le _ (CS*EN) (hSB a))
    convert hh using 1 <;> ring
  have hFSB : |∫ x in Y,FS x| ≤ 3*CFB*EN := by
    rw [hFSInt]
    have hh := abs_fin_three_sum_le (fun b => ∫ x in Y,F b x) (CFB*EN) hFB
    convert hh using 1 <;> ring
  have hIntegral : (∫ x in Y,P.modelDefectResidualDensity E x)=
      (∫ x in Y,SS x)+(∫ x in Y,FS x)+(∫ x in Y,Q x) := by
    calc
      _ = ∫ x in Y,SS x+FS x+Q x := integral_congr_ae hEq
      _ = (∫ x in Y,SS x+FS x)+(∫ x in Y,Q x) := integral_add (hSSI.add hFSI) hQI
      _ = _ := by rw [integral_add hSSI hFSI]
  refine ⟨hInt,?_⟩
  rw [hIntegral]
  calc
    _ ≤ (|∫ x in Y,SS x|+|∫ x in Y,FS x|)+|∫ x in Y,Q x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (9*CS*EN+3*CFB*EN)+CQ*EN := add_le_add (add_le_add hSSB hFSB) hQB
    _ = _ := by dsimp only [C,EN];ring

end ShrinkingSpheres
