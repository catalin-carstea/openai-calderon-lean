import Proof.PhysicalScalarSelfSquareIdentity
import Proof.PhysicalScalarAdjointDefectIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres

lemma abs_fin_three_sum_le (f : I → ℝ) (C : ℝ) (h : ∀ i,|f i| ≤ C) :
    |∑ i : I,f i| ≤ 3*C := by
  calc
    _ ≤ ∑ i : I,|f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I,C := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

/-- Complete actual scalar second-base self norm comparison, with the
formal transpose on the genuine common supported core. -/
theorem uniform_physical_scalar_self_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      IntegrableOn (scalarSelfNormDifferenceDensity d E) Y ∧
        |∫ y in Y,scalarSelfNormDifferenceDensity d E y| ≤
          C*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨CF,hCF,hFData⟩ := uniform_physical_scalar_third_cross_integral_bound hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  obtain ⟨CZ,hCZ,hZData⟩ := uniform_physical_scalar_second_zero_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK
  obtain ⟨CB,hCB,hBData⟩ := uniform_physical_scalar_adjoint_defect_square_integral_bound hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  refine ⟨54*CF+18*CZ+CB,by positivity,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ
  let F := fun i j l => scalarThirdCrossDensity d E (scalarAdjointProductWeight d.γ d.g₂ d.radius i j l) i j l
  let Z := fun i j => scalarSecondZeroDensity d E (scalarAdjointZeroProductWeight d.γ d.g₂ d.radius i j) i j
  let B := scalarAdjointDefectSquareDensity d E
  let FS := fun x => ∑ i : I,∑ j : I,∑ l : I,F i j l x
  let ZS := fun x => ∑ i : I,∑ j : I,Z i j x
  let EN := ε^2*energySq Y d.γ d.frame d.radius φ
  have hFD (i j l : I) := hFData floor hf ε hε hε1 d hd φ E D hφ i j l i j l
  have hZD (i j : I) := hZData floor hf ε hε hε1 d hd φ E D hφ i j i j
  have hBD := hBData floor hf ε hε hε1 d hd φ E D hφ
  have hFI (i j l : I) : IntegrableOn (F i j l) Y := (hFD i j l).1
  have hZI (i j : I) : IntegrableOn (Z i j) Y := (hZD i j).1
  have hBI : IntegrableOn B Y := hBD.1
  have hFSI : IntegrableOn FS Y := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun l _ => hFI i j l)))
  have hZSI : IntegrableOn ZS Y := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hZI i j))
  have hRHSI : IntegrableOn (fun x => -2*FS x-2*ZS x-B x) Y :=
    ((hFSI.const_mul (-2)).sub (hZSI.const_mul 2)).sub hBI
  have hEq : scalarSelfNormDifferenceDensity d E =ᵐ[volume.restrict Y]
      (fun x => -2*FS x-2*ZS x-B x) := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    exact physical_scalar_self_square_identity hY hSub (zero_lt_one.trans_le hK) d hd E hx
  have hInt : IntegrableOn (scalarSelfNormDifferenceDensity d E) Y := hRHSI.congr hEq.symm
  have hFSInt : (∫ x in Y,FS x)=∑ i : I,∑ j : I,∑ l : I,∫ x in Y,F i j l x := by
    rw [integral_finsetSum (f:=fun i x => ∑ j : I,∑ l : I,F i j l x) Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun l _ => hFI i j l)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun l _ => hFI i j l))]
    apply Finset.sum_congr rfl
    intro j _
    exact integral_finsetSum Finset.univ (fun l _ => hFI i j l)
  have hZSInt : (∫ x in Y,ZS x)=∑ i : I,∑ j : I,∫ x in Y,Z i j x := by
    rw [integral_finsetSum (f:=fun i x => ∑ j : I,Z i j x) Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hZI i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hZI i j)
  have hFB (i j l : I) : |∫ x in Y,F i j l x| ≤ CF*EN := by
    have hh := (hFD i j l).2.2.2
    change |2*(∫ x in Y,F i j l x)| ≤ CF*ε^2*energySq Y d.γ d.frame d.radius φ at hh
    rw [abs_mul,show |(2:ℝ)|=2 by norm_num] at hh
    dsimp only [EN]
    nlinarith only [hh,abs_nonneg (∫ x in Y,F i j l x)]
  have hZB (i j : I) : |∫ x in Y,Z i j x| ≤ CZ*EN := by
    simpa only [EN,mul_assoc] using (hZD i j).2.2.2
  have hBB : |∫ x in Y,B x| ≤ CB*EN := by simpa only [EN,mul_assoc] using hBD.2
  have hFSB : |∫ x in Y,FS x| ≤ 27*CF*EN := by
    rw [hFSInt]
    have hh := abs_fin_three_sum_le (fun i => ∑ j : I,∑ l : I,∫ x in Y,F i j l x)
      (3*(3*(CF*EN))) (fun i => abs_fin_three_sum_le _ (3*(CF*EN)) (fun j =>
        abs_fin_three_sum_le _ (CF*EN) (hFB i j)))
    convert hh using 1 <;> ring
  have hZSB : |∫ x in Y,ZS x| ≤ 9*CZ*EN := by
    rw [hZSInt]
    have hh := abs_fin_three_sum_le (fun i => ∑ j : I,∫ x in Y,Z i j x)
      (3*(CZ*EN)) (fun i => abs_fin_three_sum_le _ (CZ*EN) (hZB i))
    convert hh using 1 <;> ring
  have hIntegral : (∫ x in Y,scalarSelfNormDifferenceDensity d E x)=
      -2*(∫ x in Y,FS x)-2*(∫ x in Y,ZS x)-(∫ x in Y,B x) := by
    have hFirst : (∫ x in Y,-2*FS x-2*ZS x)= -2*(∫ x in Y,FS x)-2*(∫ x in Y,ZS x) := by
      calc
        _ = (∫ x in Y,-2*FS x)-(∫ x in Y,2*ZS x) :=
          integral_sub (hFSI.const_mul (-2)) (hZSI.const_mul 2)
        _ = _ := by rw [integral_const_mul,integral_const_mul]
    calc
      _ = ∫ x in Y,-2*FS x-2*ZS x-B x := integral_congr_ae hEq
      _ = (∫ x in Y,-2*FS x-2*ZS x)-(∫ x in Y,B x) :=
        integral_sub ((hFSI.const_mul (-2)).sub (hZSI.const_mul 2)) hBI
      _ = _ := by rw [hFirst]
  refine ⟨hInt,?_⟩
  rw [hIntegral]
  calc
    _ ≤ |-2*(∫ x in Y,FS x)-2*(∫ x in Y,ZS x)|+|∫ x in Y,B x| := abs_sub _ _
    _ ≤ (|-2*(∫ x in Y,FS x)|+|2*(∫ x in Y,ZS x)|)+|∫ x in Y,B x| :=
      add_le_add (abs_sub _ _) le_rfl
    _ = 2*|∫ x in Y,FS x|+2*|∫ x in Y,ZS x|+|∫ x in Y,B x| := by
      simp only [abs_mul,abs_neg,show |(2:ℝ)|=2 by norm_num]
    _ ≤ 2*(27*CF*EN)+2*(9*CZ*EN)+CB*EN := by linarith only [hFSB,hZSB,hBB]
    _ = _ := by dsimp only [EN];ring

end ShrinkingSpheres
