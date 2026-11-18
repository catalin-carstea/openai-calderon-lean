import Proof.ParallelNormAssemblyReservedNormalizedWords
import Proof.ParallelNormAssemblyReservedPotentialScalarInputs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

def normalizedPotentialCoefficientBody (d : Data) (y : X) :
    PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ
  | .inl _,.inl _ => ∑ a : I,∑ b : I,
      (scalarPrincipalMatrix d.γ d.g₂ d.radius y a b*coordDeriv a (fun x => Real.log (d.radius x)) y)*
        coordDeriv b (fun x => Real.log (d.radius x)) y
  | .inl _,.inr (.inl _) => 0
  | .inl _,.inr (.inr b) => ∑ a : I,
      (d.radius y*scalarPrincipalMatrix d.γ d.g₂ d.radius y a b)*
        coordDeriv a (fun x => Real.log (d.radius x)) y
  | .inr (.inl a),.inl _ => 2*∑ b : I,
      (d.radius y*potentialCoordinateWordCoefficient d y (.inr (.inl a)) (.inr (.inl b)))*
        coordDeriv b (fun x => Real.log (d.radius x)) y
  | .inr (.inl a),.inr (.inl b) =>
      potentialCoordinateWordCoefficient d y (.inr (.inl a)) (.inr (.inl b))
  | .inr (.inl a),.inr (.inr b) => scalarPrincipalMatrix d.γ d.g₂ d.radius y a b
  | .inr (.inr a),.inl _ => ∑ b : I,
      (d.radius y*scalarPrincipalMatrix d.γ d.g₂ d.radius y a b)*
        coordDeriv b (fun x => Real.log (d.radius x)) y
  | .inr (.inr a),.inr (.inl b) => scalarPrincipalMatrix d.γ d.g₂ d.radius y a b
  | .inr (.inr a),.inr (.inr b) =>
      (d.radius y*d.radius y)*scalarPrincipalMatrix d.γ d.g₂ d.radius y a b

lemma normalized_potential_coefficient_body (d : Data) (y : X) (hr : d.radius y ≠ 0)
    (a b : PhysicalPotentialGeneratorIndex) :
    normalizedPotentialWordCoefficient d y a b=normalizedPotentialCoefficientBody d y a b := by
  rcases a with u | (a | a) <;> rcases b with v | (b | b)
  all_goals simp only [normalizedPotentialWordCoefficient,normalizedPotentialCoefficientBody,
    potentialCoordinateWordCoefficient,potentialGeneratorWeight,scalarPrincipalMatrix,
    Matrix.smul_apply,smul_eq_mul,mul_one,one_mul,coordDeriv,Fin.sum_univ_three]
  all_goals field_simp [hr] <;> ring

lemma ScalarTwoJetBound.congr_on {Y : Set X} (hY : IsOpen Y) {f g : X → ℝ}
    (hfg : EqOn f g Y) {y : X} (hy : y ∈ Y) {β t : ℝ}
    (h : ScalarTwoJetBound g y β t) : ScalarTwoJetBound f y β t := by
  have hD (i : I) : EqOn (coordDeriv i f) (coordDeriv i g) Y := by
    intro x hx
    have hEq : f=ᶠ[𝓝 x] g := by filter_upwards [hY.mem_nhds hx] with z hz using hfg hz
    exact congrArg (fun L : X →L[ℝ] ℝ => L (axis i)) hEq.fderiv_eq
  have hDD (i j : I) : coordDeriv j (coordDeriv i f) y=coordDeriv j (coordDeriv i g) y := by
    have hEq : coordDeriv i f=ᶠ[𝓝 y] coordDeriv i g := by
      filter_upwards [hY.mem_nhds hy] with z hz using hD i hz
    exact congrArg (fun L : X →L[ℝ] ℝ => L (axis j)) hEq.fderiv_eq
  exact ⟨by simpa only [hfg hy] using h.value,
    fun i => by simpa only [hD i hy] using h.first i,
    fun i j => by simpa only [hDD i j] using h.second i j⟩

/-- Quantitative two-jet assembly for ALL normalized potential
coefficients, through the actual radius and invariant scalar inputs. -/
theorem normalized_potential_coefficient_two_jets_of_inputs {Y : Set X}
    (hY : IsOpen Y) {d : Data} {y : X} (hy : y ∈ Y)
    (hR : ContDiffOn ℝ ∞ d.radius Y) (hRadius : ∀ x ∈ Y,0 < d.radius x)
    (hP : ∀ a b : I,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x a b) Y)
    (hQ : ∀ a b : I,ContDiffOn ℝ ∞ (fun x => (d.γ x)⁻¹ a b) Y)
    {Cr Cl Cp Ce ε β : ℝ} (hCr : 0 ≤ Cr) (hCl : 0 ≤ Cl) (hCp : 0 ≤ Cp) (hCe : 0 ≤ Ce)
    (hε : 0 ≤ ε) (hβ : 1 ≤ β)
    (hRad : ScalarTwoJetBound d.radius y β (Cr/β))
    (hLog : ∀ a : I,ScalarTwoJetBound (coordDeriv a (fun x => Real.log (d.radius x))) y β (Cl*β))
    (hScalar : ∀ a b : I,ScalarTwoJetBound (fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b) y β (Cp*ε/β^2))
    (hPure : ∀ a b : I,ScalarTwoJetBound
      (fun x => potentialCoordinateWordCoefficient d x (.inr (.inl a)) (.inr (.inl b))) y β (Ce*ε)) :
    ∀ a b : PhysicalPotentialGeneratorIndex,
    ScalarTwoJetBound (fun x => normalizedPotentialWordCoefficient d x a b) y β
      ((144*Cp*Cl^2+96*Cr*Ce*Cl+48*Cr*Cp*Cl+16*Cr^2*Cp+Cp+Ce)*ε) := by
  let C := 144*Cp*Cl^2+96*Cr*Ce*Cl+48*Cr*Cp*Cl+16*Cr^2*Cp+Cp+Ce
  have hβP : 0 < β := zero_lt_one.trans_le hβ
  have hβ0 := hβP.le
  have hβ2 : 1 ≤ β^2 := one_le_pow₀ hβ
  have hLogs : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y := hR.log (fun x hx => (hRadius x hx).ne')
  have hFs (a : I) := contDiffOn_coordDeriv hY hLogs a
  have hSs (a b : I) : ContDiffOn ℝ ∞ (fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b) Y := by
    simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using hR.mul (hP a b)
  have hEs (a b : I) : ContDiffOn ℝ ∞
      (fun x => potentialCoordinateWordCoefficient d x (.inr (.inl a)) (.inr (.inl b))) Y := by
    simpa only [potentialCoordinateWordCoefficient,Matrix.sub_apply,div_eq_mul_inv,Pi.inv_apply] using
      ((hP a b).sub (hQ a b)).mul (hR.inv (fun x hx => (hRadius x hx).ne'))
  have hDD0 : 0 ≤ 144*Cp*Cl^2 := by positivity
  have hRD0 : 0 ≤ 96*Cr*Ce*Cl := by positivity
  have hDE0 : 0 ≤ 48*Cr*Cp*Cl := by positivity
  have hEE0 : 0 ≤ 16*Cr^2*Cp := by positivity
  have hDDC : 144*Cp*Cl^2 ≤ C := by dsimp only [C];linarith only [hRD0,hDE0,hEE0,hCp,hCe]
  have hRDC : 96*Cr*Ce*Cl ≤ C := by dsimp only [C];linarith only [hDD0,hDE0,hEE0,hCp,hCe]
  have hDEC : 48*Cr*Cp*Cl ≤ C := by dsimp only [C];linarith only [hDD0,hRD0,hEE0,hCp,hCe]
  have hEEC : 16*Cr^2*Cp ≤ C := by dsimp only [C];linarith only [hDD0,hRD0,hDE0,hCp,hCe]
  have hCpC : Cp ≤ C := by dsimp only [C];linarith only [hDD0,hRD0,hDE0,hEE0,hCe]
  have hCeC : Ce ≤ C := by dsimp only [C];linarith only [hDD0,hRD0,hDE0,hEE0,hCp]
  have hDominates (A : ℝ) (hAC : A ≤ C) : A*ε ≤ C*ε := mul_le_mul_of_nonneg_right hAC hε
  have hDD (a b : I) : ScalarTwoJetBound
      (fun x => (scalarPrincipalMatrix d.γ d.g₂ d.radius x a b*coordDeriv a (fun x => Real.log (d.radius x)) x)*
        coordDeriv b (fun x => Real.log (d.radius x)) x) y β (16*Cp*Cl^2*ε) := by
    have hh := ((hScalar a b).mul hY (hSs a b) (hFs a) hy hβ0 (by positivity) (by positivity) (hLog a)).mul
      hY ((hSs a b).mul (hFs a)) (hFs b) hy hβ0 (by positivity) (by positivity) (hLog b)
    convert hh using 1 <;> field_simp <;> ring
  have hRE (a b c : I) : ScalarTwoJetBound
      (fun x => (d.radius x*scalarPrincipalMatrix d.γ d.g₂ d.radius x a b)*
        coordDeriv c (fun x => Real.log (d.radius x)) x) y β (16*Cr*Cp*Cl*ε) := by
    have hh := (hRad.mul hY hR (hSs a b) hy hβ0 (by positivity) (by positivity) (hScalar a b)).mul
      hY (hR.mul (hSs a b)) (hFs c) hy hβ0 (by positivity) (by positivity) (hLog c)
    apply hh.mono hβ0
    have hn : 0 ≤ 16*Cr*Cp*Cl*ε := by positivity
    calc
      _ = (16*Cr*Cp*Cl*ε)/β^2 := by field_simp <;> ring
      _ ≤ _ := div_le_self hn hβ2
  have hRF (a b c : I) : ScalarTwoJetBound
      (fun x => (d.radius x*potentialCoordinateWordCoefficient d x (.inr (.inl a)) (.inr (.inl b)))*
        coordDeriv c (fun x => Real.log (d.radius x)) x) y β (16*Cr*Ce*Cl*ε) := by
    have hh := (hRad.mul hY hR (hEs a b) hy hβ0 (by positivity) (by positivity) (hPure a b)).mul
      hY (hR.mul (hEs a b)) (hFs c) hy hβ0 (by positivity) (by positivity) (hLog c)
    convert hh using 1 <;> field_simp <;> ring
  have hEE (a b : I) : ScalarTwoJetBound
      (fun x => (d.radius x*d.radius x)*scalarPrincipalMatrix d.γ d.g₂ d.radius x a b) y β (16*Cr^2*Cp*ε) := by
    have hh := (hRad.mul hY hR hR hy hβ0 (by positivity) (by positivity) hRad).mul
      hY (hR.mul hR) (hSs a b) hy hβ0 (by positivity) (by positivity) (hScalar a b)
    apply hh.mono hβ0
    have hn : 0 ≤ 16*Cr^2*Cp*ε := by positivity
    calc
      _ = (16*Cr^2*Cp*ε)/(β^2)^2 := by field_simp <;> ring
      _ ≤ _ := div_le_self hn (one_le_pow₀ hβ2)
  have hSc (a b : I) : ScalarTwoJetBound
      (fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b) y β (Cp*ε) :=
    (hScalar a b).mono hβ0 (div_le_self (mul_nonneg hCp hε) hβ2)
  intro a b
  apply ScalarTwoJetBound.congr_on hY (fun x hx => normalized_potential_coefficient_body d x (hRadius x hx).ne' a b) hy
  rcases a with u | (a | a) <;> rcases b with v | (b | b)
  all_goals try dsimp only [normalizedPotentialCoefficientBody]
  · have hh := ScalarTwoJetBound.sum hY _ (fun a => ContDiffOn.sum (fun b _ => ((hSs a b).mul (hFs a)).mul (hFs b))) hy
      (fun _ : I => 3*(16*Cp*Cl^2*ε)) (fun a => by
        convert ScalarTwoJetBound.sum hY _ (fun b => ((hSs a b).mul (hFs a)).mul (hFs b)) hy
          (fun _ : I => 16*Cp*Cl^2*ε) (fun b => hDD a b) using 1 <;> simp only [Fin.sum_univ_three] <;> ring)
    apply hh.mono hβ0
    simp only [Fin.sum_univ_three]
    convert hDominates (144*Cp*Cl^2) hDDC using 1 <;> ring
  · exact (scalarTwoJetBound_zero y β).mono hβ0 (by positivity)
  · have hh := ScalarTwoJetBound.sum hY _ (fun a => (hR.mul (hSs a b)).mul (hFs a)) hy
      (fun _ : I => 16*Cr*Cp*Cl*ε) (fun a => hRE a b a)
    apply hh.mono hβ0
    simp only [Fin.sum_univ_three]
    convert hDominates (48*Cr*Cp*Cl) hDEC using 1 <;> ring
  · have hh := (ScalarTwoJetBound.sum hY _ (fun b => (hR.mul (hEs a b)).mul (hFs b)) hy
      (fun _ : I => 16*Cr*Ce*Cl*ε) (fun b => hRF a b b)).const_mul hY
      (ContDiffOn.sum (fun b _ => (hR.mul (hEs a b)).mul (hFs b))) hy 2
    apply hh.mono hβ0
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2),Fin.sum_univ_three]
    convert hDominates (96*Cr*Ce*Cl) hRDC using 1 <;> ring
  · exact (hPure a b).mono hβ0 (hDominates Ce hCeC)
  · exact (hSc a b).mono hβ0 (hDominates Cp hCpC)
  · have hh := ScalarTwoJetBound.sum hY _ (fun b => (hR.mul (hSs a b)).mul (hFs b)) hy
      (fun _ : I => 16*Cr*Cp*Cl*ε) (fun b => hRE a b b)
    apply hh.mono hβ0
    simp only [Fin.sum_univ_three]
    convert hDominates (48*Cr*Cp*Cl) hDEC using 1 <;> ring
  · exact (hSc a b).mono hβ0 (hDominates Cp hCpC)
  · exact (hEE a b).mono hβ0 (hDominates (16*Cr^2*Cp) hEEC)

end ShrinkingSpheres.ParallelEnergy
