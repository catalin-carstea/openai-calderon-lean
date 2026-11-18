import Proof.AdmissibleRadiusSmallJets
import Proof.PrincipalModelDegreeCoordinateWeights
import Proof.CoordinateFiniteSumCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.PrincipalCommutator

def principalModelDegreeCoordinateTwoJetBudget (K M1 M2 C2 C3 : ℝ) : ℝ :=
  principalModelDegreeCoordinateBudget K M1 C2+
    24*((K+1)+(9*K^2*|M1|+1)+(162*K^3*|M1|^2+9*K^2*|M2|+1))*
      (K+(K^2+9*K^2*|C2|+27*K^2*|M1|)+
        profileRadiusThirdBudget K (9*K*|M1|) (81*K^2*|M1|^2+9*K*|M2|) C2 C3)

lemma principalModelDegreeCoordinateTwoJetBudget_nonneg (K M1 M2 C2 C3 : ℝ)
    (hK : 0 ≤ K) : 0 ≤ principalModelDegreeCoordinateTwoJetBudget K M1 M2 C2 C3 := by
  have hOld := principalModelDegreeCoordinateBudget_nonneg K M1 C2 hK
  have hG : 0 ≤ 9*K*|M1| := by positivity
  have hDG : 0 ≤ 81*K^2*|M1|^2+9*K*|M2| := by positivity
  have hThird := profileRadiusThirdBudget_nonneg K _ _ C2 C3 hK hG hDG
  unfold principalModelDegreeCoordinateTwoJetBudget
  positivity

/-- The SAME actual degree coordinate weight has the epsilon/beta,
epsilon and epsilon beta weights through two base derivatives. -/
theorem Admissible.principalModelDegreeCoordinateWeight_two_jet_bounds {Y Ω : Set X}
    (hY : IsOpen Y) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (b i j : I) :
    let B := principalModelDegreeCoordinateTwoJetBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2) (Cj 3)
    0 ≤ B ∧ |principalModelDegreeCoordinateWeight d b y| ≤ B*ε/beta d.γ d.radius y ∧
      |fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i)| ≤ B*ε ∧
      |fderiv ℝ (fun x => fderiv ℝ (principalModelDegreeCoordinateWeight d b) x (axis i))
        y (axis j)| ≤ B*ε*beta d.γ d.radius y := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let G := 9*K*M1
  let DG := 81*K^2*M1^2+9*K*M2
  let R2 := K^2+9*K^2*|Cj 2|+27*K^2*M1
  let R3 := profileRadiusThirdBudget K G DG (Cj 2) (Cj 3)
  let CR := K+R2+R3
  let CQ := (K+1)+(9*K^2*M1+1)+(162*K^3*M1^2+9*K^2*M2+1)
  let B1 := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)
  let B := principalModelDegreeCoordinateTwoJetBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2) (Cj 3)
  let β := beta d.γ d.radius y
  have hK0 := zero_le_one.trans hK
  have hKP := zero_lt_one.trans_le hK
  have hM1 : 0 ≤ M1 := abs_nonneg _
  have hM2 : 0 ≤ M2 := abs_nonneg _
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hDG : 0 ≤ DG := by dsimp only [DG];positivity
  have hR2 : 0 ≤ R2 := by dsimp only [R2];positivity
  have hR3 : 0 ≤ R3 := profileRadiusThirdBudget_nonneg _ _ _ _ _ hK0 hG hDG
  have hCR : 0 ≤ CR := by dsimp only [CR];positivity
  have hCQ : 0 ≤ CQ := by dsimp only [CQ];positivity
  have hN0 : 0 ≤ K+1 := by positivity
  have hN1 : 0 ≤ 9*K^2*M1+1 := by positivity
  have hN2 : 0 ≤ 162*K^3*M1^2+9*K^2*M2+1 := by positivity
  have hB1 : 0 ≤ B1 := principalModelDegreeCoordinateBudget_nonneg _ _ _ hK0
  have hBB : B = B1+24*CQ*CR := rfl
  have hB1B : B1 ≤ B := by rw [hBB];exact le_add_of_nonneg_right (by positivity)
  have hProdB : 24*CQ*CR ≤ B := by rw [hBB];linarith only [hB1]
  have hB : 0 ≤ B := hB1.trans hB1B
  have hβ1 : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ : 0 ≤ β := zero_le_one.trans hβ1
  have hβP : 0 < β := zero_lt_one.trans_le hβ1
  have h01 := hd.principalModelDegreeCoordinateWeight_bounds hY (by omega) hK hf hε hε1 hy b i
  refine ⟨hB,h01.1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB1B hε) hβ),
    h01.2.trans (mul_le_mul_of_nonneg_right hB1B hε),?_⟩
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun a c => (hd.1.1.1 a c).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ := ⟨fun a c => (hd.1.2.2.1.1 a c).mono hSub,
    fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have hMetric1 (a c : I) : ‖fderiv ℝ (fun x => d.γ x a c) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound (by omega) (hSub hy) a c).trans (le_abs_self _)
  have hMetric2 (a c : I) : ‖fderiv ℝ (fderiv ℝ (fun x => d.γ x a c)) y‖ ≤ M2 :=
    (hd.1.reference_second_fderiv_bound hm (hSub hy) a c).trans (le_abs_self _)
  have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
  have hr1 : d.radius y ≤ 1 :=
    ((radius_bounds (d.radius y) β floor ε hr hf (hd.2.2.2.2.1.2 y hy).2.1
      (hd.2.2.2.2.2 y hy).2).2.2).trans hε1
  have hεr : ε*d.radius y ≤ 1 :=
    (mul_le_mul_of_nonneg_right hε1 hr).trans (by simpa only [one_mul] using hr1)
  have hQ0 (a c : I) : |principal d.γ d.g₂ y a c| ≤ CQ := by
    have hh := (principal_entry_le_inverse_add hg hKP hd.2.2.2.2.2 hy a c).trans
      (show K+ε*d.radius y ≤ K+1 by linarith only [hεr])
    exact hh.trans (by dsimp only [CQ];linarith only [hN1,hN2])
  have hQ1 (a c t : I) : |coordDeriv t (fun x => principal d.γ d.g₂ x a c) y| ≤ CQ := by
    have hh := (principal_derivative_le_inverse_add hY hg hg2 hKP hd.2.2.2.2.2 hy
      M1 hM1 hMetric1 a c t).trans
        (show 9*K^2*M1+ε*d.radius y ≤ 9*K^2*M1+1 by linarith only [hεr])
    exact hh.trans (by dsimp only [CQ];linarith only [hN0,hN2])
  have hQ2 (a c : I) : |coordDeriv j (coordDeriv i (fun x => principal d.γ d.g₂ x a c)) y| ≤ CQ := by
    have hh := (principal_second_le_inverse_add hY hg hg2 hKP hd.2.2.2.2.2 hy
      M1 M2 hM1 hM2 hMetric1 hMetric2 a c i j).trans
        (show 162*K^3*M1^2+9*K^2*M2+ε*d.radius y ≤ 162*K^3*M1^2+9*K^2*M2+1 by linarith only [hεr])
    exact hh.trans (by dsimp only [CQ];linarith only [hN0,hN1])
  have hGrow (A : ℝ) (hA : 0 ≤ A) (hACR : A ≤ CR) : A*ε ≤ CR*ε*β := by
    exact (mul_le_mul_of_nonneg_right hACR hε).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ1 (mul_nonneg hCR hε))
  have hRad1 (a : I) : |coordDeriv a d.radius y| ≤ CR*ε*β := by
    have hh := (hd.coordinate_radius_two_small_jet_bounds hY (by omega) hK hf hy a i).1
    exact hh.trans ((div_le_self (mul_nonneg hK0 hε) hβ1).trans
      (hGrow K hK0 (by dsimp only [CR];linarith only [hR2,hR3])))
  have hRad2 (a t : I) : |coordDeriv t (coordDeriv a d.radius) y| ≤ CR*ε*β := by
    have hh := (hd.coordinate_radius_two_small_jet_bounds hY (by omega) hK hf hy a t).2
    exact hh.trans (hGrow R2 hR2 (by dsimp only [CR];linarith only [hK0,hR3]))
  have hRad3 (a : I) : |coordDeriv j (coordDeriv i (coordDeriv a d.radius)) y| ≤ CR*ε*β := by
    have hh := hd.coordinate_radius_third_small_jet_bound hY hm hK hf hy a i j
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show R3 ≤ CR by dsimp only [CR];linarith only [hK0,hR2]) hε) hβ)
  have hRadS (a : I) : ContDiffOn ℝ ∞ (coordDeriv a d.radius) Y :=
    contDiffOn_coordDeriv hY hd.2.2.2.2.1.1 a
  have hPS (a c : I) : ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x a c) Y :=
    contDiffOn_principal_entry hg hg2 hKP a c
  have hEach (a c t : I) :
      |coordDeriv j (coordDeriv i (fun x => principal d.γ d.g₂ x a c*coordDeriv t d.radius x)) y| ≤
        4*CQ*CR*ε*β := by
    rw [coordinate_second_mul hY (hPS a c) (hRadS t) hy j i]
    have hMul {u v : ℝ} (hu : |u| ≤ CQ) (hv : |v| ≤ CR*ε*β) : |u*v| ≤ CQ*(CR*ε*β) := by
      rw [abs_mul]
      exact mul_le_mul hu hv (abs_nonneg _) hCQ
    have h0 := hMul (hQ2 a c) (hRad1 t)
    have h1 := hMul (hQ1 a c i) (hRad2 t j)
    have h2 := hMul (hQ1 a c j) (hRad2 t i)
    have h3 := hMul (hQ0 a c) (hRad3 t)
    have hFour {u v w z : ℝ} (hu : |u| ≤ CQ*(CR*ε*β)) (hv : |v| ≤ CQ*(CR*ε*β))
        (hw : |w| ≤ CQ*(CR*ε*β)) (hz : |z| ≤ CQ*(CR*ε*β)) :
        |u+v+w+z| ≤ 4*CQ*CR*ε*β := by
      have hAbs : |u+v+w+z| ≤ |u|+|v|+|w|+|z| :=
        (abs_add_le (u+v+w) z).trans (add_le_add
          ((abs_add_le (u+v) w).trans (add_le_add (abs_add_le u v) le_rfl)) le_rfl)
      exact hAbs.trans ((add_le_add (add_le_add (add_le_add hu hv) hw) hz).trans_eq (by ring))
    exact hFour h0 h1 h2 h3
  let f := fun (a : I) (k : Fin 2) (x : X) =>
    if k=0 then principal d.γ d.g₂ x a b*coordDeriv a d.radius x
    else principal d.γ d.g₂ x b a*coordDeriv a d.radius x
  have hfs (a : I) (k : Fin 2) : ContDiffOn ℝ ∞ (f a k) Y := by
    dsimp only [f]
    split_ifs
    · exact (hPS a b).mul (hRadS a)
    · exact (hPS b a).mul (hRadS a)
  have hfun : principalModelDegreeCoordinateWeight d b = fun x => ∑ a : I,∑ k : Fin 2,f a k x := by
    funext x
    unfold principalModelDegreeCoordinateWeight
    apply Finset.sum_congr rfl
    intro a _
    simp only [Fin.sum_univ_two,f,ite_true,show ¬(1:Fin 2)=0 by decide,ite_false]
    ring
  have hSecondSum : coordDeriv j (coordDeriv i (principalModelDegreeCoordinateWeight d b)) y =
      ∑ a : I,∑ k : Fin 2,coordDeriv j (coordDeriv i (f a k)) y := by
    rw [hfun,coordinate_second_sum hY (fun a x => ∑ k : Fin 2,f a k x)
      (fun a => ContDiffOn.sum (fun k _ => hfs a k)) hy j i]
    apply Finset.sum_congr rfl
    intro a _
    exact coordinate_second_sum hY (f a) (hfs a) hy j i
  have hfBound (a : I) (k : Fin 2) : |coordDeriv j (coordDeriv i (f a k)) y| ≤ 4*CQ*CR*ε*β := by
    dsimp only [f]
    split_ifs
    · exact hEach a b a
    · exact hEach b a a
  change |coordDeriv j (coordDeriv i (principalModelDegreeCoordinateWeight d b)) y| ≤ _
  rw [hSecondSum]
  calc
    _ ≤ ∑ a : I,|∑ k : Fin 2,coordDeriv j (coordDeriv i (f a k)) y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : I,∑ k : Fin 2,|coordDeriv j (coordDeriv i (f a k)) y| :=
      Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _a : I,∑ _k : Fin 2,4*CQ*CR*ε*β :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun k _ => hfBound a k))
    _ = (24*CQ*CR)*ε*β := by simp only [Fin.sum_univ_three,Fin.sum_univ_two];ring
    _ ≤ B*ε*β := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hProdB hε) hβ

end ShrinkingSpheres
