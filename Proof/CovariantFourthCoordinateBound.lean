import Proof.CovariantJetCoordinateDerivative
import Proof.CoordinateScalarFirstRules
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def fourthCoordinateJetBudget (B1 B2 B3 H2 H3 H4 G DG DDG : ℝ) : ℝ :=
  (H4+9*G*H3)+3*(DDG*B1+2*DG*B2+G*B3)+6*(DG*H2+G*(H3+6*G*H2))

lemma fourthCoordinateJetBudget_nonneg (B1 B2 B3 H2 H3 H4 G DG DDG : ℝ)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hB3 : 0 ≤ B3)
    (hH2 : 0 ≤ H2) (hH3 : 0 ≤ H3) (hH4 : 0 ≤ H4)
    (hG : 0 ≤ G) (hDG : 0 ≤ DG) (hDDG : 0 ≤ DDG) :
    0 ≤ fourthCoordinateJetBudget B1 B2 B3 H2 H3 H4 G DG DDG := by
  unfold fourthCoordinateJetBudget
  positivity

/-- The fourth coordinate derivative follows from the SAME scalar's fourth
    covariant jet and lower coordinate jets, with explicit connection terms. -/
theorem coordinate_fourth_bound_of_covJets {Y : Set X} (hY : IsOpen Y)
    (g : MetricField) (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f Y)
    (hΓSm : ∀ a b c : I,ContDiffOn ℝ ∞ (fun x => christoffel g x a b c) Y)
    {y : X} (hy : y ∈ Y) (β B1 B2 B3 H2 H3 H4 G DG DDG : ℝ)
    (hβ : 1 ≤ β) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hB3 : 0 ≤ B3)
    (hH2 : 0 ≤ H2) (hH3 : 0 ≤ H3) (hH4 : 0 ≤ H4)
    (hG : 0 ≤ G) (hDG : 0 ≤ DG) (hDDG : 0 ≤ DDG)
    (hΓ : ∀ a b c : I,|christoffel g y a b c| ≤ G)
    (hDΓ : ∀ a b c d : I,|coordDeriv a (fun x => christoffel g x b c d) y| ≤ DG)
    (hDDΓ : ∀ a b c d e : I,|coordDeriv a (coordDeriv b (fun x => christoffel g x c d e)) y| ≤ DDG)
    (hCoord1 : ∀ a : I,|coordDeriv a f y| ≤ B1*β)
    (hCoord2 : ∀ a b : I,|coordDeriv a (coordDeriv b f) y| ≤ B2*β^2)
    (hCoord3 : ∀ a b c : I,|coordDeriv a (coordDeriv b (coordDeriv c f)) y| ≤ B3*β^3)
    (hCov2 : ∀ idx : Fin 2 → I,|covJet g f 2 y idx| ≤ H2*β^2)
    (hCov3 : ∀ idx : Fin 3 → I,|covJet g f 3 y idx| ≤ H3*β^3)
    (hCov4 : ∀ idx : Fin 4 → I,|covJet g f 4 y idx| ≤ H4*β^4)
    (i j k l : I) :
    |coordDeriv i (coordDeriv j (coordDeriv k (coordDeriv l f))) y| ≤
      fourthCoordinateJetBudget B1 B2 B3 H2 H3 H4 G DG DDG*β^4 := by
  have hβ0 := zero_le_one.trans hβ
  have hPower1 : β ≤ β^4 := by simpa only [pow_one] using pow_le_pow_right₀ hβ (show 1 ≤ 4 by omega)
  have hPower2 : β^2 ≤ β^4 := pow_le_pow_right₀ hβ (by omega)
  have hPower3 : β^3 ≤ β^4 := pow_le_pow_right₀ hβ (by omega)
  have hSf (a : I) := contDiffOn_coordDeriv hY hf a
  have hSf2 (a b : I) := contDiffOn_coordDeriv hY (hSf b) a
  have hSf3 (a b c : I) := contDiffOn_coordDeriv hY (hSf2 b c) a
  have hSG (a b c d : I) := contDiffOn_coordDeriv hY (hΓSm b c d) a
  have hSC2 (idx : Fin 2 → I) := contDiffOn_covJet hY g f hf hΓSm 2 idx
  have hSC3 (idx : Fin 3 → I) := contDiffOn_covJet hY g f hf hΓSm 3 idx
  have hDC2 (a : I) (idx : Fin 2 → I) :
      |coordDeriv a (fun x => covJet g f 2 x idx) y| ≤ (H3+6*G*H2)*β^3 := by
    have hh := abs_coordDeriv_covJet_le g f 2 y β G H2 H3 hβ hG hH2 hΓ hCov2 hCov3 a idx
    norm_num only at hh
    exact hh
  have hDC3 : |coordDeriv i (fun x => covJet g f 3 x ![j,k,l]) y| ≤ (H4+9*G*H3)*β^4 := by
    have hh := abs_coordDeriv_covJet_le g f 3 y β G H3 H4 hβ hG hH3 hΓ hCov3 hCov4 i ![j,k,l]
    norm_num only at hh
    exact hh
  let T1 := fun (s : I) (x : X) =>
    coordDeriv j (fun z => christoffel g z s k l) x*coordDeriv s f x+
      christoffel g x s k l*coordDeriv j (coordDeriv s f) x
  let T2 := fun (s : I) (x : X) => christoffel g x s j k*covJet g f 2 x ![s,l]
  let T3 := fun (s : I) (x : X) => christoffel g x s j l*covJet g f 2 x ![k,s]
  have hST1 (s : I) : ContDiffOn ℝ ∞ (T1 s) Y :=
    ((hSG j s k l).mul (hSf s)).add ((hΓSm s k l).mul (hSf2 j s))
  have hST2 (s : I) : ContDiffOn ℝ ∞ (T2 s) Y := (hΓSm s j k).mul (hSC2 ![s,l])
  have hST3 (s : I) : ContDiffOn ℝ ∞ (T3 s) Y := (hΓSm s j l).mul (hSC2 ![k,s])
  let A := fun x => covJet g f 3 x ![j,k,l]
  let B := fun x => ∑ s : I,T1 s x
  let C := fun x => ∑ s : I,T2 s x
  let D := fun x => ∑ s : I,T3 s x
  have hAS : ContDiffOn ℝ ∞ A Y := hSC3 ![j,k,l]
  have hBS : ContDiffOn ℝ ∞ B Y := ContDiffOn.sum (fun s hs => hST1 s)
  have hCS : ContDiffOn ℝ ∞ C Y := ContDiffOn.sum (fun s hs => hST2 s)
  have hDS : ContDiffOn ℝ ∞ D Y := ContDiffOn.sum (fun s hs => hST3 s)
  have hT1 (s : I) : |coordDeriv i (T1 s) y| ≤ (DDG*B1+2*DG*B2+G*B3)*β^4 := by
    have h1 := abs_coordDeriv_mul_le
      (coordDeriv j (fun z => christoffel g z s k l)) (coordDeriv s f)
      (((hSG j s k l).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((hSf s).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i
      hDG hDDG (hDΓ j s k l) (hDDΓ i j s k l) (hCoord1 s) (hCoord2 i s)
    have h2 := abs_coordDeriv_mul_le (fun x => christoffel g x s k l) (coordDeriv j (coordDeriv s f))
      (((hΓSm s k l).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((hSf2 j s).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i
      hG hDG (hΓ s k l) (hDΓ i s k l) (hCoord2 j s) (hCoord3 i j s)
    change |coordDeriv i (fun x =>
      coordDeriv j (fun z => christoffel g z s k l) x*coordDeriv s f x+
        christoffel g x s k l*coordDeriv j (coordDeriv s f) x) y| ≤ _
    rw [coordDeriv_add_at _ _
      ((((hSG j s k l).mul (hSf s)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      ((((hΓSm s k l).mul (hSf2 j s)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i]
    calc
      _ ≤ |coordDeriv i (fun x => coordDeriv j (fun z => christoffel g z s k l) x*coordDeriv s f x) y|+
          |coordDeriv i (fun x => christoffel g x s k l*coordDeriv j (coordDeriv s f) x) y| := abs_add_le _ _
      _ ≤ (DDG*(B1*β)+DG*(B2*β^2))+(DG*(B2*β^2)+G*(B3*β^3)) := add_le_add h1 h2
      _ = DDG*B1*β+2*DG*B2*β^2+G*B3*β^3 := by ring
      _ ≤ DDG*B1*β^4+2*DG*B2*β^4+G*B3*β^4 := by gcongr
      _ = _ := by ring
  have hTangent (a b c e : I) :
      |coordDeriv i (fun x => christoffel g x a b c*covJet g f 2 x ![e,l]) y| ≤
        (DG*H2+G*(H3+6*G*H2))*β^4 := by
    have hh := abs_coordDeriv_mul_le (fun x => christoffel g x a b c) (fun x => covJet g f 2 x ![e,l])
      (((hΓSm a b c).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((hSC2 ![e,l]).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i
      hG hDG (hΓ a b c) (hDΓ i a b c) (hCov2 ![e,l]) (hDC2 i ![e,l])
    calc
      _ ≤ DG*(H2*β^2)+G*((H3+6*G*H2)*β^3) := hh
      _ = DG*H2*β^2+G*(H3+6*G*H2)*β^3 := by ring
      _ ≤ DG*H2*β^4+G*(H3+6*G*H2)*β^4 := by gcongr
      _ = _ := by ring
  have hT2 (s : I) : |coordDeriv i (T2 s) y| ≤ (DG*H2+G*(H3+6*G*H2))*β^4 := hTangent s j k s
  have hT3 (s : I) : |coordDeriv i (T3 s) y| ≤ (DG*H2+G*(H3+6*G*H2))*β^4 := by
    have hh := abs_coordDeriv_mul_le (fun x => christoffel g x s j l) (fun x => covJet g f 2 x ![k,s])
      (((hΓSm s j l).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((hSC2 ![k,s]).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i
      hG hDG (hΓ s j l) (hDΓ i s j l) (hCov2 ![k,s]) (hDC2 i ![k,s])
    calc
      _ ≤ DG*(H2*β^2)+G*((H3+6*G*H2)*β^3) := hh
      _ = DG*H2*β^2+G*(H3+6*G*H2)*β^3 := by ring
      _ ≤ DG*H2*β^4+G*(H3+6*G*H2)*β^4 := by gcongr
      _ = _ := by ring
  have hB : |coordDeriv i B y| ≤ 3*((DDG*B1+2*DG*B2+G*B3)*β^4) := by
    exact_mod_cast abs_coordDeriv_fintype_sum_le T1
      (fun s => ((hST1 s).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i _ hT1
  have hC : |coordDeriv i C y| ≤ 3*((DG*H2+G*(H3+6*G*H2))*β^4) := by
    exact_mod_cast abs_coordDeriv_fintype_sum_le T2
      (fun s => ((hST2 s).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i _ hT2
  have hD : |coordDeriv i D y| ≤ 3*((DG*H2+G*(H3+6*G*H2))*β^4) := by
    exact_mod_cast abs_coordDeriv_fintype_sum_le T3
      (fun s => ((hST3 s).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i _ hT3
  have hEq : coordDeriv j (coordDeriv k (coordDeriv l f)) =ᶠ[𝓝 y] (fun x => A x+B x+C x+D x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact coordinate_third_of_covJet hY g f hf hΓSm hx j k l
  have hDerivative : coordDeriv i (coordDeriv j (coordDeriv k (coordDeriv l f))) y =
      coordDeriv i A y+coordDeriv i B y+coordDeriv i C y+coordDeriv i D y := by
    change fderiv ℝ (coordDeriv j (coordDeriv k (coordDeriv l f))) y (axis i) = _
    rw [hEq.fderiv_eq]
    change coordDeriv i (fun x => A x+B x+C x+D x) y = _
    rw [coordDeriv_add_at _ _ ((((hAS.add hBS).add hCS).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      ((hDS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i,
      coordDeriv_add_at _ _ (((hAS.add hBS).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        ((hCS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i,
      coordDeriv_add_at _ _ ((hAS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        ((hBS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) i]
  rw [hDerivative]
  have hAbs : |coordDeriv i A y+coordDeriv i B y+coordDeriv i C y+coordDeriv i D y| ≤
      |coordDeriv i A y|+|coordDeriv i B y|+|coordDeriv i C y|+|coordDeriv i D y| :=
    (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  exact hAbs.trans ((add_le_add (add_le_add (add_le_add hDC3 hB) hC) hD).trans_eq
    (by dsimp only [fourthCoordinateJetBudget];ring))
end ShrinkingSpheres
