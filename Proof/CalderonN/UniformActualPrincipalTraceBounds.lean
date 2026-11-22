module

public import Proof.CalderonN.UniformActualPrincipalScalarBounds
public import Proof.CalderonN.CoordinatePrincipalTraceFactorBounds
public import Proof.CalderonN.CoordinateTraceFirstOrderBounds
public import Proof.CalderonN.UniformActualTraceVelocityFactors

import Mathlib.Tactic

/-! The pointwise bounds for the actual principal perturbation,
model, and adjoints use one angular algebra at each base point. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5700000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem uniform_actualCoordinatePrincipalTrace_bounds (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) :
    ∃ η C D : ℝ,0 < η ∧ 0 ≤ C ∧ 0 ≤ D ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (hg : Elliptic Y K d.γ) (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
        (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
        (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
        (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y) (hg₂ : SmoothMetric Y d.g₂)
        (F : ∀ x ∈ Y,ActualGaussFiberData d x)
        (hR : SmoothSupportedTraceFiberRegular Y (actualGaussScaledConormalFamily F)),
        (∀ x (hx : x ∈ Y),∀ z ∈ ball (0:X dim) 1,((F x hx).coefficient z).IsSymm) →
        ∃ V : ActualTraceVelocityFactors hn Y,(∀ x (hx : x ∈ Y),V.Matches (F x hx)) ∧
          let P := actualCoordinatePrincipalTraceFactors hY hg (zero_lt_one.trans_le hK) he hr hr₀ hlog hQ hg₂ hA hEll S V
          let U := P.divergence hY
          let T := CoordinateTraceFirstOrder.ofPaired (P.model.first hY) (P.model.zero hY)
          let Td := CoordinateTraceFirstOrder.ofPairedAdjoint hY U.density (P.model.first hY) (P.model.zero hY)
          let Z := (P.model.correction hY).forward
          ∀ x ∈ Y,∃ A : SmoothTraceSymbolAtoms hn,
            let β := beta d.γ d.radius x
            CoordinateTraceDivergenceBounds A hY x β (D*ε) C U ∧
              CoordinateTraceFirstOrderBounds A hY x β C T ∧
              CoordinateTraceFirstOrderBounds A hY x β C Td ∧
              CoordinateTraceFirstOrderBounds A hY x β C (U.skew hY) ∧
              CoordinateTraceFirstOrderBounds A hY x β C (U.skew hY).neg ∧
              SmoothTraceAngularBound hn 1 (C*β) (Z.1 x) ∧
              ∀ i,SmoothTraceAngularBound hn 1 (C*β^2) ((Z.derivative hY (axis i)).1 x) := by
  have hKp := zero_lt_one.trans_le hK
  obtain ⟨η,I₀,J,V₀,hη,hI₀,hJ,hV₀,hVel⟩ := uniform_actualTraceVelocityFactors hn hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ hA hEll S
  obtain ⟨V₁,hV₁,hVelBound⟩ := ActualTraceVelocityFactors.bounds_of_factors (Y:=Y) (hn:=hn) 2 V₀ hV₀
  obtain ⟨M₀,hM₀,hModel⟩ := uniform_actualCoordinateTraceModel_bounds hn hY hΩ hSub (by omega : 4 ≤ m)
    K ρ c₀ M Cj hKp I₀ J hI₀ hJ hA hEll S
  obtain ⟨S₀,hS₀,hScalar⟩ := uniform_actualCoordinatePrincipal_scalar_bounds hn hY hΩ hSub (by omega : 4 ≤ m)
    K ρ c₀ M Cj hKp I₀ J hI₀ hA hEll S
  let P₀ := V₁+M₀+S₀
  have hP₀ : 0 ≤ P₀ := by dsimp only [P₀]; positivity
  obtain ⟨D,hD,hPrincipal⟩ := CoordinatePrincipalTraceFactors.bounds_of_primitives (Y:=Y) (hn:=hn) P₀ hP₀
  let C₀ := P₀+D
  have hC₀ : 0 ≤ C₀ := add_nonneg hP₀ hD
  obtain ⟨C₁,hC₁,hPair⟩ := coordinateTrace_pairedFirstOrder_bounds (Y:=Y) (hn:=hn) C₀ hC₀
  let C := C₀+2*C₁
  refine ⟨min 1 η,C,D,lt_min zero_lt_one hη,by dsimp only [C]; positivity,hD,?_⟩
  intro floor hFloor ε hε hs d hd hFrame hg he hr hr₀ hlog hQ hg₂ F hR hSym
  have hε₁ := hs.trans (min_le_left _ _)
  obtain ⟨V,hV,hBasis⟩ := hVel floor hFloor ε hε (hs.trans (min_le_right _ _)) d hd hFrame F hR hSym
  refine ⟨V,hV,?_⟩
  dsimp only
  intro x hx
  let β := beta d.γ d.radius x
  have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
  have hβ₀ := zero_le_one.trans hβ
  have hinv := inv_nonneg.mpr hβ₀
  let P := actualCoordinatePrincipalTraceFactors hY hg hKp he hr hr₀ hlog hQ hg₂ hA hEll S V
  let U := P.divergence hY
  obtain ⟨H,hV'⟩ := hBasis x hx
  let B := H.atoms
  obtain ⟨_,hVelN,hVelL⟩ := hVelBound B hY x hx β hβ₀ I₀ H.identity V hV'
  have hR := hModel floor hFloor ε d hd hFrame hg he hlog x hx _ H
  have hVle : V₁ ≤ P₀ := by dsimp only [P₀]; linarith only [hM₀,hS₀]
  have hMle : M₀ ≤ P₀ := by dsimp only [P₀]; linarith only [hV₁,hS₀]
  have hSle : S₀ ≤ P₀ := by dsimp only [P₀]; linarith only [hV₁,hM₀]
  have hP_le : P₀ ≤ C₀ := le_add_of_nonneg_right hD
  have hD_le : D ≤ C₀ := le_add_of_nonneg_left hP₀
  have hC₀le : C₀ ≤ C := by dsimp only [C]; linarith only [hC₁]
  have hC₁le : C₁ ≤ C := by dsimp only [C]; linarith only [hC₀,hC₁]
  have hC₂le : C₁+C₁ ≤ C := by dsimp only [C]; linarith only [hC₀]
  obtain ⟨hA,hA',hDiff,hPr,hDensity⟩ := hScalar floor hFloor ε hε hε₁ d hd hg he hr hr₀ hlog hQ hg₂ V x hx _ H
  have hSε := mul_le_mul_of_nonneg_right hSle hε
  have hSεβ := mul_le_mul_of_nonneg_right hSε hinv
  have hSεβ₂ := mul_le_mul_of_nonneg_right hSε (sq_nonneg β⁻¹)
  have hU := hPrincipal B hY x hx β ε hβ hε hε₁ I₀ H.identity P
    ⟨fun i j => (hA i j).enlarge hβ₀ hSεβ₂,fun i j k => (hA' i j k).enlarge hβ₀ hSεβ,
      fun i j => (hDiff i j).enlarge hβ₀ hSε,hPr.enlarge hβ₀ hSεβ₂,
      fun i => (hDensity i).enlarge hβ₀ hSle,hR.enlarge hβ₀ hMle,
      fun i => (hVelN i).enlarge hβ₀ hVle,fun i => (hVelL i).enlarge hβ₀ hVle⟩
  have hDense (i : I dim) : SmoothSupportedFiberJetBound hn hY x β 1 0 C₀ (U.density i) :=
    ((hDensity i).jets.restrict (by decide)).enlarge hβ₀ (hSle.trans hP_le)
  obtain ⟨hT,hTd⟩ := hPair B hY x hx β hβ (P.model.first hY) (P.model.zero hY) U.density
    (fun i => (hR.first i).enlarge hβ₀ (hMle.trans hP_le))
    (hR.zero.enlarge hβ₀ (mul_le_mul_of_nonneg_right (hMle.trans hP_le) hβ₀)) hDense
  have hDε : D*ε ≤ C₀ := (mul_le_of_le_one_right hD hε₁).trans hD_le
  have hDεs : D*ε*β⁻¹ ≤ C₀ :=
    (mul_le_of_le_one_right (mul_nonneg hD hε) (inv_le_one_of_one_le₀ hβ)).trans hDε
  obtain ⟨hS,hSd⟩ := hPair B hY x hx β hβ U.first U.zero U.density
    (fun i => (hU.first i).enlarge hβ₀ hDεs)
    (hU.zero.enlarge hβ₀ (hDε.trans (le_mul_of_one_le_right hC₀ hβ))) hDense
  have hSkew : CoordinateTraceFirstOrderBounds B hY x β (C₁+C₁) (U.skew hY) := by
    rw [CoordinateTraceFirstOrder.skew_eq_paired_sub U hY]
    exact hSd.sub hS hx
  have hZ := hR.correction.enlarge hβ₀ (mul_le_mul_of_nonneg_right ((hMle.trans hP_le).trans hC₀le) hβ₀)
  refine ⟨B,⟨fun i => (hU.density i).enlarge (hD_le.trans hC₀le),hU.second,hU.secondDerivative,hU.first,hU.zero⟩,
    hT.enlarge hβ₀ hC₁le,hTd.enlarge hβ₀ hC₁le,hSkew.enlarge hβ₀ hC₂le,(hSkew.neg hx).enlarge hβ₀ hC₂le,hZ.symbol.angular,?_⟩
  intro i
  change SmoothTraceAngularBound hn 1 (C*β^2) (((P.model.correction hY).forward.derivative hY (axis i)).1 x)
  simpa only [pow_two,mul_assoc,P,actualCoordinatePrincipalTraceFactors] using (hZ.jets.atAxis le_rfl i)

end CalderonN
