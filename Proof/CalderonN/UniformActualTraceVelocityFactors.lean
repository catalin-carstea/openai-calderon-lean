module

public import Proof.CalderonN.ActualTracePrimitivePairs
public import Proof.CalderonN.ActualTraceVelocityFactorBounds
public import Proof.CalderonN.ActualTraceProfileScalarJets
public import Proof.CalderonN.ActualGaussConormalHigherBaseBounds

import Proof.CalderonN.ActualCenterCorrectionMultiplierBounds
import Proof.CalderonN.ActualTranslationMultiplierBounds
import Mathlib.Tactic

/-! Instantiate the angular basis and ordinary base jets on the same
actual Gauss family. The normalized velocity is regular at this scale. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem uniform_actualTraceVelocityFactors (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) :
    ∃ η I₀ J C : ℝ,0 < η ∧ 1 ≤ I₀ ∧ 1 ≤ J ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η →
      ∀ d,Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (F : ∀ x ∈ Y,ActualGaussFiberData d x)
        (hR : SmoothSupportedTraceFiberRegular Y (actualGaussScaledConormalFamily F)),
        (∀ x (hx : x ∈ Y),∀ z ∈ ball (0:X dim) 1,((F x hx).coefficient z).IsSymm) →
        ∃ V : ActualTraceVelocityFactors hn Y,(∀ x (hx : x ∈ Y),V.Matches (F x hx)) ∧
          ∀ x (hx : x ∈ Y),∃ H : ActualTraceAngularBasis hn (smoothTraceFlatDegree hA hEll S)
            (((d.radius x)^2)⁻¹ • (F x hx).conormalRemainder) J I₀,
            V.Bounds H.atoms hY x (beta d.γ d.radius x) 2 C := by
  have hKp := zero_lt_one.trans_le hK
  obtain ⟨η₀,A₀,hη₀,hA₀,hRad⟩ := uniform_actual_radialMultiplier_germs hn hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨η₁,A₁,hη₁,hA₁,hQuad⟩ := uniform_actual_radialQuadraticMultiplier_germs hn hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨η₂,A₂,hη₂,hA₂,hCenter⟩ := uniform_actual_centerCorrectionMultiplier_germs hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨A₃,hA₃,hTrans⟩ := uniform_actual_translationMultiplier_germs hY hΩ hSub (by omega : 4 ≤ m) K ρ c₀ M Cj hKp
  obtain ⟨η₃,D,hη₃,hD,hRC⟩ := uniform_actualGauss_scaledConormal_baseJet_angularBounds hn hY hΩ hYc hSub 2
    (by decide) (by omega : 2+5 ≤ m) K ρ c₀ M Cj hK hρ
  obtain ⟨P,hP,hProf⟩ := uniform_actualTraceProfile_scalar_jets hY hΩ hSub (by omega : 3+1 ≤ m)
    (by decide : 3 ≤ 8) K ρ c₀ M Cj hKp
  let U := 1+A₀+A₁+A₂+A₃
  let J := 6*U
  have hU : 1 ≤ U := by dsimp only [U]; linarith only [hA₀,hA₁,hA₂,hA₃]
  have hJ : 1 ≤ J := by dsimp only [J]; linarith only [hU]
  obtain ⟨η₄,I₀,hη₄,hI₀,hBasis⟩ := uniform_actualTraceAngularBasis hn hY hΩ (by omega : 5 ≤ m)
    K ρ c₀ M Cj hK hρ J (zero_le_one.trans hJ) hA hEll S
  let η := min 1 (min η₀ (min η₁ (min η₂ (min η₃ η₄))))
  let W := smoothTraceMultiplierJetConstant dim (2*U)
  let C₁ := I₀+W+I₀*P+D
  let C := 2*C₁
  have hW := smoothTraceMultiplierJetConstant_nonneg (dim:=dim) (2*U) (by positivity)
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  refine ⟨η,I₀,J,C,lt_min zero_lt_one (lt_min hη₀ (lt_min hη₁ (lt_min hη₂ (lt_min hη₃ hη₄)))),
    hI₀,hJ,by dsimp only [C]; positivity,?_⟩
  intro floor hFloor ε hε hs d hd hFrame F hR hSym
  have hs₀ := hs.trans (min_le_right _ _)
  have hs₁ := hs₀.trans (min_le_right _ _)
  have hs₂ := hs₁.trans (min_le_right _ _)
  have hs₃ := hs₂.trans (min_le_right _ _)
  obtain ⟨hL,hH,hH₁,hRh⟩ := hRad floor hFloor ε hε (hs₀.trans (min_le_left _ _)) d hd hFrame F
  obtain ⟨hH₂,hQh⟩ := hQuad floor hFloor ε hε (hs₁.trans (min_le_left _ _)) d hd hFrame F
  choose hN hV hCh using hCenter floor hFloor ε hε (hs₂.trans (min_le_left _ _)) d hd hFrame F
  choose hM hMh using hTrans floor hFloor ε d hd hFrame
  let r := d.radius
  have hr := hd.2.2.2.2.1.1
  have hdr (i : I dim) : ContDiffOn ℝ ∞ (coordDeriv i r) Y :=
    (hr.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
  let L (x : X dim) (_ : x ∈ Y) := actualDensityLinearDatum d x
  let H (x : X dim) (hx : x ∈ Y) := (F x hx).reciprocal
  let H₁ := actualReciprocalWeightDifferenceDatum F
  let H₂ := actualReciprocalWeightQuadraticDatum F
  let N (i : I dim) (x : X dim) (hx : x ∈ Y) := smoothVelocityNormal ((F x hx).centerCorrection i)
  let V (i a b : I dim) (x : X dim) (hx : x ∈ Y) := smoothVelocityAngular ((F x hx).centerCorrection i) a b
  let U₀ (i : I dim) (x : X dim) (_ : x ∈ Y) := actualTranslationMultiplierDatum d i x
  let R : RegularTraceFiberFamily Y := ⟨actualGaussScaledConormalFamily F,hR⟩
  have hRs (x : X dim) (hx : x ∈ Y) : SmoothTraceAdjoint hn (R.1 x) (R.1 x) :=
    actualGaussScaledConormalFamily_symmetric hn F hx (hSym x hx)
  let F₀ : ActualTraceVelocityFactors hn Y := {
    degree := PairedTraceFiberFamily.degree hA hEll S
    rotations := PairedTraceFiberFamily.rotation
    radius := PairedTraceFiberFamily.scalar hY r hr
    half := PairedTraceFiberFamily.scalar hY (fun _ => 1/2) contDiffOn_const
    densityLinear := PairedTraceFiberFamily.multiplier L hL
    reciprocal := PairedTraceFiberFamily.multiplier H hH
    reciprocalLinear := PairedTraceFiberFamily.multiplier H₁ hH₁
    reciprocalQuadratic := PairedTraceFiberFamily.multiplier H₂ hH₂
    conormalQuadratic := PairedTraceFiberFamily.symmetric R hRs
    translation := fun i => (PairedTraceFiberFamily.multiplier (U₀ i) (hM i)).add
      (PairedTraceFiberFamily.scalar hY (coordDeriv i r) (hdr i))
    centerNormal := fun i => PairedTraceFiberFamily.multiplier (N i) (hN i)
    centerAngular := fun i a b => PairedTraceFiberFamily.multiplier (V i a b) (hV i a b) }
  refine ⟨F₀,?_,?_⟩
  · intro x hx
    have hB := smoothTraceFlatDegree_eq hn (F x hx).smoothCoefficient hA
      (F x hx).ellipticCoefficient hEll (F x hx).solve S
    refine ⟨hB.symm,fun _ _ => rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals simp only [F₀,PairedTraceFiberFamily.multiplier,PairedTraceFiberFamily.symmetric,
      supportedSphereMultiplierFamily,dite_eq_left hx,PairedTraceFiberFamily.add,RegularTraceFiberFamily.add,
      PairedTraceFiberFamily.scalar,RegularTraceFiberFamily.scalar,R,actualGaussScaledConormalFamily]
    · rfl
    · rfl
    · ext u : 1
      apply Subtype.ext
      funext z
      simp only [H₁,actualReciprocalWeightDifferenceDatum,smoothSphereTraceMul_apply,LinearMap.sub_apply,
        LinearMap.smul_apply,Submodule.coe_smul,Submodule.coe_sub,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,
        Module.End.one_apply]
      ring
    · ext u : 1
      apply Subtype.ext
      funext z
      simp only [H₂,actualReciprocalWeightQuadraticDatum,ActualGaussFiberData.affineDensityMul,
        smoothSphereTraceMul_apply,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
        Submodule.coe_add,Submodule.coe_smul,Submodule.coe_sub,Pi.add_apply,Pi.smul_apply,Pi.sub_apply,
        smul_eq_mul,Module.End.one_apply]
      ring
    · intro i
      rfl
    · intro i
      rfl
    · intro i a b
      rfl
  · intro x hx
    let β := beta d.γ r x
    have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
    have hβ' := zero_lt_one.trans_le hβ
    have hr₀ := (hd.2.2.2.2.1.2 x hx).1
    have hSmall : r x*β^2 ≤ 1 := ((hd.2.2.2.2.2 x hx).2).trans (hs.trans (min_le_left _ _))
    have hrβ : r x*β ≤ 1 := by
      have hh : β ≤ β^2 := by nlinarith only [mul_le_mul_of_nonneg_left hβ hβ'.le]
      exact (mul_le_mul_of_nonneg_left hh hr₀.le).trans hSmall
    have hr' : r x ≤ 1 := (le_mul_of_one_le_right hr₀.le hβ).trans hrβ
    obtain ⟨H⟩ := hBasis floor hFloor ε hε (hs₃.trans (min_le_right _ _)) d hd x hx (F x hx)
    refine ⟨H,?_⟩
    have hI₀C : I₀ ≤ C₁ := by dsimp only [C₁]; linarith only [hW,mul_nonneg (zero_le_one.trans hI₀) (zero_le_one.trans hP),hD]
    have hC₁C : C₁ ≤ C := by dsimp only [C]; linarith only [hC₁]
    have hPC : I₀*P ≤ C₁ := by dsimp only [C₁]; linarith only [hW,zero_le_one.trans hI₀,hD]
    have hWC : I₀+W ≤ C₁ := by dsimp only [C₁]; linarith only [mul_nonneg (zero_le_one.trans hI₀) (zero_le_one.trans hP),hD]
    have hMult {f : ∀ x ∈ Y,SmoothData dim}
        (hf : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily f))
        {s : ℝ} (hG : SupportedSphereMultiplierGerm f x β s) (hSU : s ≤ U) :
        PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 C₁ (PairedTraceFiberFamily.multiplier f hf) := by
      have hb := PairedTraceFiberFamily.multiplier_bounds H hY x hx β hβ' (zero_le_one.trans hU) le_rfl f hf
        (hG.enlarge hSU)
      exact hb.enlarge hβ'.le hWC
    have hProf' := hProf floor hFloor ε d hd x hx
    have hRadius : PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (I₀*P) F₀.radius := by
      refine PairedTraceFiberFamilyBounds.ofScalar hx hβ'.le hI₀ H.identity r hr (zero_le_one.trans hP) ?_
      intro n hn
      exact (hProf'.1 n (by omega)).trans (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (zero_le_one.trans hP) hr') (pow_nonneg hβ'.le _))
    have hDr (i : I dim) : PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (I₀*P)
        (PairedTraceFiberFamily.scalar hY (coordDeriv i r) (hdr i)) := by
      refine PairedTraceFiberFamilyBounds.ofScalar hx hβ'.le hI₀ H.identity _ _ (zero_le_one.trans hP) ?_
      intro n hn
      refine (hProf'.2.1 i n (by omega)).trans ?_
      rw [pow_succ,show P*r x*(β^n*β) = P*(r x*β)*β^n by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (zero_le_one.trans hP) hrβ) (pow_nonneg hβ'.le _)
    have hHalf : PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (I₀*1) F₀.half := by
      refine PairedTraceFiberFamilyBounds.ofScalar hx hβ'.le hI₀ H.identity _ _ zero_le_one ?_
      intro n hn
      have h := (LocalSmoothJetBudget.const (x:=x) (N:=2) (1/2:ℝ)).bound n hn
      refine h.trans ?_
      rw [Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2),one_mul]
      exact (by norm_num : (1/2:ℝ) ≤ 1).trans (one_le_pow₀ hβ)
    have hCJ : PairedTraceFiberFamilyBounds H.atoms hY x β 2 1 (I₀+D) F₀.conormalQuadratic := by
      have h := hRC floor hFloor ε hε (hs₃.trans (min_le_left _ _)) d hd hFrame F hR hSym x hx
      have hSymb : SmoothTraceSymbolBounds H.atoms 1 I₀ (R.1 x) := by
        simpa only [R,actualGaussScaledConormalFamily,dite_eq_left hx] using H.conormal
      exact ⟨(show SmoothSupportedFiberJetBound hn hY x β 2 1 D R from h).enlarge hβ'.le
        (le_add_of_nonneg_left (zero_le_one.trans hI₀)),hSymb.enlarge (le_add_of_nonneg_right hD),
        hSymb.enlarge (le_add_of_nonneg_right hD)⟩
    have hRC' : I₀+D ≤ C := by
      apply le_trans _ hC₁C
      dsimp only [C₁]
      linarith only [hW,mul_nonneg (zero_le_one.trans hI₀) (zero_le_one.trans hP)]
    have hU₀ : A₀ ≤ U := by dsimp only [U]; linarith only [hA₁,hA₂,hA₃]
    have hU₁ : A₁ ≤ U := by dsimp only [U]; linarith only [hA₀,hA₂,hA₃]
    have hU₂ : A₂ ≤ U := by dsimp only [U]; linarith only [hA₀,hA₁,hA₃]
    have hU₃ : A₃ ≤ U := by dsimp only [U]; linarith only [hA₀,hA₁,hA₂]
    refine ⟨(PairedTraceFiberFamily.degree_bounds hA hEll S H hY x hx β hβ'.le 2).enlarge hβ'.le (hI₀C.trans hC₁C),
      fun i j => (PairedTraceFiberFamily.rotation_bounds H hY x hx β hβ'.le 2 i j).enlarge hβ'.le (hI₀C.trans hC₁C),
      hRadius.enlarge hβ'.le (hPC.trans hC₁C),hHalf.enlarge hβ'.le (by simpa only [mul_one] using hI₀C.trans hC₁C),
      (hMult hL (hRh x hx).1 hU₀).enlarge hβ'.le hC₁C,(hMult hH (hRh x hx).2.1 hU₀).enlarge hβ'.le hC₁C,
      (hMult hH₁ (hRh x hx).2.2 hU₀).enlarge hβ'.le hC₁C,(hMult hH₂ (hQh x hx) hU₁).enlarge hβ'.le hC₁C,
      hCJ.enlarge hβ'.le hRC',?_,?_,?_⟩
    · intro i
      have h := (hMult (hM i) (hMh i x hx) hU₃).add hx ((hDr i).enlarge hβ'.le hPC)
      exact h.enlarge hβ'.le (show C₁+C₁ ≤ C from by dsimp only [C]; linarith)
    · intro i
      exact (hMult (hN i) (hCh i x hx).1 hU₂).enlarge hβ'.le hC₁C
    · intro i a b
      exact (hMult (hV i a b) ((hCh i x hx).2 a b) hU₂).enlarge hβ'.le hC₁C

end CalderonN
