module

public import Proof.CalderonN.SupportedSphereMultiplierGerms

public import Proof.CalderonN.ActualRadialNumeratorGerms

import Proof.CalderonN.ActualPhysicalCoefficientGerm
import Mathlib.Tactic

/-! Uniform coefficient bounds for the genuine reciprocal weight, its
radius-normalized difference, and the affine density multiplier. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5900000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

@[expose] def actualReciprocalWeightDifferenceDatum
    (D : ∀ x ∈ Y,ActualGaussFiberData d x) (x : X dim) (hx : x ∈ Y) : SmoothData dim :=
  ⟨fun z => (d.radius x)⁻¹*((D x hx).reciprocal.1 z-1),
    contDiff_const.mul ((D x hx).reciprocal.2.sub contDiff_const)⟩

@[expose] def actualDensityLinearDatum (d : Data dim) (x : X dim) : SmoothData dim :=
  smoothLinearTraceDatum (firstDensityCenterLinear d x)

theorem uniform_actual_radialMultiplier_germs (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ D : ∀ x ∈ Y,ActualGaussFiberData d x,
        let L := supportedSphereMultiplierFamily (fun x (_ : x ∈ Y) => actualDensityLinearDatum d x)
        let H := supportedSphereMultiplierFamily (fun x hx => (D x hx).reciprocal)
        let H₁ := supportedSphereMultiplierFamily (actualReciprocalWeightDifferenceDatum D)
        ∃ (hL : SmoothSupportedTraceFiberRegular Y L) (hH : SmoothSupportedTraceFiberRegular Y H)
          (hH₁ : SmoothSupportedTraceFiberRegular Y H₁),∀ x ∈ Y,
          let β := beta d.γ d.radius x
          SupportedSphereMultiplierGerm (fun x (_ : x ∈ Y) => actualDensityLinearDatum d x) x β C ∧
          SupportedSphereMultiplierGerm (fun x hx => (D x hx).reciprocal) x β C ∧
          SupportedSphereMultiplierGerm (actualReciprocalWeightDifferenceDatum D) x β C := by
  have hn₂ : 2 ≤ dim := by omega
  obtain ⟨η₀,C₀,D₀,hη₀,hC₀,hD₀,hNum⟩ := uniform_actual_radialNumerator_germs hn₂
    hY hΩ hYc hSub 4 (by decide) hm K ρ c₀ M Cj hK hρ
  obtain ⟨η₁,hη₁,hCoeff⟩ := uniform_actual_physicalCoefficient_germ hn₂ hY hΩ hYc
    (by omega) K ρ c₀ M Cj hK hρ
  let Ball := closedBall (0:X dim) 1
  obtain ⟨Q,hQ,hInv⟩ := uniform_normalized_radial_inverse_germs (E:=X dim) Ball
    (isCompact_closedBall _ _) 4 C₀ D₀ hC₀ hD₀
  let A := D₀+Q
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let η := min η₀ (min η₁ (1/(2*(D₀+1))))
  refine ⟨η,A,lt_min hη₀ (lt_min hη₁ (by positivity)),hA,?_⟩
  intro floor hFloor ε hε hs d hd hFrame D
  dsimp only
  let mL (x : X dim) (_ : x ∈ Y) := actualDensityLinearDatum d x
  let mH (x : X dim) (hx : x ∈ Y) := (D x hx).reciprocal
  let mH₁ := actualReciprocalWeightDifferenceDatum D
  have hRep (x : X dim) (hx : x ∈ Y) :
      ∃ (V : Set (X dim)) (p q s : X dim × X dim → ℝ),
        IsOpen V ∧ x ∈ V ∧ V ⊆ Y ∧ ContDiff ℝ ∞ p ∧ ContDiff ℝ ∞ q ∧ ContDiff ℝ ∞ s ∧
        (∀ y ∈ V, ∀ hy : y ∈ Y,∀ z ∈ standardSphere dim,
          p (y,z) = (mL y hy).1 z ∧ q (y,z) = (mH y hy).1 z ∧ s (y,z) = (mH₁ y hy).1 z) ∧
        ∀ z ∈ Ball,
          let β := beta d.γ d.radius x
          LocalSmoothJetBudget (fun v : X dim × X dim => p (x+β⁻¹ • v.1,z+v.2)) 0 4 A ∧
          LocalSmoothJetBudget (fun v : X dim × X dim => q (x+β⁻¹ • v.1,z+v.2)) 0 4 A ∧
          LocalSmoothJetBudget (fun v : X dim × X dim => s (x+β⁻¹ • v.1,z+v.2)) 0 4 A := by
    obtain ⟨R,P,L,V,hR,hREq,hP,hL,hV,hBV,hReal,hJets⟩ := hNum floor hFloor ε hε
      (hs.trans (min_le_left _ _)) d hd hFrame x hx
    let β := beta d.γ d.radius x
    have hr := (hd.2.2.2.2.1.2 x hx).1
    have hrε := (le_mul_of_one_le_right hr.le (one_le_pow₀ (hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1))).trans
      (hd.2.2.2.2.2 x hx).2
    have hεD : ε*(2*(D₀+1)) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 2*(D₀+1))).mp
      (hs.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hSmall : |R x| * D₀ ≤ 1/2 := by
      rw [hREq.eq_of_nhds,abs_of_pos hr]
      have h := mul_le_mul_of_nonneg_right hrε hD₀
      nlinarith only [h,hεD,hε]
    obtain ⟨U,H,H₁,hU,hBU,hH,hH₁,hId,hJ⟩ := hInv R hR P hP x β hSmall (fun z hz =>
      ⟨(hJets z hz).1,(hJets z hz).2.1⟩)
    obtain ⟨U₀,U₁,hU₀,_,hx₀,hB₀,hTube⟩ := generalized_tube_lemma
      (isCompact_singleton (x:=x)) (isCompact_closedBall (0:X dim) 1)
      (hV.inter hU) (subset_inter hBV hBU)
    obtain ⟨J,hJsub,hJopen,hxJ⟩ := _root_.mem_nhds_iff.mp (hREq.and (hY.mem_nhds hx))
    refine ⟨U₀∩J,L,H,H₁,hU₀.inter hJopen,⟨hx₀ (mem_singleton _),hxJ⟩,
      fun _ hy => (hJsub hy.2).2,hL,hH,hH₁,?_,?_⟩
    · intro y hy hyY z hz
      have hZ := sphere_subset_closedBall hz
      have hyz : (y,z) ∈ V∩U := hTube (show (y,z) ∈ U₀ ×ˢ U₁ from ⟨hy.1,hB₀ hZ⟩)
      have hEq := hReal y z hyz.1 hyY hz
      have hp := hId (y,z) hyz.2
      have hRad : R y = d.radius y := (hJsub hy.2).1
      obtain ⟨N,a,J',_,hyN,_,ha,_,_,hN⟩ := hCoeff floor hFloor ε hε
        (hs.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd hFrame y hyY
      have hA : EqOn (fun z => a (y,z)) (D y hyY).coefficient (ball (0:X dim) 1) :=
        ((hN y hyN).mono ball_subset_closedBall).trans (D y hyY).coefficientEq.symm
      have hClosed : EqOn (fun z => a (y,z)) (D y hyY).coefficient Ball := by
        change EqOn _ _ (closedBall (0:X dim) 1)
        rw [← closure_ball _ (by norm_num : (1:ℝ) ≠ 0)]
        exact hA.closure (ha.continuous.comp (continuous_const.prodMk continuous_id))
          (D y hyY).smoothCoefficient.continuous
      have hWeight : (D y hyY).weight.1 z = 1+d.radius y*P (y,z) := by
        rw [(D y hyY).weight_eq_quadratic hz,← hClosed hZ,hN y hyN hZ]
        exact hEq.2
      have hRec : (D y hyY).reciprocal.1 z = ((D y hyY).weight.1 z)⁻¹ := (D y hyY).reciprocalEq hz
      have hInvEq : H (y,z) = (D y hyY).reciprocal.1 z := by
        rw [hp.1,hRad,hRec,hWeight]
      refine ⟨hEq.1,hInvEq,?_⟩
      have hR' := (hd.2.2.2.2.1.2 y hyY).1.ne'
      have hDen : 1+d.radius y*P (y,z) ≠ 0 := by
        rw [← hRad]
        exact hp.2.2.ne'
      change H₁ (y,z) = (d.radius y)⁻¹*((D y hyY).reciprocal.1 z-1)
      rw [hp.2.1,hInvEq,hRec,hWeight]
      have hDen' : 1+P (y,z)*d.radius y ≠ 0 := by simpa only [mul_comm] using hDen
      ring_nf
      field_simp [hR',hDen,hDen'] <;> ring
    · intro z hz
      exact ⟨((hJets z hz).2.2).enlarge (le_add_of_nonneg_right hQ),
        ((hJ z hz).1).enlarge (le_add_of_nonneg_left hD₀),
        ((hJ z hz).2).enlarge (le_add_of_nonneg_left hD₀)⟩
  have hL : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily mL) := by
    apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    obtain ⟨V,p,q,s,hV,hxV,hVY,hp,hq,hs,hEq,_⟩ := hRep x hx
    exact ⟨V,p,hV,hxV,hVY,hp.contDiffOn,fun y hy hyY z hz => (hEq y hy hyY z hz).1⟩
  have hH : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily mH) := by
    apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    obtain ⟨V,p,q,s,hV,hxV,hVY,hp,hq,hs,hEq,_⟩ := hRep x hx
    exact ⟨V,q,hV,hxV,hVY,hq.contDiffOn,fun y hy hyY z hz => (hEq y hy hyY z hz).2.1⟩
  have hH₁ : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily mH₁) := by
    apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    obtain ⟨V,p,q,s,hV,hxV,hVY,hp,hq,hs,hEq,_⟩ := hRep x hx
    exact ⟨V,s,hV,hxV,hVY,hs.contDiffOn,fun y hy hyY z hz => (hEq y hy hyY z hz).2.2⟩
  refine ⟨hL,hH,hH₁,?_⟩
  intro x hx
  let β := beta d.γ d.radius x
  obtain ⟨V,p,q,s,hV,hxV,hVY,hp,hq,hs,hEq,hJets⟩ := hRep x hx
  exact ⟨⟨V,p,hV,hxV,hVY,hp,fun y hy hyY z hz => (hEq y hy hyY z hz).1,fun z hz => (hJets z hz).1⟩,
    ⟨V,q,hV,hxV,hVY,hq,fun y hy hyY z hz => (hEq y hy hyY z hz).2.1,fun z hz => (hJets z hz).2.1⟩,
    ⟨V,s,hV,hxV,hVY,hs,fun y hy hyY z hz => (hEq y hy hyY z hz).2.2,fun z hz => (hJets z hz).2.2⟩⟩

theorem uniform_actual_radialMultiplier_bounds (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ)
    (B : Module.End ℝ (SmoothSphereTrace dim)) (hB : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f,B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f)) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ D : ∀ x ∈ Y,ActualGaussFiberData d x,
        let L := supportedSphereMultiplierFamily (fun x (_ : x ∈ Y) => actualDensityLinearDatum d x)
        let H := supportedSphereMultiplierFamily (fun x hx => (D x hx).reciprocal)
        let H₁ := supportedSphereMultiplierFamily (actualReciprocalWeightDifferenceDatum D)
        ∃ (hL : SmoothSupportedTraceFiberRegular Y L) (hH : SmoothSupportedTraceFiberRegular Y H)
          (hH₁ : SmoothSupportedTraceFiberRegular Y H₁),∀ x ∈ Y,
          let β := beta d.γ d.radius x
          SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C L hL ∧
          SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C H hH ∧
          SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C H₁ hH₁ := by
  obtain ⟨η,A,hη,hA,hG⟩ := uniform_actual_radialMultiplier_germs hn hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨C,hC,hLift⟩ := supportedSphereMultiplier_bounds_of_germ (Y:=Y) hn B hB hFin A hA
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hFloor ε hε hs d hd hf D
  obtain ⟨hL,hH,hH₁,h⟩ := hG floor hFloor ε hε hs d hd hf D
  refine ⟨hL,hH,hH₁,?_⟩
  intro x hx
  have hβ := zero_lt_one.trans_le (hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1)
  exact ⟨hLift hY x hx _ hβ _ hL (h x hx).1,hLift hY x hx _ hβ _ hH (h x hx).2.1,
    hLift hY x hx _ hβ _ hH₁ (h x hx).2.2⟩

end CalderonN
