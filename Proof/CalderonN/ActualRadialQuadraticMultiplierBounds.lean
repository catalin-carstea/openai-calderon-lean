module

public import Proof.CalderonN.SupportedSphereMultiplierGerms

public import Proof.CalderonN.ActualRadialMultiplierBounds
public import Proof.CalderonN.ActualRadialNumeratorGerms

import Proof.CalderonN.ActualPhysicalCoefficientGerm
import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! The normalized quadratic remainder of the actual reciprocal radial
weight has a nonsingular scalar germ. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

@[expose] def actualReciprocalWeightQuadraticDatum
    (D : ∀ x ∈ Y,ActualGaussFiberData d x) (x : X dim) (hx : x ∈ Y) : SmoothData dim :=
  ⟨fun z => ((d.radius x)^2)⁻¹*((D x hx).reciprocal.1 z-1+d.radius x*firstDensityCenterLinear d x z),
    contDiff_const.mul (((D x hx).reciprocal.2.sub contDiff_const).add
      (contDiff_const.mul (firstDensityCenterLinear d x).contDiff))⟩

theorem reciprocal_quadratic_eq (r p l q : ℝ) (hr : r ≠ 0) (hW : 1+r*p ≠ 0)
    (hp : p = l+r*q) :
    (r^2)⁻¹*((1+r*p)⁻¹-1+r*l) = (l*p-q)*(1+r*p)⁻¹ := by
  field_simp [hr,hW]
  linear_combination -r*hp

theorem uniform_actual_radialQuadraticMultiplier_germs (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ D : ∀ x ∈ Y,ActualGaussFiberData d x,
        let H₂ := supportedSphereMultiplierFamily (actualReciprocalWeightQuadraticDatum D)
        ∃ hH₂ : SmoothSupportedTraceFiberRegular Y H₂,∀ x ∈ Y,
          SupportedSphereMultiplierGerm (actualReciprocalWeightQuadraticDatum D) x (beta d.γ d.radius x) C := by
  have hn₂ : 2 ≤ dim := by omega
  obtain ⟨η₀,C₀,D₀,hη₀,hC₀,hD₀,hNum⟩ := uniform_actual_radialNumerator_factorization_germs hn₂
    hY hΩ hYc hSub 4 (by decide) hm K ρ c₀ M Cj hK hρ
  obtain ⟨η₁,hη₁,hCoeff⟩ := uniform_actual_physicalCoefficient_germ hn₂ hY hΩ hYc
    (by omega) K ρ c₀ M Cj hK hρ
  let Ball := closedBall (0:X dim) 1
  obtain ⟨Q,hQ,hInv⟩ := uniform_normalized_radial_inverse_germs (E:=X dim) Ball
    (isCompact_closedBall _ _) 4 C₀ D₀ hC₀ hD₀
  let S := (2:ℝ)^4*‖ContinuousLinearMap.mul ℝ ℝ‖
  let A := S*(S*D₀*D₀+D₀)*Q
  have hA : 0 ≤ A := by dsimp only [A,S]; positivity
  let η := min η₀ (min η₁ (1/(2*(D₀+1))))
  refine ⟨η,A,lt_min hη₀ (lt_min hη₁ (by positivity)),hA,?_⟩
  intro floor hFloor ε hε hs d hd hFrame D
  dsimp only
  let m₂ := actualReciprocalWeightQuadraticDatum D
  have hRep (x : X dim) (hx : x ∈ Y) :
      ∃ (V : Set (X dim)) (q : X dim × X dim → ℝ),
        IsOpen V ∧ x ∈ V ∧ V ⊆ Y ∧ ContDiff ℝ ∞ q ∧
        (∀ y ∈ V,∀ hy : y ∈ Y,∀ z ∈ standardSphere dim,q (y,z) = (m₂ y hy).1 z) ∧
        ∀ z ∈ Ball, let β := beta d.γ d.radius x
          LocalSmoothJetBudget (fun v : X dim × X dim => q (x+β⁻¹ • v.1,z+v.2)) 0 4 A := by
    obtain ⟨R,P,L,E,V,hR,hREq,hP,hL,hE,hV,hBV,hReal,hJets⟩ := hNum floor hFloor ε hε
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
    obtain ⟨U,H,_,hU,hBU,hH,_,hId,hJ⟩ := hInv R hR P hP x β hSmall (fun z hz =>
      ⟨(hJets z hz).1,(hJets z hz).2.1⟩)
    let q (w : X dim × X dim) := (L w*P w-E w)*H w
    have hq : ContDiff ℝ ∞ q := ((hL.mul hP).sub hE).mul hH
    obtain ⟨U₀,U₁,hU₀,_,hx₀,hB₀,hTube⟩ := generalized_tube_lemma
      (isCompact_singleton (x:=x)) (isCompact_closedBall (0:X dim) 1)
      (hV.inter hU) (subset_inter hBV hBU)
    obtain ⟨J,hJsub,hJopen,hxJ⟩ := _root_.mem_nhds_iff.mp (hREq.and (hY.mem_nhds hx))
    refine ⟨U₀∩J,q,hU₀.inter hJopen,⟨hx₀ (mem_singleton _),hxJ⟩,
      fun _ hy => (hJsub hy.2).2,hq,?_,?_⟩
    · intro y hy hyY z hz
      have hZ := sphere_subset_closedBall hz
      have hyz : (y,z) ∈ V∩U := hTube (show (y,z) ∈ U₀ ×ˢ U₁ from ⟨hy.1,hB₀ hZ⟩)
      have hEq := hReal y z hyz.1 hyY hz
      have hp := hId (y,z) hyz.2
      have hRad : R y = d.radius y := (hJsub hy.2).1
      obtain ⟨W,a,J',_,hyW,_,ha,_,_,hWa⟩ := hCoeff floor hFloor ε hε
        (hs.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd hFrame y hyY
      have hA : EqOn (fun z => a (y,z)) (D y hyY).coefficient (ball (0:X dim) 1) :=
        ((hWa y hyW).mono ball_subset_closedBall).trans (D y hyY).coefficientEq.symm
      have hClosed : EqOn (fun z => a (y,z)) (D y hyY).coefficient Ball := by
        change EqOn _ _ (closedBall (0:X dim) 1)
        rw [← closure_ball _ (by norm_num : (1:ℝ) ≠ 0)]
        exact hA.closure (ha.continuous.comp (continuous_const.prodMk continuous_id))
          (D y hyY).smoothCoefficient.continuous
      have hWeight : (D y hyY).weight.1 z = 1+d.radius y*P (y,z) := by
        rw [(D y hyY).weight_eq_quadratic hz,← hClosed hZ,hWa y hyW hZ]
        exact hEq.2.1
      have hRec : (D y hyY).reciprocal.1 z = ((D y hyY).weight.1 z)⁻¹ := (D y hyY).reciprocalEq hz
      have hH' : H (y,z) = (1+d.radius y*P (y,z))⁻¹ := by rw [hp.1,hRad]
      have hRad₀ := (hd.2.2.2.2.1.2 y hyY).1.ne'
      have hDen : 1+d.radius y*P (y,z) ≠ 0 := by rw [← hRad]; exact hp.2.2.ne'
      change (L (y,z)*P (y,z)-E (y,z))*H (y,z) =
        ((d.radius y)^2)⁻¹*((D y hyY).reciprocal.1 z-1+d.radius y*firstDensityCenterLinear d y z)
      rw [hH',hRec,hWeight,← hEq.1]
      exact (reciprocal_quadratic_eq _ _ _ _ hRad₀ hDen hEq.2.2).symm
    · intro z hz
      let f (v : X dim × X dim) := (x+β⁻¹ • v.1,z+v.2)
      have hEJ : LocalSmoothJetBudget (- (E ∘ f)) 0 4 D₀ := by
        refine ⟨(hJets z hz).2.2.2.smooth.neg,fun n hn => ?_⟩
        rw [iteratedFDeriv_neg,Pi.neg_apply,norm_neg]
        exact (hJets z hz).2.2.2.bound n hn
      exact ((((hJets z hz).2.2.1.real_mul (hJets z hz).2.1).add hEJ).real_mul (hJ z hz).1)
  have hH₂ : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily m₂) := by
    apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    obtain ⟨V,q,hV,hxV,hVY,hq,hEq,_⟩ := hRep x hx
    exact ⟨V,q,hV,hxV,hVY,hq.contDiffOn,hEq⟩
  refine ⟨hH₂,?_⟩
  intro x hx
  obtain ⟨V,q,hV,hxV,hVY,hq,hEq,hJets⟩ := hRep x hx
  exact ⟨V,q,hV,hxV,hVY,hq,hEq,hJets⟩

theorem uniform_actual_radialQuadraticMultiplier_bounds (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ)
    (B : Module.End ℝ (SmoothSphereTrace dim)) (hB : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f,B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f)) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ D : ∀ x ∈ Y,ActualGaussFiberData d x,
        let H₂ := supportedSphereMultiplierFamily (actualReciprocalWeightQuadraticDatum D)
        ∃ hH₂ : SmoothSupportedTraceFiberRegular Y H₂,∀ x ∈ Y,
          SmoothSupportedTraceCoefficientBounds hn B hY x (beta d.γ d.radius x) 0 C H₂ hH₂ := by
  obtain ⟨η,A,hη,hA,hG⟩ := uniform_actual_radialQuadraticMultiplier_germs hn hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨C,hC,hLift⟩ := supportedSphereMultiplier_bounds_of_germ (Y:=Y) hn B hB hFin A hA
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hFloor ε hε hs d hd hf D
  obtain ⟨hH₂,h⟩ := hG floor hFloor ε hε hs d hd hf D
  refine ⟨hH₂,?_⟩
  intro x hx
  exact hLift hY x hx _ (zero_lt_one.trans_le (hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1)) _ hH₂ (h x hx)

end CalderonN
