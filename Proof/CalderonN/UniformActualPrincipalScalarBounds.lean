module

public import Proof.CalderonN.ActualCoordinatePrincipalTrace
public import Proof.CalderonN.ActualTraceDensityScalarJets
public import Proof.CalderonN.UniformActualTraceModelBounds

import Proof.CalderonN.CoordinateJets
import Mathlib.Tactic

/-! Put the actual scalar jets in the coefficient family interface. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem uniform_actualCoordinatePrincipal_scalar_bounds (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 0 < K)
    (I₀ J : ℝ) (hI₀ : 1 ≤ I₀)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d : Data dim,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ (hg : Elliptic Y K d.γ) (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
        (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
        (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
        (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y)
        (hg₂ : SmoothMetric Y d.g₂) (V : ActualTraceVelocityFactors hn Y),
      ∀ x ∈ Y,∀ (R : Module.End ℝ (SmoothSphereTrace dim))
        (H : ActualTraceAngularBasis hn (smoothTraceFlatDegree hA hEll S) R J I₀),
        let F := actualCoordinatePrincipalTraceFactors hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V
        let β := beta d.γ d.radius x
        (∀ i j,PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (C*ε*(β⁻¹)^2) (F.principal i j)) ∧
        (∀ i j k,PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (C*ε*β⁻¹) (F.principalDerivative i j k)) ∧
        (∀ i j,PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (C*ε) (F.smallDifference i j)) ∧
        PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (C*ε*(β⁻¹)^2) F.radius ∧
        ∀ i,PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 C (F.density i) := by
  obtain ⟨G,hG,hGeom⟩ := uniform_actualPrincipalTrace_scalar_jets hY hΩ hSub hm K ρ c₀ M Cj hK
  obtain ⟨P,hP,hProf⟩ := uniform_actualTraceProfile_scalar_jets hY hΩ hSub hm (by decide : 3 ≤ 8) K ρ c₀ M Cj hK
  obtain ⟨L,hL,hDens⟩ := uniform_actualTraceDensity_scalar_jets hΩ (by omega : 2+1 ≤ m) K hK M
  let C := I₀*(G+P+L)
  have hG₀ := zero_le_one.trans hG
  have hP₀ := zero_le_one.trans hP
  have hI := zero_le_one.trans hI₀
  have hGC : I₀*G ≤ C := mul_le_mul_of_nonneg_left (by linarith only [hP₀,hL]) hI
  have hPC : I₀*P ≤ C := mul_le_mul_of_nonneg_left (by linarith only [hG₀,hL]) hI
  have hLC : I₀*L ≤ C := mul_le_mul_of_nonneg_left (by linarith only [hG₀,hP₀]) hI
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro floor hFloor ε hε hε₁ d hd hg he hr hr₀ hlog hQ hg₂ V x hx R H
  dsimp only
  let F := actualCoordinatePrincipalTraceFactors hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V
  let β := beta d.γ d.radius x
  let s := β⁻¹
  have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
  have hβp := zero_lt_one.trans_le hβ
  have hβ₀ := hβp.le
  have hs := inv_nonneg.mpr hβ₀
  have hGeom' := hGeom floor hFloor ε hε hε₁ d hd x hx
  have hProf' := (hProf floor hFloor ε d hd x hx).1
  have hRad : d.radius x ≤ ε*s^2 := by
    change d.radius x ≤ ε*(β⁻¹)^2
    rw [inv_pow,← div_eq_mul_inv,le_div_iff₀ (sq_pos_of_pos hβp)]
    exact (hd.2.2.2.2.2 x hx).2
  have hGε := mul_le_mul_of_nonneg_right hGC hε
  have hPε := mul_le_mul_of_nonneg_right hPC hε
  have hz (i j : I dim) : PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (C*ε*s^2) (F.principal i j) := by
    have h := PairedTraceFiberFamilyBounds.ofScalar (N:=2) (hY:=hY) hx hβ₀ hI₀ H.identity _
      (hr.mul (hQ i j)) (by positivity : 0 ≤ G*ε*s^2) (fun n hn => hGeom'.2 i j n (by omega))
    refine h.enlarge hβ₀ ?_
    rw [← mul_assoc,← mul_assoc]
    exact mul_le_mul_of_nonneg_right hGε (sq_nonneg _)
  have ha (i j k : I dim) : PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (C*ε*s) (F.principalDerivative i j k) := by
    let f (y : X dim) := d.radius y*principal d.γ d.g₂ y j k
    have hf : ContDiffOn ℝ ∞ f Y := hr.mul (hQ j k)
    have hf' : ContDiffOn ℝ ∞ (coordDeriv i f) Y :=
      (hf.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
    have h := PairedTraceFiberFamilyBounds.ofScalar (N:=2) (hY:=hY) hx hβ₀ hI₀ H.identity _ hf'
      (by positivity : 0 ≤ G*ε*s) (by
        intro n hn
        refine (norm_iteratedFDeriv_coordDeriv_le (hf.contDiffAt (hY.mem_nhds hx)) i n).trans
          ((hGeom'.2 j k (n+1) (by omega)).trans_eq ?_)
        change G*ε*s^2*β^(n+1) = (G*ε*s)*β^n
        have he : s^2*β = s := by dsimp only [s]; rw [pow_two,mul_assoc,inv_mul_cancel₀ hβp.ne',mul_one]
        calc
          _ = G*ε*(s^2*β)*β^n := by rw [pow_succ]; ring
          _ = _ := by rw [he])
    refine h.enlarge hβ₀ ?_
    rw [← mul_assoc,← mul_assoc]
    exact mul_le_mul_of_nonneg_right hGε hs
  have hq (i j : I dim) : PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (C*ε) (F.smallDifference i j) := by
    have h := PairedTraceFiberFamilyBounds.ofScalar (N:=2) (hY:=hY) hx hβ₀ hI₀ H.identity _
      (contDiffOn_tracePrincipalSmallDifference (hg.smoothMetric hK) hg₂ hr hr₀ i j)
      (mul_nonneg hG₀ hε) (fun n hn => hGeom'.1 i j n (by omega))
    exact h.enlarge hβ₀ (by rw [← mul_assoc]; exact hGε)
  have hr' : PairedTraceFiberFamilyBounds H.atoms hY x β 2 0 (C*ε*s^2) F.radius := by
    have h := PairedTraceFiberFamilyBounds.ofScalar (N:=2) (hY:=hY) hx hβ₀ hI₀ H.identity _ hr
      (by positivity : 0 ≤ P*ε*s^2) (by
        intro n hn
        refine (hProf' n (by omega)).trans ?_
        rw [mul_assoc P]
        exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRad (pow_nonneg hβ₀ n)) hP₀).trans_eq
          (by ring))
    exact h.enlarge hβ₀ (by rw [← mul_assoc,← mul_assoc]; exact mul_le_mul_of_nonneg_right hPε (sq_nonneg _))
  refine ⟨hz,ha,hq,hr',?_⟩
  intro i
  have h := hDens d.γ d.g₁ d.g₂ d.frame hd.1 x (hSub hx) i
  have hDensityBound := PairedTraceFiberFamilyBounds.ofScalar (N:=2) (hY:=hY) hx hβ₀ hI₀ H.identity _
    (contDiffOn_traceDensityDivergence hY (metricDensity d.γ) (hg.contDiffOn_density hK)
      (fun x hx => metricDensity_pos hg hK hx) (fun _ => axis i) contDiffOn_const)
    hL (fun n hn => (h.bound n hn).trans (le_mul_of_one_le_right hL (one_le_pow₀ hβ)))
  exact hDensityBound.enlarge hβ₀ hLC

end CalderonN
