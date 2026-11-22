module

public import Proof.CalderonN.SmoothSupportedTraceCoefficientSum
public import Proof.CalderonN.ActualSupportedLowerOrderVelocity

import Mathlib.Tactic

/-! The first normal-response formula propagates the actual angular
factor bounds to the coefficient of the lower-order commutator. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Matrix.Norms.Elementwise Topology
set_option autoImplicit false
set_option maxHeartbeats 6100000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}
abbrev TraceFiberFamily (dim : ℕ) := X dim → Module.End ℝ (SmoothSphereTrace dim)

theorem actualGaussLowerVelocity_bounds_of_factors (hn : 3 ≤ dim) (hY : IsOpen Y)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ D₀ : ℝ, 0 ≤ D₀ ∧ ∀ {d : Data dim} (F : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim)
      (hW : SmoothSupportedTraceFiberRegular Y (actualGaussLowerVelocityFamily F i))
      (x : X dim) (hx : x ∈ Y) (β : ℝ), 0 ≤ β →
      ∀ (B : Module.End ℝ (SmoothSphereTrace dim))
      (hB : SmoothSupportedTraceFiberRegular Y (fun _ => B))
      (hRB : ∀ a b : I dim,SmoothSupportedTraceFiberRegular Y (fun _ => smoothSphereTraceRotation a b)),
      SmoothSupportedTraceCoefficientBounds hn B hY x β 1 C (fun _ => B) hB →
      (∀ a b,SmoothSupportedTraceCoefficientBounds hn B hY x β 1 C
        (fun _ => smoothSphereTraceRotation a b) (hRB a b)) →
      ∀ (L H H₁ R M N : TraceFiberFamily dim) (V : I dim → I dim → TraceFiberFamily dim)
      (hL : SmoothSupportedTraceFiberRegular Y L) (hH : SmoothSupportedTraceFiberRegular Y H)
      (hH₁ : SmoothSupportedTraceFiberRegular Y H₁) (hR : SmoothSupportedTraceFiberRegular Y R)
      (hM : SmoothSupportedTraceFiberRegular Y M) (hN : SmoothSupportedTraceFiberRegular Y N)
      (hV : ∀ a b,SmoothSupportedTraceFiberRegular Y (V a b)),
      SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C L hL →
      SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C H hH →
      SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C H₁ hH₁ →
      SmoothSupportedTraceCoefficientBounds hn B hY x β 1 C R hR →
      SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C M hM →
      SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C N hN →
      (∀ a b,SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C (V a b) (hV a b)) →
      ∀ (hr : ContDiffOn ℝ ∞ d.radius Y), |d.radius x| ≤ C →
      (∀ a : X dim,‖a‖ ≤ 1 → |fderiv ℝ d.radius x a| ≤ C*β) →
      (∀ᶠ y in 𝓝 x,∀ hy : y ∈ Y,
        let A := F y hy
        let u := A.centerCorrection i
        d.radius y ≠ 0 ∧ A.flatDegree = B ∧
        A.affineCorrection+B*L y = (1/2:ℝ) • (L y*B+B*L y-L y) ∧
        L y = ActualGaussFiberData.affineDensityMul d y ∧ H y = smoothSphereTraceMul A.reciprocal ∧
        H₁ y = (d.radius y)⁻¹ • (H y-1) ∧ R y = ((d.radius y)^2)⁻¹ • A.conormalRemainder ∧
        M y = ActualGaussFiberData.translationMultiplier d y i+fderiv ℝ d.radius y (axis i) • 1 ∧
        N y = smoothSphereTraceMul (smoothVelocityNormal u) ∧
        ∀ a b,V a b y = smoothSphereTraceMul (smoothVelocityAngular u a b)) →
      SmoothSupportedTraceCoefficientBounds hn B hY x β 1 D₀ (actualGaussLowerVelocityFamily F i) hW := by
  let c := C*C+C*C
  let t := c+c+C+(c+c+C)
  let p := c+((t+c)*C+(t+c)*C)
  let n := C+(C*p+C*p)
  let g := ∑ _a : I dim,∑ _b : I dim,c
  let u := n*C+n*C+g
  let D₀ := p*C+p*C+(C*u+C*u)
  have hCp := zero_le_one.trans hC
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hn' : 0 ≤ n := by dsimp only [n]; positivity
  have hg' : 0 ≤ g := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hc
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  refine ⟨D₀,by dsimp only [D₀]; positivity,?_⟩
  intro d F i hW x hx β hβ B hB hRot bB bRot L H H₁ R M N V hL hH hH₁ hR hM hN hV bL bH bH₁ bR bM bN bV hr hR₀ hR₁ hEq
  have ht₀ := (((bL.mul bB hx hβ).add (bB.mul bL hx hβ) hx).sub
    (bL.weaken hβ (by decide : 0 ≤ 1)) hx).base_smul hx hβ (fun _ => 1/2) contDiffOn_const
      zero_le_one (by norm_num)
      (fun a ha => by simp only [fderiv_fun_const,Pi.zero_apply,zero_apply,abs_zero,one_mul]; exact hβ)
  have ht₁ : SmoothSupportedTraceCoefficientBounds hn B hY x β 1 t
      (fun y => (1/2:ℝ) • (L y*B+B*L y-L y))
      (((hL.mul hY hB).add (hB.mul hY hL)).sub hL |>.base_smul hY contDiffOn_const) := by
    simpa only [Nat.add_zero,Nat.zero_add,one_mul] using ht₀
  have hrr := bR.base_smul hx hβ d.radius hr hCp hR₀ hR₁
  have hp₁ := (bB.mul bH₁ hx hβ).add ((ht₁.add hrr hx).mul bH hx hβ) hx
  have hn₁ := bB.add (hp₁.base_smul hx hβ d.radius hr hCp hR₀ hR₁) hx
  have hRotV (a b : I dim) := (bRot a b).mul (bV a b) hx hβ
  let hRotV' (a b : I dim) := (hRot a b).mul hY (hV a b)
  have hG' := SmoothSupportedTraceCoefficientBounds.finite_sum hβ hx Finset.univ
    (fun a y => ∑ b : I dim,smoothSphereTraceRotation a b*V a b y)
    (fun _ => ∑ _b : I dim,c)
    (fun a _ => SmoothSupportedTraceFiberRegular.sum Finset.univ (fun b y => smoothSphereTraceRotation a b*V a b y)
      (fun b _ => hRotV' a b))
    (fun a _ => SmoothSupportedTraceCoefficientBounds.finite_sum hβ hx Finset.univ
      (fun b y => smoothSphereTraceRotation a b*V a b y) (fun _ => c)
      (fun b _ => hRotV' a b) (fun b _ => hRotV a b))
  have hEnd := (hp₁.mul bM hx hβ).add
    (((hn₁.mul bN hx hβ).sub hG' hx).base_smul hx hβ d.radius hr hCp hR₀ hR₁) hx
  have hSame : (fun y =>
      let T := (1/2:ℝ) • (L y*B+B*L y-L y)
      let P := B*H₁ y+(T+d.radius y • R y)*H y
      P*M y+d.radius y • ((B+d.radius y • P)*N y-
        ∑ a : I dim,∑ b : I dim,smoothSphereTraceRotation a b*V a b y)) =ᶠ[𝓝 x]
          actualGaussLowerVelocityFamily F i := by
    filter_upwards [hEq,hY.mem_nhds hx] with y hy hyY
    obtain ⟨hrne,hB',hT,hL',hH',hH₁',hR',hM',hN',hV'⟩ := hy hyY
    let A := F y hyY
    let r := d.radius y
    let P := B*H₁ y+((A.affineCorrection+B*L y)+r • R y)*H y
    have hA := A.affine_add_radius_velocityRemainder_eq hrne i
    have hNormal : A.normalResponse = B+r • P := by
      have hp' := A.normalResponse_eq_flat_add_firstDifference hrne
      dsimp only at hp'
      change A.normalResponse = B+r • (B*H₁ y+((A.affineCorrection+B*L y)+r • R y)*H y)
      rw [hH₁',hL',hH',hR',← hB']
      exact hp'
    simp only [actualGaussLowerVelocityFamily,dite_eq_left hyY]
    rw [← hT,← hNormal,hM',hN']
    simp_rw [hV']
    have hA' := hA.symm
    rw [hB',← hL',← hH',← hR',← hH₁'] at hA'
    exact hA' 
  exact hEnd.congr hx hSame

end CalderonN
