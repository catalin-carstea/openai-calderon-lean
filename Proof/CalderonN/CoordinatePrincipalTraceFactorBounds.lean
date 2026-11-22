module

public import Proof.CalderonN.CoordinatePrincipalTraceFactors
public import Proof.CalderonN.CoordinateTraceModelFactorBounds
public import Proof.CalderonN.CoordinateTraceCoefficientBounds
public import Proof.CalderonN.SmoothTraceNegation

import Mathlib.Tactic

/-! The small numerator and radius weights in the coordinate
divergence coefficients. -/

public section

noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 5400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

namespace PairedTraceFiberFamilyBounds

theorem mulFour {A : SmoothTraceSymbolAtoms hn} {hY : IsOpen Y} {x : X dim}
    {β C D : ℝ} {N k l : ℕ} {F G : PairedTraceFiberFamily hn Y}
    (h : PairedTraceFiberFamilyBounds A hY x β N k C F) (hx : x ∈ Y) (hβ : 0 ≤ β) (hN : N ≤ 2)
    (h' : PairedTraceFiberFamilyBounds A hY x β N l D G) :
    PairedTraceFiberFamilyBounds A hY x β N (k+l) (4*(C*D)) (F.mul hY G) := by
  refine (h.mul hx hβ h').enlarge hβ (mul_le_mul_of_nonneg_right ?_ (mul_nonneg h.nonneg h'.nonneg))
  exact max_le (by norm_num) ((pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hN).trans_eq (by norm_num))

end PairedTraceFiberFamilyBounds

namespace CoordinatePrincipalTraceFactors

structure PrimitiveBounds (A : SmoothTraceSymbolAtoms hn) (hY : IsOpen Y) (x : X dim)
    (β ε C : ℝ) (F : CoordinatePrincipalTraceFactors hn Y) : Prop where
  principal : ∀ i j,PairedTraceFiberFamilyBounds A hY x β 2 0 (C*ε*(β⁻¹)^2) (F.principal i j)
  principalDerivative : ∀ i j k,PairedTraceFiberFamilyBounds A hY x β 2 0 (C*ε*β⁻¹) (F.principalDerivative i j k)
  smallDifference : ∀ i j,PairedTraceFiberFamilyBounds A hY x β 2 0 (C*ε) (F.smallDifference i j)
  radius : PairedTraceFiberFamilyBounds A hY x β 2 0 (C*ε*(β⁻¹)^2) F.radius
  density : ∀ i,PairedTraceFiberFamilyBounds A hY x β 2 0 C (F.density i)
  model : CoordinateTraceModelFactors.Bounds A hY x β C F.model
  velocityRemainder : ∀ i,PairedTraceFiberFamilyBounds A hY x β 2 1 C (F.velocity.velocityRemainder hY i)
  lowerVelocity : ∀ i,PairedTraceFiberFamilyBounds A hY x β 2 1 C (F.velocity.lowerVelocity hY i)

theorem bounds_of_primitives (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ (A : SmoothTraceSymbolAtoms hn) (hY : IsOpen Y) (x : X dim),x ∈ Y →
      ∀ β ε : ℝ,1 ≤ β → 0 ≤ ε → ε ≤ 1 →
      ∀ J : ℝ,SmoothTraceSymbolBounds A 0 J (1 : Module.End ℝ (SmoothSphereTrace dim)) →
      ∀ F : CoordinatePrincipalTraceFactors hn Y,PrimitiveBounds A hY x β ε C F →
      CoordinateTraceDivergenceBounds A hY x β (D*ε) D (F.divergence hY) := by
  let b := 8*C^2+16*C^3
  let d := C+4*C^2
  let c := 16*C^3+128*C^4+4*C*(24*C^2+C)
  let B := 2*((dim:ℝ)*b)+(dim:ℝ)*d
  let E := (dim:ℝ)*((dim:ℝ)*c)
  let D := C+B+E
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨D,by dsimp only [D]; positivity,?_⟩
  intro A hY x hx β ε hβ hε hε₁ J hI F h
  let s := β⁻¹
  have hβp := zero_lt_one.trans_le hβ
  have hβ₀ := hβp.le
  have hs : 0 ≤ s := inv_nonneg.mpr hβ₀
  have hs₁ : s ≤ 1 := inv_le_one_of_one_le₀ hβ
  have hi : s*β = 1 := inv_mul_cancel₀ hβp.ne'
  have hi₂ : s^2*β^2 = 1 := by rw [← mul_pow,hi,one_pow]
  have hi₁ : s^2*β = s := by rw [pow_two,mul_assoc,hi,mul_one]
  have hs₂ : s^2 ≤ s := by rw [pow_two]; exact mul_le_of_le_one_right hs hs₁
  have hε₂ : ε^2 ≤ ε := by rw [pow_two]; exact mul_le_of_le_one_right hε hε₁
  have hD₀ : C ≤ D := by dsimp only [D]; linarith only [hB,hE]
  have hD₁ : B ≤ D := by dsimp only [D]; linarith only [hC,hE]
  have hD₂ : E ≤ D := by dsimp only [D]; linarith only [hC,hB]
  have sum (N k : ℕ) (T : I dim → PairedTraceFiberFamily hn Y) (K : ℝ)
      (hT : ∀ i,PairedTraceFiberFamilyBounds A hY x β N k K (T i)) :
      PairedTraceFiberFamilyBounds A hY x β N k ((dim:ℝ)*K) (PairedTraceFiberFamily.finiteSum Finset.univ T) := by
    have ht := PairedTraceFiberFamilyBounds.finite_sum hx hβ₀ Finset.univ T (fun _ => K) (hI.zero_of_identity k)
      (fun i _ => hT i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using ht
  have hFirst (i j k : I dim) : PairedTraceFiberFamilyBounds A hY x β 2 1 (b*ε*s) (F.firstNormalEntry hY i j k) := by
    have hKW := (h.model.potential k).add hx (h.lowerVelocity k)
    have hAKW := (h.principal i j).mulFour hx hβ₀ (by decide) hKW
    have hAKW' : PairedTraceFiberFamilyBounds A hY x β 2 1 (8*C^2*ε*s)
        ((F.principal i j).mul hY ((F.model.potential hY k).add (F.velocity.lowerVelocity hY k))) := by
      refine hAKW.enlarge hβ₀ ?_
      change 4*(C*ε*s^2*(C*β+C)) ≤ 8*C^2*ε*s
      have h' := mul_le_mul_of_nonneg_left hs₂ (show 0 ≤ 4*C^2*ε by positivity)
      calc
        _ = (4*C^2*ε)*(s^2*β)+(4*C^2*ε)*s^2 := by ring
        _ ≤ _ := by rw [hi₁]; nlinarith only [h']
    have hRV := ((h.radius.mulFour hx hβ₀ (by decide) (h.smallDifference i j)).mulFour hx hβ₀ (by decide)
      (h.model.leading k))
    have hRV' : PairedTraceFiberFamilyBounds A hY x β 2 1 (16*C^3*ε*s)
        (((F.radius.mul hY (F.smallDifference i j)).mul hY (F.model.leading hY k))) := by
      refine hRV.enlarge hβ₀ ?_
      change 4*(4*(C*ε*s^2*(C*ε))*C) ≤ 16*C^3*ε*s
      calc
        _ = 16*C^3*(ε^2*s^2) := by ring
        _ ≤ 16*C^3*(ε*s) := mul_le_mul_of_nonneg_left (mul_le_mul hε₂ hs₂ (sq_nonneg _) hε) (by positivity)
        _ = _ := by ring
    refine (hAKW'.add hx hRV').enlarge hβ₀ ?_
    dsimp only [b]
    apply le_of_eq
    ring
  have hAdj (i j : I dim) : PairedTraceFiberFamilyBounds A hY x β 2 0 (d*ε*s)
      ((F.principalDerivative j j i).add ((F.density j).mul hY (F.principal j i))) := by
    refine ((h.principalDerivative j j i).add hx
      ((h.density j).mulFour hx hβ₀ (by decide) (h.principal j i))).enlarge hβ₀ ?_
    change C*ε*s+4*(C*(C*ε*s^2)) ≤ d*ε*s
    have h' := mul_le_mul_of_nonneg_left hs₂ (show 0 ≤ 4*C^2*ε by positivity)
    dsimp only [d]
    nlinarith only [h']
  have hB' (i : I dim) : PairedTraceFiberFamilyBounds A hY x β 2 1 (B*ε*s) (F.first hY i) := by
    have h₁ := sum 2 1 (fun j => F.firstNormalEntry hY i j j) _ (fun j => hFirst i j j)
    have h₂ := sum 2 1 (fun j => F.firstNormalEntry hY j i j) _ (fun j => hFirst j i j)
    have h₃ := sum 2 0 _ _ (fun j => hAdj i j)
    refine ((h₁.add hx h₂).sub hx (h₃.weaken hβ₀ (by decide))).enlarge hβ₀ ?_
    dsimp only [B]
    apply le_of_eq
    ring
  have hEntry (i j : I dim) :
      PairedTraceFiberFamilyBounds A hY x β 1 2 (c*ε) (F.zeroNormalizedEntry hY i j) := by
    let R (i : I dim) := (h.model.leading i).restrict (by decide : 1 ≤ 2)
    let K (i : I dim) := (h.model.potential i).restrict (by decide : 1 ≤ 2)
    let G (i : I dim) := (h.velocityRemainder i).restrict (by decide : 1 ≤ 2)
    let W (i : I dim) := (h.lowerVelocity i).restrict (by decide : 1 ≤ 2)
    let h4 := (by decide : 1 ≤ 2)
    have hq := (h.smallDifference i j).restrict h4
    have hr := h.radius.restrict h4
    have ha := (h.principal i j).restrict h4
    have hVV := (hq.mulFour hx hβ₀ h4 (R i)).mulFour hx hβ₀ h4 (R j)
    have hVK := (R i).mulFour hx hβ₀ h4 (K j)
    have hKV := (R j).mulFour hx hβ₀ h4 (K i)
    have hRV := (hr.mulFour hx hβ₀ h4 hq).mulFour hx hβ₀ h4 (hVK.add hx hKV)
    have hVK' : 4*(4*(C*ε*s^2*(C*ε))*(4*(C*(C*β))+4*(C*(C*β)))) ≤ 128*C^4*ε := by
      have hL : ε^2*s ≤ ε := (mul_le_of_le_one_right (sq_nonneg _) hs₁).trans hε₂
      calc
        _ = (128*C^4)*(ε^2*(s^2*β)) := by ring
        _ ≤ _ := by rw [hi₁]; exact mul_le_mul_of_nonneg_left hL (by positivity)
    have hVV' : 4*(4*(C*ε*C)*C) ≤ 16*C^3*ε := by apply le_of_eq; ring
    have hRG := (R i).mulFour hx hβ₀ h4 (G j)
    have hGR := (G i).mulFour hx hβ₀ h4 (R j)
    have hKK := (K i).mulFour hx hβ₀ h4 (K j)
    have hWK := (W j).mulFour hx hβ₀ h4 (K i)
    have hKW := (W i).mulFour hx hβ₀ h4 (K j)
    have hWW := (W i).mulFour hx hβ₀ h4 (W j)
    have hDK := (h.model.potentialDerivative i j).weaken hβ₀ (by decide : 1 ≤ 2)
    have hSum := (((((hRG.add hx hGR).add hx hKK).add hx hWK).add hx hKW).add hx hWW).add hx hDK
    have hSize : 4*(C*C)+4*(C*C)+4*(C*β*(C*β))+4*(C*(C*β))+4*(C*(C*β))+4*(C*C)+C*β^2 ≤
        (24*C^2+C)*β^2 := by
      have h1 : 1 ≤ β^2 := one_le_pow₀ hβ
      have h2 : β ≤ β^2 := by nlinarith only [mul_le_mul_of_nonneg_left hβ hβ₀]
      have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 12*C^2 by positivity)
      have h4 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 8*C^2 by positivity)
      nlinarith only [h3,h4]
    have hSum' := hSum.enlarge hβ₀ hSize
    have hProd := ha.mulFour hx hβ₀ (by decide : 1 ≤ 2) hSum'
    have hProd' := hProd.enlarge hβ₀ (show 4*(C*ε*s^2*((24*C^2+C)*β^2)) ≤ (4*C*(24*C^2+C))*ε from by
      apply le_of_eq
      calc
        _ = (4*C*(24*C^2+C))*ε*(s^2*β^2) := by ring
        _ = _ := by rw [hi₂,mul_one])
    refine (((hVV.enlarge hβ₀ hVV').add hx (hRV.enlarge hβ₀ hVK')).add hx hProd').enlarge hβ₀ ?_
    dsimp only [c]
    apply le_of_eq
    ring
  have hE' : PairedTraceFiberFamilyBounds A hY x β 1 2 (E*ε) (F.zero hY) := by
    have hh := sum 1 2 _ ((dim:ℝ)*(c*ε)) (fun i => sum 1 2 _ (c*ε) (hEntry i))
    simpa only [E,zero,mul_assoc] using hh
  refine ⟨fun i => (h.density i).symbol.angular.enlarge hD₀,?_,?_,?_,hE'.enlarge hβ₀ (mul_le_mul_of_nonneg_right hD₂ hε)⟩
  · intro i j
    exact (h.principal i j).symbol.angular.neg.enlarge
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD₀ hε) (sq_nonneg _))
  · intro i j k
    change SmoothTraceAngularBound hn 0 _ (((F.principal i j).forward.neg.derivative hY (axis k)).1 x)
    rw [RegularTraceFiberFamily.derivative_neg_value hY _ _ hx]
    refine (((h.principal i j).jets.atAxis (by decide) k).neg).enlarge ?_
    change C*ε*s^2*β ≤ D*ε*s
    calc
      _ = C*ε*(s^2*β) := by ring
      _ ≤ _ := by rw [hi₁]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD₀ hε) hs
  · intro i
    exact (hB' i).enlarge hβ₀ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD₁ hε) hs)

end CoordinatePrincipalTraceFactors

end CalderonN
