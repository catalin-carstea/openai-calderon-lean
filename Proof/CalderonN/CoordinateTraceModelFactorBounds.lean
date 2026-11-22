module

public import Proof.CalderonN.CoordinateTraceModelFactors
public import Proof.CalderonN.CoordinateTraceCoefficientBounds

import Mathlib.Tactic

/-! Angular orders and base weights of the coordinate model, its
radial correction, and the leading angular velocity. -/

public section

noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

namespace CoordinateTraceModelFactors

structure PrimitiveBounds (A : SmoothTraceSymbolAtoms hn) (hY : IsOpen Y) (x : X dim)
    (β C : ℝ) (F : CoordinateTraceModelFactors hn Y) : Prop where
  degree : PairedTraceFiberFamilyBounds A hY x β 2 1 C F.degree
  rotation : ∀ i j,PairedTraceFiberFamilyBounds A hY x β 2 1 C (F.rotation i j)
  raising : ∀ i,PairedTraceFiberFamilyBounds A hY x β 2 1 C (F.raising i)
  frameEntry : ∀ a i,PairedTraceFiberFamilyBounds A hY x β 2 0 C (F.frameEntry a i)
  coframeEntry : ∀ a i,PairedTraceFiberFamilyBounds A hY x β 2 0 C (F.coframeEntry a i)
  connection : ∀ i a b,PairedTraceFiberFamilyBounds A hY x β 2 0 C (F.connection i a b)
  logGradient : ∀ i,PairedTraceFiberFamilyBounds A hY x β 2 0 (C*β) (F.logGradient i)
  connectionDerivative : ∀ i j a b,PairedTraceFiberFamilyBounds A hY x β 1 0 (C*β^2)
    (F.connectionDerivative i j a b)
  logGradientDerivative : ∀ i j,PairedTraceFiberFamilyBounds A hY x β 1 0 (C*β^2)
    (F.logGradientDerivative i j)

structure Bounds (A : SmoothTraceSymbolAtoms hn) (hY : IsOpen Y) (x : X dim)
    (β C : ℝ) (F : CoordinateTraceModelFactors hn Y) : Prop where
  potential : ∀ i,PairedTraceFiberFamilyBounds A hY x β 2 1 (C*β) (F.potential hY i)
  potentialDerivative : ∀ i j,PairedTraceFiberFamilyBounds A hY x β 1 1 (C*β^2) (F.potentialDerivative hY i j)
  leading : ∀ i,PairedTraceFiberFamilyBounds A hY x β 2 1 C (F.leading hY i)
  first : ∀ i,PairedTraceFiberFamilyBounds A hY x β 2 1 C (F.first hY i)
  zero : PairedTraceFiberFamilyBounds A hY x β 1 2 (C*β) (F.zero hY)
  correction : PairedTraceFiberFamilyBounds A hY x β 1 1 (C*β) (F.correction hY)

theorem Bounds.enlarge {A : SmoothTraceSymbolAtoms hn} {hY : IsOpen Y} {x : X dim} {β C D : ℝ}
    {F : CoordinateTraceModelFactors hn Y} (h : Bounds A hY x β C F) (hβ : 0 ≤ β) (hCD : C ≤ D) :
    Bounds A hY x β D F :=
  ⟨fun i => (h.potential i).enlarge hβ (mul_le_mul_of_nonneg_right hCD hβ),
    fun i j => (h.potentialDerivative i j).enlarge hβ (mul_le_mul_of_nonneg_right hCD (sq_nonneg _)),
    fun i => (h.leading i).enlarge hβ hCD,fun i => (h.first i).enlarge hβ hCD,
    h.zero.enlarge hβ (mul_le_mul_of_nonneg_right hCD hβ),
    h.correction.enlarge hβ (mul_le_mul_of_nonneg_right hCD hβ)⟩

theorem bounds_of_primitives (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ (A : SmoothTraceSymbolAtoms hn) (hY : IsOpen Y) (x : X dim),x ∈ Y →
      ∀ β : ℝ,1 ≤ β → ∀ J : ℝ,SmoothTraceSymbolBounds A 0 J (1 : Module.End ℝ (SmoothSphereTrace dim)) →
      ∀ F : CoordinateTraceModelFactors hn Y,PrimitiveBounds A hY x β C F →
      Bounds A hY x β D F := by
  let c := 4*(C*C)
  let t := (dim:ℝ)*((dim:ℝ)*c)+c
  let l := (dim:ℝ)*c
  let z := (dim:ℝ)*(2*(l*t))
  let w := (dim:ℝ)*(2*(C*l))
  let D := t+l+z+w
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hl : 0 ≤ l := by dsimp only [l]; positivity
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  refine ⟨D,by dsimp only [D]; positivity,?_⟩
  intro A hY x hx β hβ J hI F h
  have hβ₀ := zero_le_one.trans hβ
  have hZero (k : ℕ) := hI.zero_of_identity k
  have sum (N k : ℕ) (P : I dim → PairedTraceFiberFamily hn Y) (K : ℝ)
      (hP : ∀ i,PairedTraceFiberFamilyBounds A hY x β N k K (P i)) :
      PairedTraceFiberFamilyBounds A hY x β N k ((dim:ℝ)*K) (PairedTraceFiberFamily.finiteSum Finset.univ P) := by
    have h := PairedTraceFiberFamilyBounds.finite_sum hx hβ₀ Finset.univ P (fun _ => K) (hZero k) (fun i _ => hP i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h
  have hPot (i : I dim) : PairedTraceFiberFamilyBounds A hY x β 2 1 (t*β) (F.potential hY i) := by
    have ha := sum 2 1 _ ((dim:ℝ)*c) (fun a => sum 2 1 _ c (fun b => by
      simpa only [c,show max (2:ℝ) ((2:ℝ)^2) = 4 by norm_num] using
        (h.connection i a b).mul hx hβ₀ (h.rotation a b)))
    have hb := (h.logGradient i).mul hx hβ₀ h.degree
    refine (ha.add hx hb).enlarge hβ₀ ?_
    have hh := le_mul_of_one_le_right (show 0 ≤ (dim:ℝ)*((dim:ℝ)*c) by positivity) hβ
    simp only [show max (2:ℝ) (2^2) = 4 by norm_num,t,c]
    dsimp only [c] at hh
    nlinarith only [hh]
  have hPot' (i j : I dim) :
      PairedTraceFiberFamilyBounds A hY x β 1 1 (t*β^2) (F.potentialDerivative hY i j) := by
    have ha := sum 1 1 _ ((dim:ℝ)*(c*β^2)) (fun a => sum 1 1 _ (c*β^2) (fun b => by
      have hb := (h.connectionDerivative i j a b).mul hx hβ₀ ((h.rotation a b).restrict (by decide))
      refine hb.enlarge hβ₀ ?_
      simp only [show max (2:ℝ) (2^1) = 2 by norm_num,c]
      nlinarith only [mul_nonneg (sq_nonneg C) (sq_nonneg β)]))
    have hb := (h.logGradientDerivative i j).mul hx hβ₀ (h.degree.restrict (by decide))
    refine (ha.add hx hb).enlarge hβ₀ ?_
    simp only [show max (2:ℝ) (2^1) = 2 by norm_num,t,c]
    nlinarith only [mul_nonneg (sq_nonneg C) (sq_nonneg β)]
  have hRaise (P : I dim → PairedTraceFiberFamily hn Y)
      (hP : ∀ a,PairedTraceFiberFamilyBounds A hY x β 2 0 C (P a)) :
      PairedTraceFiberFamilyBounds A hY x β 2 1 l
        (PairedTraceFiberFamily.finiteSum Finset.univ (fun a => (P a).mul hY (F.raising a))) :=
    sum 2 1 (fun a => (P a).mul hY (F.raising a)) c (fun a => by
      have h := (hP a).mul hx hβ₀ (h.raising a)
      simpa only [c,show max (2:ℝ) (2^2) = 4 by norm_num] using h)
  have hLead (i : I dim) : PairedTraceFiberFamilyBounds A hY x β 2 1 l (F.leading hY i) :=
    hRaise _ (fun a => h.coframeEntry a i)
  have hFirst (i : I dim) : PairedTraceFiberFamilyBounds A hY x β 2 1 l (F.first hY i) :=
    hRaise _ (fun a => h.frameEntry a i)
  have hZ : PairedTraceFiberFamilyBounds A hY x β 1 2 (z*β) (F.zero hY) := by
    have hh := sum 1 2 (fun i => (F.first hY i).mul hY (F.potential hY i)) (2*(l*t)*β) (fun i => by
      have h := ((hFirst i).restrict (by decide : 1 ≤ 2)).mul hx hβ₀ ((hPot i).restrict (by decide))
      simpa only [show max (2:ℝ) (2^1) = 2 by norm_num,mul_assoc] using h)
    simpa only [z,mul_assoc,zero] using hh
  have hW : PairedTraceFiberFamilyBounds A hY x β 1 1 (w*β) (F.correction hY) := by
    have hh := sum 1 1 (fun i => (F.logGradient i).mul hY (F.first hY i).adj) (2*(C*l)*β) (fun i => by
      have h := ((h.logGradient i).restrict (by decide : 1 ≤ 2)).mul hx hβ₀ ((hFirst i).adj hx hβ₀ |>.restrict (by decide))
      refine h.enlarge hβ₀ ?_
      rw [show max (2:ℝ) (2^1) = 2 by norm_num]
      apply le_of_eq
      ring)
    simpa only [w,mul_assoc,correction] using hh
  have hTD : t ≤ D := by dsimp only [D]; linarith only [hl,hz,hw]
  have hLD : l ≤ D := by dsimp only [D]; linarith only [ht,hz,hw]
  have hZD : z ≤ D := by dsimp only [D]; linarith only [ht,hl,hw]
  have hWD : w ≤ D := by dsimp only [D]; linarith only [ht,hl,hz]
  exact ⟨fun i => (hPot i).enlarge hβ₀ (mul_le_mul_of_nonneg_right hTD hβ₀),
    fun i j => (hPot' i j).enlarge hβ₀ (mul_le_mul_of_nonneg_right hTD (sq_nonneg _)),
    fun i => (hLead i).enlarge hβ₀ hLD,fun i => (hFirst i).enlarge hβ₀ hLD,
    hZ.enlarge hβ₀ (mul_le_mul_of_nonneg_right hZD hβ₀),hW.enlarge hβ₀ (mul_le_mul_of_nonneg_right hWD hβ₀)⟩

end CoordinateTraceModelFactors

end CalderonN
