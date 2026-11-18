import Proof.SmoothBoundarySeparation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothAngularCasimir

/-- The frozen Dirichlet duality uniquely identifies a physical L2 adjoint on
    every smooth input component. The constructed output need only be L2;
    smooth test density supplies the uniqueness. -/
theorem Admissible.frozen_adjoint_component_realization {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y) (i : I)
    (T Ta : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hPair : ∀ f v,⟪T f,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) f,Ta v⟫_ℝ)
    (hForward : ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
      ∀ f : SphereSobolev (3/2:ℝ),
      (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
        u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (T (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f)) =ᵐ[sphereProbability]
          fun w : UnitSphere => horizontal d.γ (fun p => u (endpoint d.expMap d.radius p))
            y (frameVector d.frame y w.val) (axis i))
    (φ : Field) (hφ : smoothNear φ (bundle Y d.γ)) (L : ℂ →L[ℝ] ℝ)
    (v : SphereSobolev 1)
    (hInput : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) v) =ᵐ[sphereProbability]
        fun w : UnitSphere => L (φ (y,frameVector d.frame y w.val))) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (Ta v)
      =ᵐ[sphereProbability] fun w : UnitSphere => L (adjointField d.adjoint i φ (y,frameVector d.frame y w.val)) := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let F : UnitSphere → ℂ := fun w => φ (y,frameVector d.frame y w.val)
  let G : UnitSphere → ℂ := fun w => adjointField d.adjoint i φ (y,frameVector d.frame y w.val)
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hAdj := hd.2.2.2.1 i φ hφ
  have hFC : Continuous F := (hφ.sphere_slice hy).continuous_frame_slice hFrame
  have hGC : Continuous G := (hAdj.1.sphere_slice hy).continuous_frame_slice hFrame
  let Fc : C(UnitSphere,ℂ) := ⟨F,hFC⟩
  let Gc : C(UnitSphere,ℂ) := ⟨G,hGC⟩
  let Gr : C(UnitSphere,ℝ) := ⟨fun w => L (G w),L.continuous.comp hGC⟩
  let g : SphereL2 := (ContinuousMap.toLp 2 sphereProbability ℝ) Gr
  have hGValue : g =ᵐ[sphereProbability] fun w => L (G w) :=
    ContinuousMap.coeFn_toLp (p:=2) (μ:=sphereProbability) (𝕜:=ℝ) Gr
  have hMemF : MemLp F 2 sphereProbability := continuousSphere_memLp_complex Fc
  have hMemG : MemLp G 2 sphereProbability := continuousSphere_memLp_complex Gc
  have hEq : g = Z.symm (Ta v) := by
    apply sphereL2_eq_of_smooth_inner
    intro f
    have hTestHere := hd.exists_harmonic_smooth_sphere_test hy f
    obtain ⟨u,hu,hValue,hBoundary⟩ := hTestHere
    let f1 := smoothOneBoundaryData f
    have hH := hForward u hu (smoothHighBoundaryData f) hBoundary
    have hDual := hAdj.2 y hy u hu
    change (∫ w : UnitSphere,G w*(u (normalChart d.expMap d.frame y (d.radius y) w.val) : ℂ) ∂sphereProbability) =
      ∫ w : UnitSphere,F w*((horizontal d.γ (fun p => u (endpoint d.expMap d.radius p))
        y (frameVector d.frame y w.val) (axis i) : ℝ) : ℂ) ∂sphereProbability at hDual
    have hLeft : (∫ w : UnitSphere,G w*(f.1 w.val : ℂ) ∂sphereProbability) =
        ∫ w : UnitSphere,G w*(u (normalChart d.expMap d.frame y (d.radius y) w.val) : ℂ) ∂sphereProbability := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun w => congrArg (fun t : ℝ => G w*(t:ℂ)) (hValue w).symm)
    have hReal := realComponent_pairing_of_complex_integral F G hMemF hMemG L
      (smoothSphereLift f.1 f.2) (Z.symm (T f1)) (Z.symm (I0 v)) g
      (fun w => f.1 w.val)
      (fun w => horizontal d.γ (fun p => u (endpoint d.expMap d.radius p)) y (frameVector d.frame y w.val) (axis i))
      (ContinuousMap.coeFn_toLp (p:=2) (μ:=sphereProbability) (𝕜:=ℝ) (smoothSphereValue f))
      hH hInput hGValue (hLeft.trans hDual)
    have hNative : ⟪Z.symm (T f1),Z.symm (I0 v)⟫_ℝ = ⟪smoothSphereLift f.1 f.2,Z.symm (Ta v)⟫_ℝ := by
      calc
        _ = ⟪T f1,I0 v⟫_ℝ := Z.symm.inner_map_map _ _
        _ = ⟪I0 f1,Ta v⟫_ℝ := hPair f1 v
        _ = ⟪Z (smoothSphereLift f.1 f.2),Ta v⟫_ℝ :=
          congrArg (fun q : SphereSobolev 0 => ⟪q,Ta v⟫_ℝ) (smoothOneBoundaryData_coarse f)
        _ = _ := by
          have h := Z.inner_map_map (smoothSphereLift f.1 f.2) (Z.symm (Ta v))
          rw [Z.apply_symm_apply] at h
          exact h
    exact hReal.trans hNative
  rw [← hEq]
  exact hGValue

end ShrinkingSpheres
