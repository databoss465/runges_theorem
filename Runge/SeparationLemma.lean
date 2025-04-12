import Mathlib
import Runge.Basic
import Runge.GridContour

open Complex Set Finset Metric RatFunc

#check Continuous.exists_forall_le'
#check IsCompact.exists_isMinOn

-- Compact set `K` has a point of minimal distance to any other set `U`
lemma point_of_least_sep (K U : Set ℂ) [Gridable K] :
  ∃ x₀ ∈ K, ∀ x ∈ K, infDist x₀ U ≤ infDist x U := by
  let f : ℂ → ℝ := fun x ↦ infDist x U
  have hfK : ∃ x₀ ∈ K, IsMinOn f K x₀ := by
    apply IsCompact.exists_isMinOn
    · exact Gridable.hK
    · exact Gridable.hNon
    · apply Continuous.continuousOn
      unfold f
      apply continuous_infDist_pt

  change ∃ x₀ ∈ K, ∀ x ∈ K, f x₀ ≤ f x
  obtain ⟨x₀, h₁, h₂⟩ := hfK
  use x₀, h₁
  rw [isMinOn_iff] at h₂
  exact h₂

-- If `x` and `y` are elements of `closed square z δ`, then `dist x y < 2 * δ`
lemma square_dist {z x y : ℂ} {δ : ℝ} (hδ : 0 < δ) (hx : x ∈ closed_square z δ)
  (hy : y ∈ closed_square z δ) : dist x y < 2 * δ := by

  have hxy : dist x y ≤ √ (δ ^ 2 + δ ^ 2) := by
    rw [Complex.dist_eq_re_im, Real.sqrt_le_sqrt_iff]
    apply add_le_add
    · rw [sq_le_sq, abs_eq_self.mpr (LT.lt.le hδ), ←Real.dist_eq]
      have h₁ : x.re ∈ Icc z.re (z.re + δ) := by
        unfold closed_square at hx
        rw [Complex.mem_reProdIm] at hx
        exact hx.1
      have h₂ : y.re ∈ Icc z.re (z.re + δ) := by
        unfold closed_square at hy
        rw [Complex.mem_reProdIm] at hy
        exact hy.1
      rw [←sub_sub_self z.re δ, ← sub_add, tsub_add_eq_add_tsub]
      apply Real.dist_le_of_mem_Icc h₁ h₂
      rfl

    · rw [sq_le_sq, abs_eq_self.mpr (LT.lt.le hδ), ←Real.dist_eq]
      have h₁ : x.im ∈ Icc z.im (z.im + δ) := by
        unfold closed_square at hx
        rw [Complex.mem_reProdIm] at hx
        exact hx.2
      have h₂ : y.im ∈ Icc z.im (z.im + δ) := by
        unfold closed_square at hy
        rw [Complex.mem_reProdIm] at hy
        exact hy.2
      rw [←sub_sub_self z.im δ, ← sub_add, tsub_add_eq_add_tsub]
      apply Real.dist_le_of_mem_Icc h₁ h₂
      rfl

    · apply add_nonneg
      · apply sq_nonneg
      · apply sq_nonneg

  have hδ' : √2 * δ < 2 * δ := by
    apply mul_lt_mul_of_pos_right _ hδ
    rw [Real.sqrt_lt zero_le_two zero_le_two]
    ring
    linarith

  calc
    dist x y ≤ √ (δ ^ 2 + δ ^ 2) := hxy
    _ = √(2 * δ ^ 2) := by ring_nf
    _ = √2 * √ (δ ^ 2) := by apply Real.sqrt_mul zero_le_two
    _ = √2 * δ := by rw [Real.sqrt_sq (LT.lt.le hδ)]
    _ < 2 * δ := hδ'

-- For every `x` in the `GridContourSet K hδ`, there exists a `y` in `K` such that `dist x y < 2 * δ`
lemma grid_contour_sep (K : Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) :
  ∀ x ∈ (GridContourSet K hδ), ∃ y ∈ K, dist x y < 2 * δ := by

  let ε := 2 * δ
  have hε : 0 < ε := by apply mul_pos; linarith; exact hδ
  let V := (Mesh (Box K hε) hδ).filter (fun v ↦ ((closed_square v δ) ∩ K).Nonempty)
  let edges := (DirectedEdgeSetOriented K hδ V)
  have h : GridContourSet K hδ = ⋃ e ∈ edges, edgeInterval e := by rfl

  intro x hx
  rw [h, mem_iUnion] at hx
  obtain ⟨⟨z,w⟩, interval, he, hx⟩ := hx
  simp at he
  let ⟨h, he⟩ := he
  rw [←he] at hx

  by_cases h₁ : z.re < w.re

  -- z.re < w.re
  · by_cases h₂ : z.im = w.im

    -- z.im = w.im
    · unfold edgeInterval at hx
      have h' : ¬z.re = w.re := by linarith
      simp [h', h₂] at hx
      rw [min_eq_left_of_lt h₁, max_eq_right_of_lt h₁] at hx

      unfold edges at h
      apply mem_directed_edge_set at h
      unfold ContourGraph at h
      simp at h
      let ⟨_, h⟩ := h
      unfold one_common_square at h
      simp [h₁] at h
      let ⟨ha, h⟩ := h

      have hzw : w.re = z.re + δ := by
        rw [norm_def (w - z), normSq_apply, sub_im, h₂, sub_self] at ha
        simp at ha
        rw [Real.sqrt_mul_self] at ha
        linarith
        simp [h₁]
        exact LT.lt.le h₁

      have h_sub : (Icc (z.re) (z.re + δ) ×ℂ {z.im}) ⊆ (closed_square z δ) := by
        unfold closed_square
        apply reProdIm_subset_iff.mpr
        apply prod_mono_right
        apply Set.singleton_subset_iff.mpr
        simp
        exact LT.lt.le hδ

      have h_sub' : (Icc (z.re) (z.re + δ) ×ℂ {z.im}) ⊆ (closed_square (z - δ * I) δ) := by
            unfold closed_square
            simp
            apply reProdIm_subset_iff.mpr
            rw [← hzw]
            apply prod_mono_right
            apply Set.singleton_subset_iff.mpr
            simp
            exact LT.lt.le hδ

      rw [h₂, ←hzw] at h_sub
      rw [h₂, ←hzw] at h_sub'

      cases h with
      | inl h =>
        obtain ⟨y, hy⟩ := nonempty_def.mp h.1
        rw [mem_inter_iff] at hy
        use y
        constructor
        · exact hy.2
        · have hx' : x ∈ closed_square z δ := Set.mem_of_subset_of_mem h_sub hx
          exact square_dist hδ hx' hy.1

      | inr h =>
        obtain ⟨y, hy⟩ := nonempty_def.mp h.2
        rw [mem_inter_iff] at hy
        use y
        constructor
        · exact hy.2
        · have hx' : x ∈ closed_square (z- δ * I) δ := Set.mem_of_subset_of_mem h_sub' hx
          exact square_dist hδ hx' hy.1

    -- z.im ≠ w.im : Pathology
    · exfalso
      unfold edgeInterval at hx
      have h' : ¬z.re = w.re := by linarith
      simp [h', h₂] at hx

  · have h₁' : w.re < z.re ∨ w.re = z.re := by
      apply LE.le.lt_or_eq
      apply le_of_not_gt
      linarith
    cases h₁' with

    -- w.re  < z.re
    | inl h₁' =>
      by_cases h₂ : z.im = w.im

      -- z.im = w.im
      · -- unfold the GridContour.Adj somewhere here and get cases
        unfold edgeInterval at hx
        have h' : ¬z.re = w.re := by linarith
        simp [h', h₂] at hx
        rw [min_comm, min_eq_left_of_lt h₁', max_comm, max_eq_right_of_lt h₁'] at hx

        unfold edges at h
        apply mem_directed_edge_set at h
        unfold ContourGraph at h
        simp at h
        let ⟨_, h⟩ := h
        unfold one_common_square at h
        simp [h₁, h₁'] at h
        let ⟨ha, h⟩ := h

        have hzw : z.re = w.re + δ := by
          rw [norm_def (w - z), normSq_apply, sub_im, h₂, sub_self] at ha
          simp at ha
          rw [Real.sqrt_mul_self_eq_abs, abs_eq] at ha
          cases ha
          · linarith
          · linarith
          exact LT.lt.le hδ

        have h_sub : (Icc (w.re) (w.re + δ) ×ℂ {w.im}) ⊆ (closed_square w δ) := by
          unfold closed_square
          apply reProdIm_subset_iff.mpr
          apply prod_mono_right
          apply Set.singleton_subset_iff.mpr
          simp
          exact LT.lt.le hδ

        have h_sub' : (Icc (w.re) (w.re + δ) ×ℂ {w.im}) ⊆ (closed_square (w - δ * I) δ) := by
          unfold closed_square
          simp
          apply reProdIm_subset_iff.mpr
          rw [← hzw]
          apply prod_mono_right
          apply Set.singleton_subset_iff.mpr
          simp
          exact LT.lt.le hδ

        rw [←hzw] at h_sub
        rw [←hzw] at h_sub'

        cases h with
        | inl h =>
          obtain ⟨y, hy⟩ := nonempty_def.mp h.1
          rw [mem_inter_iff] at hy
          use y
          constructor
          · exact hy.2
          · have hx' : x ∈ closed_square w δ := Set.mem_of_subset_of_mem h_sub hx
            exact square_dist hδ hx' hy.1

        | inr h =>
          obtain ⟨y, hy⟩ := nonempty_def.mp h.2
          rw [mem_inter_iff] at hy
          use y
          constructor
          · exact hy.2
          · have hx' : x ∈ closed_square (w - δ * I) δ := Set.mem_of_subset_of_mem h_sub' hx
            exact square_dist hδ hx' hy.1

      -- z.im ≠ w.im : Pathology
      · exfalso
        unfold edgeInterval at hx
        have h' : ¬z.re = w.re := by linarith
        simp [h', h₂] at hx

    -- w.re = z.re
    | inr h₁' =>
      by_cases h₂ : z.im < w.im

      -- z.im < w.im
      · -- unfold the GridContour.Adj somewhere here and get cases
        unfold edgeInterval at hx
        have h' : ¬ z.im = w.im := by linarith
        simp [h₁', h'] at hx
        rw [min_eq_left_of_lt h₂, max_eq_right_of_lt h₂] at hx

        unfold edges at h
        apply mem_directed_edge_set at h
        unfold ContourGraph at h
        simp at h
        let ⟨_, h⟩ := h
        unfold one_common_square at h
        have h₁'' : ¬w.re < z.re := by linarith
        simp [h₁, h₁'', h₂] at h
        let ⟨ha, h⟩ := h

        have hzw : w.im = z.im + δ := by
          rw [norm_def (w - z), normSq_apply, sub_re, h₁'] at ha
          simp at ha
          rw [Real.sqrt_mul_self] at ha
          linarith
          simp [h₂]
          exact LT.lt.le h₂

        have h_sub : {z.re} ×ℂ Icc z.im (z.im + δ) ⊆ (closed_square z δ) := by
          unfold closed_square
          apply reProdIm_subset_iff.mpr
          apply prod_mono_left
          apply Set.singleton_subset_iff.mpr
          simp
          exact LT.lt.le hδ

        have h_sub' : {z.re} ×ℂ Icc (z.im) (z.im + δ) ⊆ (closed_square (z - δ) δ) := by
          unfold closed_square
          simp
          apply reProdIm_subset_iff.mpr
          rw [← hzw]
          apply prod_mono_left
          apply Set.singleton_subset_iff.mpr
          simp
          exact LT.lt.le hδ

        rw [←hzw] at h_sub
        rw [←hzw] at h_sub'

        cases h with
        | inl h =>
          obtain ⟨y, hy⟩ := nonempty_def.mp h.1
          rw [mem_inter_iff] at hy
          use y
          constructor
          · exact hy.2
          · have hx' : x ∈ closed_square z δ := Set.mem_of_subset_of_mem h_sub hx
            exact square_dist hδ hx' hy.1

        | inr h =>
          obtain ⟨y, hy⟩ := nonempty_def.mp h.2
          rw [mem_inter_iff] at hy
          use y
          constructor
          · exact hy.2
          · have hx' : x ∈ closed_square (z - δ) δ := Set.mem_of_subset_of_mem h_sub' hx
            exact square_dist hδ hx' hy.1

      -- ¬z.im < w.im
      · have h₂' : w.im < z.im ∨ w.im = z.im := by
          apply LE.le.lt_or_eq
          apply le_of_not_gt
          linarith

        cases h₂' with

        -- w.im < z.im
        | inl h₂' =>
          -- unfold the GridContour.Adj somewhere here and get cases
          unfold edgeInterval at hx
          have h' : ¬ z.im = w.im := by linarith
          simp [h₁', h₂'] at hx
          rw [min_comm, min_eq_left_of_lt h₂', max_comm, max_eq_right_of_lt h₂'] at hx

          unfold edges at h
          apply mem_directed_edge_set at h
          unfold ContourGraph at h
          simp at h
          let ⟨_, h⟩ := h
          unfold one_common_square at h
          have h₁'' : ¬w.re < z.re := by linarith
          simp [h₁, h₁'', h₂, h₂'] at h
          let ⟨ha, h⟩ := h

          have hzw : z.im = w.im + δ := by
            rw [norm_def (w - z), normSq_apply, sub_re, h₁', sub_self] at ha
            simp at ha
            rw [Real.sqrt_mul_self_eq_abs, abs_eq] at ha
            cases ha
            · linarith
            · linarith
            exact LT.lt.le hδ

          have h_sub : {z.re} ×ℂ Icc (w.im) (w.im + δ) ⊆ (closed_square w δ) := by
            unfold closed_square
            apply reProdIm_subset_iff.mpr
            apply prod_mono_left
            rw [h₁']
            apply Set.singleton_subset_iff.mpr
            simp
            exact LT.lt.le hδ

          have h_sub' : {z.re} ×ℂ Icc (w.im) (w.im + δ) ⊆ (closed_square (w - δ) δ) := by
            unfold closed_square
            simp
            apply reProdIm_subset_iff.mpr
            apply prod_mono_left
            rw [h₁']
            apply Set.singleton_subset_iff.mpr
            simp
            exact LT.lt.le hδ

          rw [←hzw] at h_sub
          rw [←hzw] at h_sub'

          cases h with
          | inl h =>
            obtain ⟨y, hy⟩ := nonempty_def.mp h.1
            rw [mem_inter_iff] at hy
            use y
            constructor
            · exact hy.2
            · have hx' : x ∈ closed_square w δ := Set.mem_of_subset_of_mem h_sub hx
              exact square_dist hδ hx' hy.1

          | inr h =>
            obtain ⟨y, hy⟩ := nonempty_def.mp h.2
            rw [mem_inter_iff] at hy
            use y
            constructor
            · exact hy.2
            · have hx' : x ∈ closed_square (w - δ) δ := Set.mem_of_subset_of_mem h_sub' hx
              exact square_dist hδ hx' hy.1

        -- w.im = z.im
        | inr h₂' =>
          -- Pathology
          exfalso
          unfold edgeInterval at hx
          have h' : w = z:= ext h₁' h₂'

          unfold edges at h
          apply mem_directed_edge_set at h
          unfold ContourGraph at h
          simp at h
          let ⟨h, _⟩ := h
          simp [h'] at h
          linarith

-- CIF_GridContour
lemma DifferentiableOn.grid_contour_integral_sub_inv_smul {Ω K : Set ℂ} {f : ℂ → ℂ}
  (hΩ : IsOpen Ω) (hΩK : K ⊆ Ω) [Gridable K] (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∀ a ∈ K, GridContourIntegral (fun z ↦ (z - a)⁻¹ • f z) K hδ = (2 * π * I) • f a := by sorry


/-- **Separation Lemma**: Given a compact set `K` and a function `f : ℂ → ℂ` that is complex differentiable on
an open set `Ω`, containing `K`, there exists a `δ > 0` such that the integral of `(z - a)⁻¹ • f(z)` over the
grid contour of `K` is equal to `2 * π * I * f(a)`, where `a` is a point in `K` and the grid contour is
contained in `Ω \ K`.
-/
theorem separation_lemma {Ω K : Set ℂ} {f : ℂ → ℂ} (hΩ : IsOpen Ω) (hΩ₁ : Ωᶜ.Nonempty) (hΩK : K ⊆ Ω) [Gridable K]
  (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∃ (δ : ℝ) (hδ : 0 < δ), (∀ a ∈ K, GridContourIntegral (fun z ↦ (z - a)⁻¹ • f z) K hδ = (2 * π * I) • f a) ∧
  (GridContourSet K hδ ⊆ Ω \ K) := by
  have hΩK' : Disjoint K Ωᶜ := disjoint_compl_right_iff_subset.mpr hΩK
  obtain ⟨x₀, hx₀, hKx₀⟩ := point_of_least_sep K Ωᶜ
  let d : ℝ := infDist x₀ Ωᶜ / 2
  have hd : 0 < d := by
    apply half_pos
    rw [← IsClosed.not_mem_iff_infDist_pos (isClosed_compl_iff.mpr hΩ) hΩ₁, not_mem_compl_iff]
    exact mem_of_subset_of_mem hΩK hx₀

  have hΓK : Disjoint K (GridContourSet K hd) := by
        rw [disjoint_iff_inter_eq_empty, inter_comm]
        let ε := 2 * d
        have hε : 0 < ε := by apply mul_pos; linarith; exact hd
        let V := (Mesh (Box K hε) hd).filter (fun v ↦ ((closed_square v d) ∩ K).Nonempty)
        let edges := (DirectedEdgeSetOriented K hd V)
        have h : GridContourSet K hd = ⋃ e ∈ edges, edgeInterval e := by rfl
        rw [h, iUnion_inter K, iUnion_eq_empty]
        intro (z,w)
        rw [iUnion_inter, iUnion_eq_empty]
        have h' {z w : ℂ} (hzw : (z,w) ∈ edges) : edgeInterval (z,w) ∩ K = ∅ := by
          unfold edges at hzw
          apply mem_directed_edge_set at hzw
          simp [ContourGraph] at hzw
          apply (edge_interval_inter_empty K hd hzw.2)
        exact h'

  have hΓδ : ∀ x ∈ (GridContourSet K hd), ∃ y ∈ K, dist x y < infDist x₀ Ωᶜ := by
    have h2d : infDist x₀ Ωᶜ = 2 * d := by unfold d; ring
    rw [h2d]
    exact grid_contour_sep K hd

  use d, hd
  constructor
  -- CIF Statement
  · exact DifferentiableOn.grid_contour_integral_sub_inv_smul hΩ hΩK hf

  -- Contour Set Statement
  · rw [diff_eq, Set.subset_inter_iff, and_comm]
    constructor

    -- Γ ⊆ Kᶜ
    · exact subset_compl_iff_disjoint_left.mpr hΓK

    -- Γ ⊆ Ω
    · rw [Set.subset_def]
      intro x hx
      rw [←compl_compl Ω, Set.mem_compl_iff]
      by_contra h_contra
      obtain ⟨y, hy, hxy⟩ := hΓδ x hx
      have h : infDist x₀ Ωᶜ ≤ dist x y := by
        specialize hKx₀ y hy
        have h : infDist y Ωᶜ ≤ dist y x := infDist_le_dist_of_mem h_contra
        rw [dist_comm] at h
        linarith
      linarith [hxy, h]

-- Two approaches to prove separation theorem
-- TODO: Every connected component of GridContour is a cycle => need this to show that GridContour is a "Path"
-- TODO: Every GridContour is a union of squares => need this for CIF on GridContour

-- TODO : Show that every edge is contained in `Ω` => The argument is that `d(K, Γ)` is less than  `d(K, Ωᶜ)`

-- Needs work!
theorem approximation_lemma {Ω K : Set ℂ} {f : ℂ → ℂ} {δ : ℝ} (hΩ : IsOpen Ω)
  (hΩK : K ⊆ Ω) [Gridable K] (hδ : 0 < δ) (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∃ (R : RatFunc ℂ), (only_poles_in' (GridContourSet K hδ) R) ∧
  (∀ x ∈ K, ‖f x - R.eval (RingHom.id ℂ) x‖ < ε) := by sorry
