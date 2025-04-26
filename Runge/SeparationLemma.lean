import Mathlib
import Runge.Basic
import Runge.GridContour

/-!
# Separation Lemma (WIP)

This file contains the proof of the **Separation Lemma**, which is a key result in complex analysis.
The lemma establishes that for a compact set `K` in the complex plane and a function `f` that is
complex differentiable on an open set `Ω` containing `K`, there exists a positive resolution `δ`
such that the integral of `(z - a)⁻¹ * f(z)` over the grid contour of `K` equals `2 * Real.pi * I * f(a)`
for any point `a ∈ K`. Additionally, the grid contour is contained in the complement of `K` within `Ω`.

## Main Results

- `point_of_least_sep`: A compact set `K` has a point of minimal distance to any other set `U`.
- `square_dist`: If `x` and `y` are elements of a closed square, their distance is bounded by `2 * δ`.
- `grid_contour_sep`: For every point on the grid contour boundary, there exists a point in `K`
  such that their distance is less than `2 * δ`.
- `gc_integral_eq_sum_sq_integral`: The integral over the grid contour is the sum of integrals
  over individual squares.
- `DifferentiableOn.grid_contour_integral_sub_inv_smul`: Cauchy's integral formula for a grid contour.
- `separation_lemma`: The main theorem, which proves the Separation Lemma.

## Notation

- `GridContourBoundary`: The boundary of the grid contour.
- `GridContourIntegral`: The integral of a function over the grid contour.
- `closed_square` and `open_square`: Definitions of closed and open squares in the complex plane.
-/

open Complex Set Finset Metric RatFunc Real

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


-- For every `x` in the `GridContourBoundary K hδ`, there exists a `y` in `K` such that dist x y < `2 * δ`
lemma grid_contour_sep (K : Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) :
  ∀ x ∈ (GridContourBoundary K hδ), ∃ y ∈ K, dist x y < 2 * δ := by

  let ε := 2 * δ
  have hε : 0 < ε := by apply mul_pos; linarith; exact hδ
  let V := (Mesh hδ (Box K hε)).filter (fun v ↦ ((closed_square v δ) ∩ K).Nonempty)
  let edges := (DirectedEdgeSetOriented K hδ V)
  have h : GridContourBoundary K hδ = ⋃ e ∈ edges, edgeInterval e := by rfl

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
      · unfold edgeInterval at hx
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
      · unfold edgeInterval at hx
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

-- Integral over the grid contour is the sum integral of individual squares!
lemma gc_integral_eq_sum_sq_integral {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (K: Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) :
    GridContourIntegral K hδ f  = ∑ z ∈ GridContourCollection K hδ, (square_integral f z hδ ):= by

    -- *get help*
    sorry

-- Cauchy's Integral Formula for a square
lemma DifferentiableOn.square_integral_sub_inv_smul {v : ℂ} {δ : ℝ} (hδ : 0 < δ)
  {f : ℂ → ℂ} (hf : ∀ x ∈ closed_square v δ, DifferentiableAt ℂ f x) :
  ∀ a ∈ open_square v δ, square_integral (fun z ↦ (z - a)⁻¹ * f z) v hδ = (2 * Real.pi * I) * f a := by

  -- Done in PNT+, PR in mathlib
  sorry

lemma DifferentiableOn.square_integral_eq_zero {v : ℂ} {δ : ℝ} (hδ : 0 < δ)
  {f : ℂ → ℂ} (hf : ∀ x ∈ closed_square v δ, DifferentiableAt ℂ f x) :
  ∀ a ∉ closed_square v δ, square_integral (fun z ↦ (z - a)⁻¹ * f z) v hδ = 0 := by

  -- Look this up, low priority
  sorry

#check Finset.sum_eq_single

-- Cauchy's Integral Formula for a Grid Contour
lemma DifferentiableOn.grid_contour_integral_sub_inv_smul {Ω K : Set ℂ} {f : ℂ → ℂ} {δ : ℝ}
  (hδ : 0 < δ) (hΩ : IsOpen Ω) (hΩK : K ⊆ Ω) [Gridable K] (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∀ a ∈ K, GridContourIntegral K hδ (fun x ↦ (x - a)⁻¹ * f x) = (2 * Real.pi * I) * f a := by
    intro a ha
    apply mem_of_subset_of_mem (subset_grid_contour_area K hδ) at ha
    let ε := 2 * δ
    have hε : 0 < ε := by apply mul_pos; linarith; exact hδ
    let V := (Mesh hδ (Box K hε)).filter (fun v ↦ ((closed_square v δ) ∩ K).Nonempty)
    have h : GridContourArea K hδ = ⋃ v ∈ V, closed_square v δ := by rfl
    rw [h, mem_iUnion] at ha
    obtain ⟨w, hw⟩ := ha
    simp at hw
    let ⟨hv, hw⟩ := hw
    rw [←diff_union_of_subset (open_sq_subset_closed_sq w hδ), union_comm] at hw
    apply mem_or_mem_of_mem_union at hw
    cases hw with

    -- When a is in the interior of any square
    | inl hw =>
      -- make a `lemma` for this as well
      -- State the lemma as need, consider an iff statement
      have hw' : ∀ v' ∈ V, v' ≠ w → a ∉ closed_square v' δ := by sorry
      have h' : GridContourCollection K hδ = V := by rfl
      let F (z : ℂ) := if z = w then (2 * Real.pi * I) * f a else 0

      have h₁ : ∀ v ∈ V, ∀ x ∈ closed_square v δ, DifferentiableAt ℂ f x := by
        intro v hv x hx
        -- make a `lemma` for this in GridContour
        -- ∀ v ∈ Mesh, closed_square v δ ⊆ Ω
        have h₂' : closed_square v δ ⊆ Ω := by sorry
        apply hf
        exact mem_of_subset_of_mem h₂' hx

      have h' : GridContourCollection K hδ = V := by rfl
      have h'': square_integral (fun x ↦ (x - a)⁻¹ * f x) w hδ = (2 * Real.pi * I) * f a := by
        apply DifferentiableOn.square_integral_sub_inv_smul hδ (h₁ w hv) a
        exact hw

      rw [gc_integral_eq_sum_sq_integral, h', ← h'']
      apply Finset.sum_eq_single_of_mem
      · exact hv
      · intro v' hv' hv''
        apply DifferentiableOn.square_integral_eq_zero hδ (h₁ v' hv') a
        exact hw' v' hv' hv''

    -- When a is on the boundary of any square
    | inr hw =>
      -- *GET HELP*
      sorry

lemma DifferentiableOn.inv_two_pi_grid_contour_integral {Ω K : Set ℂ} {f : ℂ → ℂ} {δ : ℝ}
  (hδ : 0 < δ) (hΩ : IsOpen Ω) (hΩK : K ⊆ Ω) [Gridable K] (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∀ a ∈ K, (2 * Real.pi * I)⁻¹ * GridContourIntegral K hδ (fun x ↦ (x - a)⁻¹ * f x) =  f a := by
  intro a ha
  have :  GridContourIntegral K hδ (fun x ↦ (x - a)⁻¹ * f x) = (2 * Real.pi * I) * f a := DifferentiableOn.grid_contour_integral_sub_inv_smul _ hΩ hΩK hf a ha
  rw [this, ← mul_assoc]
  simp only [mul_inv_rev, inv_I, neg_mul]
  ring
  simp only [I_sq, neg_mul, one_mul, neg_neg]
  rw [Complex.mul_inv_cancel]
  simp
  rw [Complex.ofReal_ne_zero]
  exact Real.pi_ne_zero


/-- **Separation Lemma**: Given a compact set `K` and a function `f : ℂ → ℂ` that is complex differentiable on
an open set `Ω`, containing `K`, there exists a `δ > 0` such that the integral of `(z - a)⁻¹ * f(z)` over the
grid contour of `K` is equal to `2 * Real.pi * I * f(a)`, where `a` is a point in `K` and the grid contour is
contained in `Ω \ K`.
-/
theorem separation_lemma {Ω K : Set ℂ} {f : ℂ → ℂ} (hΩ : IsOpen Ω) (hΩ₁ : Ωᶜ.Nonempty) (hΩK : K ⊆ Ω) [Gridable K]
  (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∃ (δ : ℝ) (hδ : 0 < δ), (∀ a ∈ K, GridContourIntegral K hδ (fun z ↦ (z - a)⁻¹ * f z)  = (2 * Real.pi * I) * f a) ∧
  (GridContourBoundary K hδ ⊆ Ω \ K) := by
  have hΩK' : Disjoint K Ωᶜ := disjoint_compl_right_iff_subset.mpr hΩK
  obtain ⟨x₀, hx₀, hKx₀⟩ := point_of_least_sep K Ωᶜ
  let d : ℝ := infDist x₀ Ωᶜ / 2
  have hd : 0 < d := by
    apply half_pos
    rw [← IsClosed.not_mem_iff_infDist_pos (isClosed_compl_iff.mpr hΩ) hΩ₁, not_mem_compl_iff]
    exact mem_of_subset_of_mem hΩK hx₀

  have hΓK : Disjoint K (GridContourBoundary K hd) := by
        rw [disjoint_iff_inter_eq_empty, inter_comm]
        let ε := 2 * d
        have hε : 0 < ε := by apply mul_pos; linarith; exact hd
        let V := (Mesh hd (Box K hε)).filter (fun v ↦ ((closed_square v d) ∩ K).Nonempty)
        let edges := (DirectedEdgeSetOriented K hd V)
        have h : GridContourBoundary K hd = ⋃ e ∈ edges, edgeInterval e := by rfl
        rw [h, iUnion_inter K, iUnion_eq_empty]
        intro (z,w)
        rw [iUnion_inter, iUnion_eq_empty]
        have h' {z w : ℂ} (hzw : (z,w) ∈ edges) : edgeInterval (z,w) ∩ K = ∅ := by
          unfold edges at hzw
          apply mem_directed_edge_set at hzw
          simp [ContourGraph] at hzw
          apply (edge_interval_inter_empty K hd hzw.2)
        exact h'

  have hΓδ : ∀ x ∈ (GridContourBoundary K hd), ∃ y ∈ K, dist x y < infDist x₀ Ωᶜ := by
    have h2d : infDist x₀ Ωᶜ = 2 * d := by unfold d; ring
    rw [h2d]
    exact grid_contour_sep K hd

  use d, hd
  constructor
  -- Cauchy's Integral Formula Statement
  · exact DifferentiableOn.grid_contour_integral_sub_inv_smul hd hΩ hΩK hf

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
