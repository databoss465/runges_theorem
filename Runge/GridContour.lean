import Mathlib

open Complex Set Finset

-- A square in the complex plane
structure complex_square where
  btm_left : ℂ    -- Bottom left corner
  side : ℝ        -- Side length
  h₁ : side > 0

def unit_square : complex_square := ⟨0, 1, by linarith⟩
#check unit_square

-- The vertices of a complex square listed in a counter-clockwise order
def complex_sq_vertices (s: complex_square) : List ℂ :=
  [s.btm_left,
    s.btm_left + s.side,
    s.btm_left + s.side + s.side * I,
    s.btm_left + s.side * I]

#eval complex_sq_vertices unit_square   --Essentially [0, 1, 1 + i, i] but it doesn't look like that

def complex_sq_as_set (s: complex_square) : Set ℂ :=
  Ico s.btm_left.re (s.btm_left.re + s.side) ×ℂ Ico s.btm_left.im (s.btm_left.im + s.side)

def complex_sq_interior (s: complex_square) : Set ℂ :=
  let z := s.btm_left
  let w := s.btm_left + s.side * (1 + I) -- Top-right corner
 (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ Set.Ioo (min z.im w.im) (max z.im w.im))

def complex_sq_closure (s: complex_square) : Set ℂ :=
  let z := s.btm_left
  let w := s.btm_left + s.side * (1 + I) -- Top-right corner
  uIcc z.re w.re ×ℂ uIcc z.im w.im

-- Integral of a function over a complex square
noncomputable def complex_sq_boundary_integral {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (s : complex_square) : E :=
  let z := s.btm_left
  let w := s.btm_left + s.side * (1 + I) -- Top-right corner
  (((∫ (x : ℝ) in z.re..w.re, f (↑x + ↑z.im * Complex.I)) - ∫ (x : ℝ) in
  z.re..w.re, f (↑x + ↑w.im * Complex.I)) + Complex.I • ∫ (y : ℝ) in z.im..w.im, f
  (↑w.re + ↑y * Complex.I)) - Complex.I • ∫ (y : ℝ) in z.im..w.im, f (↑z.re + ↑y * Complex.I)

noncomputable def complex_sq_boundary_integral' {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (s : complex_square) : E :=
  let vs := complex_sq_vertices s
  have h₁ : vs.length = 4 := by rfl
  (∫ x in vs[0].re..vs[1].re, f (x + vs[0].im * I)) - (∫ x in vs[3].re..vs[2].re, f (x + vs[2].im * I)) +
  I • ((∫ y in vs[1].im..vs[2].im, f (vs[1].re + y * I)) - (∫ y in vs[0].im..vs[3].im, f (vs[3].re + y * I)))

theorem complex_sq_boundary_integral_eq_zero {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (s : complex_square) (hC : ContinuousOn f (complex_sq_closure s))
    (hD : DifferentiableOn ℂ f (complex_sq_interior s)) :
    complex_sq_boundary_integral f s = 0 := by
    let z := s.btm_left
    let w := s.btm_left + s.side * (1 + I) -- Top-right corner
    apply Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    exact hC
    exact hD

-- TODO: CIF for the complex square (after proven for the rectangle)

-- Grid contour
structure Grid where
  squares : Finset ℂ    -- Bottom left corners of the squares
  vertices : List ℂ     -- ccw Vertex list of total contour
  side : ℝ              -- Side length of the squares
  h₁ : side > 0
  h₂ : squares.Nonempty

-- TODO: function to add squares and update vertex list

--TODO: Define Grid Contour as an Inductive Type (maybe inductive type is better?)
--TODO: Recursive(?) Vertex Updating algorithm
