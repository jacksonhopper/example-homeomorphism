import mathlib

open Set

-- the homeomorphism between the subtype Ioo (0:ℝ) 1 and ℝ
noncomputable def Ioo_0_1_homeo_real : (Ioo (0:ℝ) 1) ≃ₜ ℝ := by
    -- define to and inv funs
    let to_fun  : (Ioo (0:ℝ) 1) → ℝ := fun x ↦ Real.log (x / (1 - x))
    let logit := fun t : ℝ ↦ 1 / (1 + Real.exp (-t))
    let logit_range : ∀ t : ℝ, logit t ∈ Ioo 0 1 := by
        intro t
        let logit_gt_zero : logit t > 0 := by
            apply div_pos
            · norm_num
            · linarith [Real.exp_pos (-t)]
        let logit_lt_one : logit t < 1 := by
            rw [div_lt_one (by linarith [Real.exp_pos (-t)])]
            linarith [Real.exp_pos (-t)]
        simp only [mem_Ioo]
        exact And.intro logit_gt_zero logit_lt_one
    let inv_fun : ℝ → (Ioo (0:ℝ) 1) := fun t ↦ ⟨ logit t,
        logit_range t ⟩
    -- prove functions are continuous
    let cts_to_fun : Continuous to_fun := by
        change Continuous (fun x : Ioo (0:ℝ) 1 ↦ Real.log (x.1 / (1 - x.1)))
        apply Continuous.log
        · -- Continuous fun x : Ioo 0 1 ↦ x / (1 - x)
            apply Continuous.div
            · exact continuous_subtype_val
            · -- Continuous fun x ↦ 1 - x
                apply Continuous.sub
                · exact continuous_const
                · exact continuous_subtype_val
            · -- ∀ x : Ioo 0 1, 1 - x ≠ 0
                intro x
                let one_sub_x_gt_0 : 1 - x > (0:ℝ) := by
                    let x_lt_one : x < (1:ℝ) := by exact x.2.2 -- x < 1
                    linarith [x_lt_one]
                apply ne_of_gt one_sub_x_gt_0
        · -- for x : Ioo 0 1, x / (1 - x) > 0
            intro x
            apply ne_of_gt
            apply div_pos
            · exact x.2.1 -- 0 < x
            · linarith [x.2.2] -- 0 < 1 - x
    let cts_inv_fun : Continuous inv_fun := by
        refine Continuous.subtype_mk ?_ logit_range
        apply Continuous.div
        · exact continuous_const
        · -- Continuous t ↦ 1 + Real.exp(-t)
            apply Continuous.add
            · exact continuous_const
            · -- Continous t ↦ Real.exp(-t)
                apply Continuous.rexp
                exact continuous_neg
        · -- ∀ x, 1 + Real.exp(-x) ≠ 0
            intro x
            apply ne_of_gt
            apply add_pos
            · norm_num
            · exact Real.exp_pos (-x)
    -- prove functions are inverse (2 directions)
    let left_inv : Function.LeftInverse inv_fun to_fun := by
        intro ⟨ x, hx0, hx1 ⟩
        simp only [inv_fun, to_fun, logit]
        ext
        simp only [one_div]
        rw [Real.exp_neg, Real.exp_log (div_pos hx0 (by linarith))]
        field_simp
        linarith
    let right_inv : Function.RightInverse inv_fun to_fun := by
        intro x
        simp only [to_fun, inv_fun, logit]
        rw [Real.log_div]
        · -- Real.log (1 / (1 + Real.exp (-x))) - Real.log (1 - 1 / (1 + Real.exp (-x))) = x
            rw[Real.log_div]
            · -- log 1 - log (1 + exp (-x)) - log (1 - 1 / (1 + exp (-x))) = x
                simp only [Real.log_one, zero_sub, one_div]
                let h : 1 - (1 + Real.exp (-x))⁻¹ = Real.exp (-x) / (1 + Real.exp (-x)) := by
                    have hd : 1 + Real.exp (-x) ≠ 0 := by
                        apply ne_of_gt
                        linarith [Real.exp_pos (-x)]
                    field_simp
                    ring
                rw [h]
                rw [Real.log_div (Real.exp_pos (-x)).ne']
                · -- -log (1 + exp (-x)) - (log (exp (-x)) - log (1 + exp (-x))) = x
                    rw [Real.log_exp]
                    ring
                · -- 1 + Real.exp (-x) ≠ 0
                    apply ne_of_gt
                    linarith [Real.exp_pos (-x)]
            · norm_num
            · -- 1 + Real.exp (-x) ≠ 0
                apply ne_of_gt
                linarith [Real.exp_pos (-x)]
        · -- 1 / (1 + Real.exp (-x)) ≠ 0
            apply ne_of_gt
            apply div_pos
            · norm_num
            · linarith[Real.exp_pos (-x)]
        · -- 1 - 1 / (1 + Real.exp (-x)) ≠ 0
            rw [sub_ne_zero, ne_comm]
            apply ne_of_lt
            rw [div_lt_one (by linarith [Real.exp_pos (-x)])]
            linarith [Real.exp_pos (-x)]
    -- gather definitions and close proof
    exact
    {   toFun := to_fun,
        invFun := inv_fun,
        left_inv := left_inv,
        right_inv := right_inv}

theorem fact_that_Ioo_0_1_homeo_real : Nonempty (↥(Ioo (0 : ℝ) 1) ≃ₜ ℝ) :=
    ⟨ Ioo_0_1_homeo_real ⟩
