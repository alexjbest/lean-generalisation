import measure_theory.interval_integral

open set

noncomputable def f (x : ℝ) := if x ≤ 1/37 then 37 else 0
open_locale classical
noncomputable def a : ℝ := ∫ x in 0..1, f x
open interval_integral measure_theory
example : a = 1 := begin
  simp only [a, f, one_div, nat.cast_bit0, nat.cast_zero, nat.cast_bit1, nat.cast_one, nat.cast_ite],
  have meas : measurable (λ (a : ℝ), ite (a ≤ 37⁻¹) (37 : ℝ) 0) :=
  begin
    apply measurable.ite,
    exact is_measurable_Iic,
    exact measurable_const,
    exact measurable_const,
  end,
  rw ← integral_add_adjacent_intervals,
  work_on_goal 3 {exact 1/37,},
  have : (1 : ℝ) + 0 = 1 := by simp,
  convert this; rw integral_of_le,
  all_goals {try {linarith}},
  { have : measurable (λ a : ℝ, (37:ℝ)) := measurable_const,
    rw integral_congr_ae _ this,
    simp only [measure_theory.integral_const, one_div, algebra.id.smul_eq_mul, sub_zero, real.volume_Ioc, measure.restrict_apply, univ_inter,
  is_measurable.univ],
    norm_num,
    simp only [one_div, is_measurable_Ioc, ae_restrict_eq],
    refine eq_on.eventually_eq_of_mem _ _,
    exact Ioc 0 37⁻¹,
    intros x hx,
    simp only,
    rw if_pos,
    exact (mem_Ioc.mp hx).2,
    apply filter.mem_inf_sets_of_right,
    exact filter.mem_principal_self (Ioc 0 37⁻¹),
    dsimp,
    sorry,
     },
  { have : measurable (λ a : ℝ, (0:ℝ)) := measurable_const,
    rw integral_congr_ae _ this,
    simp only [measure_theory.integral_const, algebra.id.smul_eq_mul, mul_zero],
    norm_num,
    simp only [one_div],
    refine eq_on.eventually_eq_of_mem _ _,
    exact Ioc 37⁻¹ 1,
    intros x hx,
    simp only,
    rw if_neg,
    push_neg,
    exact (mem_Ioc.mp hx).1,
    apply filter.mem_inf_sets_of_right,
    exact filter.mem_principal_self _,
    exact meas,
   },
    all_goals{ apply measure_theory.integrable.interval_integrable,},
  end
