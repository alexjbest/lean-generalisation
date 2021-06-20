import generalisation_linter

lemma good (G : Type*) [group G] (n : ℤ) (g : G) (h : g^(-n) = 1) : g^n = 1 :=
begin
  rw [gpow_neg, inv_eq_one] at h,
  exact h,
end

open expr tactic
set_option trace.generalising true
set_option profiler true
run_cmd  (
do c ← get_env,
  class_dag c >>= (λ d, trace $ d.meet (
[⟨ `has_inv, [var 0]⟩, ⟨`has_one , [var 0]⟩, ⟨`group, [var 0]⟩, ⟨`has_pow, [var 0, `(int)]⟩] )))
run_cmd  (
do c ← get_env,
  class_dag c >>= (λ d, trace $ d.meet (
[⟨ `linear_ordered_semiring, [var 0]⟩, ⟨`nontrivial, [var 0]⟩] )))


#lint only generalisation_linter
