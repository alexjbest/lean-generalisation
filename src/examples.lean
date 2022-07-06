import generalisation_linter
import algebra.associated
import algebra.char_p
import topology.metric_space.basic
import algebra.ring
import algebra.category.Group
import algebra.group_power
import algebra.algebra.basic

#print  is_unit_iff_dvd_one

lemma atest (α : Type*) [comm_monoid α] : (1 : α) * 1 = 1 ∧ ∀ a b : α, a * b = b * a := ⟨mul_one _, mul_comm⟩
-- lemma atest' (α : Type*) [comm_semigroup α] [monoid α] : (1 : α) * 1 = 1 ∧ ∀ a b : α, a * b = b * a := ⟨mul_one _, mul_comm⟩
lemma btest (α : Type*) [ordered_ring α] (a b : α) : 0 ≤ 0 ∧ a * b + b = a * b + b := ⟨eq.le rfl, rfl⟩
lemma btest' (α : Type*) [ring α] [preorder α] (a b : α) : 0 ≤ 0 ∧ a * b + b = a * b + b := ⟨eq.le rfl, rfl⟩
variables (α : Type*)
#print atest
#print char_p.char_is_prime_of_two_le -- _inst_1: integral_domain ↝ no_zero_divisors semiring
-- should be domain?
#check preorder




-- #print eval
-- run_cmd do d ← get_decl `eval,
--   cd ← dag_attr.get_cache,
--   e ← get_env,
--   trace $ find_gens' d cd e d.type d.value 0 "",
--   return ()





-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `mem_orbit_self,trace l.value.binding_body.binding_body.binding_body.binding_body
-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `mem_orbit_self, aa ← get_instance_chains `mul_action 0 l.value.binding_body.binding_body.binding_body.binding_body , trace $ cd.minimal_vertices aa --.lambda_body.app_fn.app_fn.app_arg.lambda_body.app_fn.app_arg.app_fn.lambda_body--find_gens' cd e l.type l.value 0 ""

-- run_cmd do e ← get_env,
-- cd ← class_dag e,
-- l← e.get `algebra.of_semimodule',
-- trace $ l.value.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.app_fn.app_fn.app_fn.app_arg.app_arg,
-- -- aa ← is_instance_chain 2 l.value.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.app_fn.app_fn.app_fn.app_arg.app_arg,
-- -- trace aa
-- aa ← get_instance_chains `semimodule 2 l.value.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.app_fn.app_fn.app_fn.app_arg.app_arg,
-- trace aa,
-- trace $ cd.minimal_vertices aa --.lambda_body.app_fn.app_fn.app_arg.lambda_body.app_fn.app_arg.app_fn.lambda_body--find_gens' cd e l.type l.value 0 ""
