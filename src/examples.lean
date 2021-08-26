import generalisation_linter
import algebra.associated
import algebra.char_p
import topology.metric_space.basic
import algebra.ring
import algebra.category.Group
import algebra.group_power
import algebra.algebra.basic

set_option pp.all false
#print  is_unit_iff_dvd_one

lemma atest (α : Type*) [comm_monoid α] : (1 : α) * 1 = 1 ∧ ∀ a b : α, a * b = b * a := ⟨mul_one _, mul_comm⟩
-- lemma atest' (α : Type*) [comm_semigroup α] [monoid α] : (1 : α) * 1 = 1 ∧ ∀ a b : α, a * b = b * a := ⟨mul_one _, mul_comm⟩
lemma btest (α : Type*) [ordered_ring α] (a b : α) : 0 ≤ 0 ∧ a * b + b = a * b + b := ⟨eq.le rfl, rfl⟩
lemma btest' (α : Type*) [ring α] [preorder α] (a b : α) : 0 ≤ 0 ∧ a * b + b = a * b + b := ⟨eq.le rfl, rfl⟩
variables (α : Type*)
#print  atest
#print char_p.char_is_prime_of_two_le -- _inst_1: integral_domain ↝ no_zero_divisors semiring
-- should be domain?
#check preorder



--- only needs semiring and has neg doesn't matter what negative ints do.
theorem exists_int_gt' [linear_ordered_ring α] [archimedean α] (x : α) : ∃ n : ℤ, x < n :=
let ⟨n, h⟩ := exists_nat_gt x in ⟨n, by rwa ← coe_coe⟩


@[simp] lemma mul_le_mul_right_of_neg' [linear_ordered_ring α] {a b c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
⟨le_imp_le_of_lt_imp_lt $ λ h', mul_lt_mul_of_neg_right h' h,
  λ h', mul_le_mul_of_nonpos_right h' h.le⟩

section examples
section
  lemma good (G : Type*) [group G] (n : ℤ) (g : G) (h : g^(-n) = 1) : g^n = 1 :=
  begin
    rw [gpow_neg, inv_eq_one] at h,
    exact h,
  end

  lemma good2 (G : Type*) [add_monoid G] (n : ℕ) (g : G) (h : n •  g = 0) : (2*n)•  g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- monoid?
  lemma bad (G : Type*) [group G] (n : ℕ) (g : G) (h : g^n = 1) : g^(2*n) = 1 :=
  by rw [pow_mul', h, one_pow]

  -- harder example as we have a diamond ?
  -- #check ring.to_distrib
  -- #check ring.to_semiring
  -- add_monoid
  lemma bad2diamond (G : Type*) [ring G] (n : ℕ) (g : G) (h : n •  g = 0) : (2*n)•  g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- statement generalises but proof does not!! this one is hard then
  -- add_monoid linter only finds semiring
  lemma bad3pfbad (G : Type*) [ring G] (n : ℕ) (g : G) (h : n •  g = 0) : (2*n)•  g = 0 :=
  by simp only [nsmul_eq_mul] at h; simp only [nat.cast_bit0, nsmul_eq_mul, nat.cast_one, nat.cast_mul]; assoc_rewrite h; exact mul_zero 2
  set_option pp.all true
  lemma bad3pfbad' (G : Type*) [ring G] (n : ℕ) (g : G) (h : n • g = 0) : (2*n)• g = 0 :=
  by {rw [nsmul_eq_mul] at ⊢ h,  rw [nat.cast_mul, mul_assoc, h], exact mul_zero _}
set_option pp.max_steps 30000
set_option pp.max_depth 30000
set_option pp.goal.max_hypotheses 10000
-- #print nat.cast_coe
-- #print bad3pfbad'
set_option trace.generalising false
-- run_cmd do d ← get_decl `bad3pfbad',
--   cd ← dag_attr.get_cache,
--   e ← get_env,
--   trace $ find_gens' d cd e d.type d.value 0 "",
--   return ()

  -- add_monoid
  lemma bad4 (G : Type*) [add_comm_group G] (n : ℕ) (g : G) (h : n • g = 0) : (2*n)• g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- add_monoid
  lemma bad5 (G : Type*) [add_group G] (n : ℕ) (g : G) (h : n • g = 0) : (2*n)• g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- this works without the second stage checking the body, but it has a diamond if we include the type
  -- add_comm_semigroup
  lemma bad6 (G : Type*) [add_comm_group G] (g h : G) : g + h = h + g := add_comm _ _
  -- add_comm_semigroup
  lemma bad8 (G H : Type*) [add_comm_group G] (g h : G) : g + h = h + g := add_comm _ _

  -- TODO looks like some instance missed here with original version? possibly in the pi binder
  -- add_comm_semigroup
  lemma bad7pibinder (G : Type*) [add_comm_group G] (g h : G) : g + h = h + g ∧ ∀ g2, g2 + g = g + g2 :=
  ⟨add_comm _ _,assume g2, add_comm _ _ ⟩
  -- challenging example this is a projection but not an instance
  lemma bad10 (G H : Type*) [has_mul G] [has_mul H] [fintype G] [fintype H] (h : G ≃* H) :
  fintype.card G = fintype.card H := fintype.card_congr h.to_equiv
  -- multiple tings
  -- monoid H, fintypes not needed
  lemma bad9 (G H : Type*) [monoid G] [group H] [fintype G] [fintype H] : (1^2 : G) = 1 ∧ (1^2 : H) = 1 :=
  ⟨one_pow 2, one_pow 2⟩

  -- group
  lemma bad11 (G : Type*) [comm_group G] (n : ℤ) (g : G) (h : g^(-n) = 1) : g^n = 1 :=
  begin
    rw [gpow_neg, inv_eq_one] at h,
    exact h,
  end
  -- set_option old_structure_cmd true
-- @[protect_proj] class linear_ordered_field' (α : Type*) extends linear_ordered_comm_ring α, field α
  lemma bun (G: Group) (g :G) : g^2*g^2 = g^4 :=
  begin
    group,
  end
def eval {M N: Type*} [monoid M] [comm_monoid N] : M →* (M →* N) →* N := (monoid_hom.id (M →* N)).flip

-- #print eval
set_option trace.generalising false
-- run_cmd do d ← get_decl `eval,
--   cd ← dag_attr.get_cache,
--   e ← get_env,
--   trace $ find_gens' d cd e d.type d.value 0 "",
--   return ()
section
-- TODO
-- has_pow int and nat are different!
-- solutions: add to dag separately? or treat the instance chain as shorter
local attribute [semireducible] int.nonneg
lemma one_lt_fpow' {K}  [linear_ordered_field K] {p : K} (hp : 1 < p) :
  ∀ z : ℤ, 0 < z → 1 < p ^ z
| (n : ℕ) h := by { rw [gpow_coe_nat],
    exact one_lt_pow hp (nat.succ_le_of_lt (int.lt_of_coe_nat_lt_coe_nat h)) }
#print one_lt_fpow'
#check expr.alpha_eqv
set_option trace.generalising false
open tactic
run_cmd do d ← get_decl `one_lt_fpow',
  cd ← dag_attr.get_cache,
  e ← get_env,
  -- trace $ find_gens' d cd e d.type d.value 0 "",
  d.type.mfold () (λ e n _, do --trace (e.instantiate_nth_var 4 ((expr.var 0))),
                              trace (e.instantiate_vars (list.repeat (expr.var 0) e.get_free_var_range)), return ()),
  return ()
#eval tactic.trace `(∀ l m t: ℕ, (l < t → l < t)).pi_binders
#check (`(∀ l m t: ℕ, (l < t → 0 < t)) : expr).match_pi
set_option pp.all false
run_cmd (do
  let body :=  (`(∀ m t: ℕ, (t + m > 0)):expr).pi_binders.2,
  tactic.trace body,
  tactic.trace $ body.replace (λ e n, match e with
  | expr.var n := some (expr.var 0)
  | e := none
  end),
  return () )
  end

open equiv.set equiv sum nat function set subtype

@[simp] lemma sum_diff_subset_apply_inr'
  {α} {s t : set α} (h : s ⊆ t) [decidable_pred (∈ s)] (x : t \ s) :
  equiv.set.sum_diff_subset h (sum.inr x) = inclusion (diff_subset t s) x := rfl
  set_option pp.all false
  -- #check equiv.set.sum_diff_subset
  set_option pp.all true
  -- #print sum_diff_subset_apply_inr'

lemma supr_apply' {α : Type*} {β : α → Type*} {ι : Sort*} [Π i, has_Sup (β i)] {f : ι → Πa, β a}
  {a : α} :
  (⨆i, f i) a = (⨆i, f i a) :=
@infi_apply α (λ i, order_dual (β i)) _ _ f a



variables {β γ :Type} {ι : Sort} {s : set α}
--none
theorem exists_nat_ge' [linear_ordered_semiring α] [archimedean α] (x : α) :
  ∃ n : ℕ, x ≤ n :=
(exists_nat_gt x).imp $ λ n, le_of_lt

theorem finset_le {r : α → α → Prop} [is_trans α r]
  {ι} [hι : nonempty ι] {f : ι → α} (D : directed r f) (s : finset ι) :
  ∃ z, ∀ i ∈ s, r (f i) (f z) :=
show ∃ z, ∀ i ∈ s.1, r (f i) (f z), from
multiset.induction_on s.1 (let ⟨z⟩ := hι in ⟨z, λ _, false.elim⟩) $
λ i s ⟨j, H⟩, let ⟨k, h₁, h₂⟩ := D i j in
⟨k, λ a h, or.cases_on (multiset.mem_cons.1 h)
  (λ h, h.symm ▸ h₁)
  (λ h, trans (H _ h) h₂)⟩

lemma finite.bdd_below_bUnion [semilattice_inf α] [nonempty α] {I : set β} {S : β → set α} (H : finite I) :
  (bdd_below (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_below (S i)) :=
@finite.bdd_above_bUnion (order_dual α) _ _ _ _ _ H


open filter
variables  {ι' : Type }
lemma unbounded_of_tendsto_at_top' [nonempty α] [semilattice_inf α] [preorder β] [no_top_order β]
  {f : α → β} (h : tendsto f at_bot at_top) :
  ¬ bdd_above (range f) :=
@unbounded_of_tendsto_at_top (order_dual α) _ _ _ _ _ _ h

-- it looks like we only need has_pow here as has_pow is all that appears in the proof
-- however to_monoid and to_inv also appear in the statement, so should not show up
-- theorem gpow_neg_succ_of_nat' {G : Type } [group G] (a : G) (n : ℕ) : a ^ -[1+n] = (a ^ n.succ)⁻¹ := rfl
-- #printgpow_neg_succ_of_nat

-- #print sum_diff_subset_apply_inr'

-- lemma char_p_iff_char_p' {K L : Type*} [division_ring K] [semiring L] [nontrivial L] (f : K →+* L) (p : ℕ) :

lemma ring_hom.char_p_iff_char_p' {K L : Type*} [field K] [field L] (f : K →+* L) (p : ℕ) :
  char_p K p ↔ char_p L p :=
begin
  split;
  { introI _c, constructor, intro n,
    rw [← @char_p.cast_eq_zero_iff _ _ _ p _c n, ← f.injective.eq_iff, f.map_nat_cast, f.map_zero] }
end
open nat subtype multiset

lemma piecewise_piecewise_of_subset_left' {δ : α → Sort*} (s : finset α) (g f : Π (i : α), δ i) [Π (j : α), decidable (j ∈ s)] {s t : finset α} [Π i, decidable (i ∈ s)]
  [Π i, decidable (i ∈ t)] (h : s ⊆ t) (f₁ f₂ g : Π a, δ a) :
  s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
s.piecewise_congr (λ i hi, finset.piecewise_eq_of_mem _ _ _ (h hi)) (λ _ _, rfl)
-- #check       piecewise_piecewise_of_subset_left'

lemma sub_le_of_abs_sub_le_left' {c b a : α} [linear_ordered_ring α] (h : abs (a - b) ≤ c) : b - c ≤ a :=
_root_.sub_le.1 $ (abs_sub_le_iff.1 h).2

lemma inf_ind' [semilattice_inf α] [is_total α (≤)] (a b : α) {p : α → Prop} (ha : p a) (hb : p b) : p (a ⊓ b) :=
@sup_ind (order_dual α) _ _ _ _ _ ha hb
-- #print inf_ind --TODO why is inst_2 removed

open_locale filter
lemma map_at_bot_eq [nonempty α] [semilattice_inf α] {f : α → β} :
  at_bot.map f = (⨅a, 𝓟 $ f '' {a' | a' ≤ a}) :=
@map_at_top_eq (order_dual α) _ _ _ _
#print map_at_bot_eq
open_locale big_operators
lemma abs_sum_le_sum_abs [linear_ordered_field α] {f : β → α} {s : finset β} :
  abs (∑ x in s, f x) ≤ ∑ x in s, abs (f x) :=
finset.le_sum_of_subadditive _ abs_zero abs_add s f

universes u v w
set_option pp.all true
lemma mem_orbit_self
{α : Type u} {β : Type v} [monoid α] [mul_action α β]
(b : β) : b ∈ mul_action.orbit α b :=
⟨1, mul_action.one_smul _⟩
--     #print mem_orbit_self
-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `mem_orbit_self,trace l.value.binding_body.binding_body.binding_body.binding_body
-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `mem_orbit_self, aa ← get_instance_chains `mul_action 0 l.value.binding_body.binding_body.binding_body.binding_body , trace $ cd.minimal_vertices aa --.lambda_body.app_fn.app_fn.app_arg.lambda_body.app_fn.app_arg.app_fn.lambda_body--find_gens' cd e l.type l.value 0 ""
  #print euclidean_domain.gcd

  #print algebra.of_module  --TODO
#print distrib.to_has_mul
#print mul_action.to_has_scalar
open tactic
run_cmd do d ← get_decl `algebra.of_module,
  cd ← dag_attr.get_cache,
  e ← get_env,
  trace $ find_gens' d cd e d.type d.value 0 "",
  return ()
run_cmd do e ← get_env,
cd ← class_dag e,
l← e.get `algebra.of_semimodule',
trace $ l.value.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.app_fn.app_fn.app_fn.app_arg.app_arg,
-- aa ← is_instance_chain 2 l.value.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.app_fn.app_fn.app_fn.app_arg.app_arg,
-- trace aa
aa ← get_instance_chains `semimodule 2 l.value.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.binding_body.app_fn.app_fn.app_fn.app_arg.app_arg,
trace aa,
trace $ cd.minimal_vertices aa --.lambda_body.app_fn.app_fn.app_arg.lambda_body.app_fn.app_arg.app_fn.lambda_body--find_gens' cd e l.type l.value 0 ""

  #print finset.prod_sum_elim /- _inst_2: decidable_eq ↝
 -/
  end
end examples
