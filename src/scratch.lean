import tactic
import dag
import algebra.order.ring
import ring_theory.int.basic
import tactic.slim_check

variables (G : Type) [h : group G]
#check  h.9
meta def tt : tactic unit := tactic.reflexivity
structure t := (n : ℕ) (h : n = n . try_refl_tac)
#print canonically_ordered_comm_semiring
#eval list.qsort (λ a b, a < b) ["a", "b", "ba"]
#check name

#check string.has_lt
lemma {!!} : 1 = 1 :=
begin
end
class has_pow' (α β : Type) := (f : α → β → α)

instance {α : Type} [monoid α] : has_pow' α ℕ := sorry
#check (by apply_instance: has_pow' ℕ ℕ )
def t := ℕ

#check (by apply_instance: has_pow' ℕ nat )

open tactic
-- set_option pp.all true

@[derive decidable_eq]
meta structure bound_instance :=
(name : name)
(bindings : list (option expr))
meta instance : has_to_format bound_instance := ⟨λ bi, bi.name.to_string ++ " "
  ++ bi.bindings.to_format ⟩
meta example : bound_instance := { name := `nat.has_pow,
  bindings := [none, `(nat)] }
#eval to_bool $ @expr.const tt `nat [] = @expr.const tt `nat []
#eval to_bool $ ({ name := `nat.has_pow,
  bindings := [none, `(1 + %%(expr.var 1))] } : bound_instance) =
({ name := `nat.has_pow,
  bindings := [none, `(1 + %%(expr.var 1))] } : bound_instance)
lemma a : ({ name := `nat.has_pow,
  bindings := [none, `(nat)] } : bound_instance) = ({ name := `nat.has_pow,
  bindings := [none, `(nat)] } : bound_instance) :=
  begin
    simp,
    congr,
    refl,
  end
meta def declaration.to_bound_instance (d : declaration) : bound_instance :=
  let l := d.type.pi_binders.snd in
⟨l.get_app_fn.const_name, l.get_app_args.map (λ e, if e.is_var then none else some e)⟩
run_cmd (do d ← tactic.get_decl `nat.has_pow',
  trace d.to_bound_instance,
  return ())

@[derive decidable_eq]
inductive aa
| a
| b

open aa

meta def ap : aa → format
| a := "a"
| b := "b"
meta instance : has_to_format aa := ⟨λ t, ap t⟩
meta instance : has_to_tactic_format aa := ⟨λ t, return $ ap t⟩
instance : has_lt aa := ⟨λ a b, true⟩
instance : decidable_rel (has_lt.lt : aa → aa → Prop) := by apply_instance

open tactic
run_cmd (do trace $ (dag.mk aa).insert_edge a b , return ())

universe u

theorem ex_1_3_1_f' (α: Type u) [linear_ordered_comm_ring α]
   (a b : α) (h: a < b) (ha : 0 < a) : a^3 < b^3 :=
  begin
    simp only [(assume t, by ring : ∀ t : α, t^3 = t * t * t)],
    exact mul_lt_mul (mul_lt_mul h h.le ha (ha.le.trans h.le)) h.le ha (mul_self_nonneg b)
  end
theorem ex_1_3_1_f (α: Type u) [linear_ordered_comm_ring α]
   (a b : α) (h: a < b): a^3 < b^3 :=
begin
  by_cases ha : 0 < a,
  { exact ex_1_3_1_f' α a b h ha, },
  rw ← neg_lt_neg_iff at *,
  simp only [(assume t, by ring : ∀ t : α, -t^3 = (-t)^3)],
  rcases lt_trichotomy 0 (-b) with hb | hb | hb,
  { exact ex_1_3_1_f' α (-b) (-a) h hb, },
  { rw ← hb at *,
    rw zero_pow (by norm_num : 0 < 3),
    exact pow_pos h 3, },
  { simp only [neg_neg_iff_pos, not_lt, neg_pow_bit1, neg_zero] at *,
  calc _ < (0 : α) : sorry
  ... ≤ _ : by library_search,
     }
end
#check list.lex
#check expr.has_lt
#check option.has_lt
open expr
#eval (var 0).hash
#eval (var 1).hash
#eval `(nat).hash
#eval `(nat).hash
