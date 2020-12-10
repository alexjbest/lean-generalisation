--set_option pp.all true
set_option profiler true
lemma another (g : 1000 = 2*500): 1000 = 2*500 ∧ 1000 = 2*500 :=
begin
  let h :ℕ ,
  exact ⟨rfl, rfl⟩
end
#print another
#lint
lemma foo (p : Prop) : p → p :=
assume hp : p,
have hp2 : p, from hp,
show p, from hp
#print foo

lemma fun_problem (p : Prop) : ¬ (p ↔ ¬ p) :=
assume hpnp,
have hnp : ¬ p, from
  assume hp : p,
  have hnp : ¬ p, from hpnp.mp hp,
  show false, from hnp hp,
have hp : p, from
  have unnecessary : ¬ p, from hnp,
  show p, from hpnp.mpr hnp,
show false, from hnp hp


open tactic declaration expr

meta def expr.has_zero_var (e : expr) : bool :=
e.fold ff $ λ e' d res, res || match e' with | var k := k = d | _ := ff end

meta def find_unused_have_macro : expr → tactic (list name)
| (app a a_1) := (++) <$> find_unused_have_macro a <*> find_unused_have_macro a_1
| (lam var_name bi var_type body) :=  find_unused_have_macro body
| (pi var_name bi var_type body) := find_unused_have_macro body
| (elet var_name type assignment body) := find_unused_have_macro body
| (macro md [lam ppnm _ _ bd]) := do
       (++) (if bd.has_zero_var then [] else [ppnm]) <$>
        find_unused_have_macro bd
| (macro md l) := do ls ← l.mmap find_unused_have_macro, return ls.join
| _ := return []

meta def find_unused_let_macro : expr → tactic (list name)
| (app a a_1) := (++) <$> find_unused_let_macro a <*> find_unused_let_macro a_1
| (lam var_name bi var_type body) :=  find_unused_let_macro body
| (pi var_name bi var_type body) := find_unused_let_macro body
| (elet var_name type assignment body) := do
  --trace body,
       (++) (if body.has_zero_var then [] else [var_name]) <$>
        find_unused_let_macro body

| (macro md [lam ppnm _ _ bd]) :=find_unused_let_macro bd
| (macro md l) := do ls ← l.mmap find_unused_let_macro, return ls.join
| _ := return []

meta def unused_of_decl : declaration → tactic (list name)
| (defn a a_1 a_2 bd a_4 a_5) := find_unused_let_macro bd
| (thm a a_1 a_2 bd) := find_unused_let_macro bd.get
| _ := return []
run_cmd unused_of_decl int_fract_pair.le_of_succ_succ_nth_continuants_aux_b

@[linter] meta def linter.unused_lets : linter :=
{ test := λ d,
  (do
  --trace d.to_name,
  ns ← unused_of_decl d,
   if ns.length = 0 then return none else return (", ".intercalate (ns.map to_string))),
  no_errors_found := "all good",
  errors_found := "DECLS HAVE UNNEEDED LETS",
  is_fast := tt,
  auto_decls := ff }
lemma tmp : ∃ n, n = 1 :=
let a := 1, b:=1 in
begin
  set t := 2,
  use a,
end
#print tmp
#lint only unused_lets
